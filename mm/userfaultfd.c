// SPDX-License-Identifier: GPL-2.0-only
/*
 *  mm/userfaultfd.c
 *
 *  Copyright (C) 2015  Red Hat, Inc.
 */

#include <linux/mm.h>
#include <linux/sched/signal.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include <linux/swap.h>
#include <linux/swapops.h>
#include <linux/userfaultfd_k.h>
#include <linux/mmu_notifier.h>
#include <linux/hugetlb.h>
#include <linux/shmem_fs.h>
#include <asm/tlbflush.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <linux/device.h>
#include <linux/cdev.h>
#include <linux/wait.h>
#include <linux/string.h>
#include <linux/dma-mapping.h>
#include <linux/slab.h>
#include <linux/dmaengine.h>
#include "internal.h"
#include <linux/delay.h>
#include <linux/pci.h>
#include <asm/pgtable.h>
#include <linux/mutex.h>

static DECLARE_WAIT_QUEUE_HEAD(wq);
//For simplicity, request/release a fixed number of channs
struct dma_chan *chans[MAX_DMA_CHANS] = {NULL};
#define MAX_SIZE_PER_DMA_REQUEST (2*1024*1024)
u32 size_per_dma_request =  MAX_SIZE_PER_DMA_REQUEST;
u32 dma_channs = 0;

struct tx_dma_param {
    struct mutex tx_dma_mutex;
	u64 expect_count;
	volatile u64 wakeup_count;
};

/*
 * Find a valid userfault enabled VMA region that covers the whole
 * address range, or NULL on failure.  Must be called with mmap_sem
 * held.
 */
static struct vm_area_struct *vma_find_uffd(struct mm_struct *mm,
					    unsigned long start,
					    unsigned long len)
{
	struct vm_area_struct *vma = find_vma(mm, start);

	if (!vma) {
		printk("mm/userfaultfd.c: vma_find_uffd: !vma\n");
		return NULL;
	}

//	printk("mm/userfaultfd.c: vma_find_uffd: start: 0x%lx\tlen: %ld\n", start, len);
//  printk("mm/userfaultfd.c: vma_find_uffd: found vma 0x%p: 0x%lx - 0x%lx\tlen: %ld\n", vma, vma->vm_start, vma->vm_end, (vma->vm_end - vma->vm_start));
  /*
	 * Check the vma is registered in uffd, this is required to
	 * enforce the VM_MAYWRITE check done at uffd registration
	 * time.
	 */
	if (!vma->vm_userfaultfd_ctx.ctx) {
		printk("mm/userfaultfd.c: vma_find_uffd: !vma->vm_userfaultfd_ctx.ctx\n");
		return NULL;
	}

	if (start < vma->vm_start || start + len > vma->vm_end) {
		printk("mm/userfaultfd.c: vma_find_uffd: region out of vma range\n");
	  printk("mm/userfaultfd.c: vma_find_uffd: start: 0x%lx\tlen: %ld\n", start, len);
    printk("mm/userfaultfd.c: vma_find_uffd: found vma 0x%p: 0x%lx - 0x%lx\tlen: %ld\n", vma, vma->vm_start, vma->vm_end, (vma->vm_end - vma->vm_start));
		return NULL;
	}

	return vma;
}

static __always_inline
struct vm_area_struct *find_dst_vma(struct mm_struct *dst_mm,
				    unsigned long dst_start,
				    unsigned long len)
{
	/*
	 * Make sure that the dst range is both valid and fully within a
	 * single existing vma.
	 */
	struct vm_area_struct *dst_vma;

	dst_vma = find_vma(dst_mm, dst_start);
	if (!dst_vma)
		return NULL;

	if (dst_start < dst_vma->vm_start ||
	    dst_start + len > dst_vma->vm_end)
		return NULL;

	/*
	 * Check the vma is registered in uffd, this is required to
	 * enforce the VM_MAYWRITE check done at uffd registration
	 * time.
	 */
	if (!dst_vma->vm_userfaultfd_ctx.ctx)
		return NULL;

	return dst_vma;
}

/*
 * Install PTEs, to map dst_addr (within dst_vma) to page.
 *
 * This function handles both MCOPY_ATOMIC_NORMAL and _CONTINUE for both shmem
 * and anon, and for both shared and private VMAs.
 */
int mfill_atomic_install_pte(struct mm_struct *dst_mm, pmd_t *dst_pmd,
			     struct vm_area_struct *dst_vma,
			     unsigned long dst_addr, struct page *page,
			     bool newly_allocated, bool wp_copy)
{
	int ret;
	pte_t _dst_pte, *dst_pte;
	bool writable = dst_vma->vm_flags & VM_WRITE;
	bool vm_shared = dst_vma->vm_flags & VM_SHARED;
	bool page_in_cache = page->mapping;
	spinlock_t *ptl;
	struct inode *inode;
	pgoff_t offset, max_off;

	_dst_pte = mk_pte(page, dst_vma->vm_page_prot);
	if (page_in_cache && !vm_shared)
		writable = false;
	if (writable || !page_in_cache)
		_dst_pte = pte_mkdirty(_dst_pte);
	if (writable) {
		if (wp_copy)
			_dst_pte = pte_mkuffd_wp(_dst_pte);
		else
			_dst_pte = pte_mkwrite(_dst_pte);
	}

	dst_pte = pte_offset_map_lock(dst_mm, dst_pmd, dst_addr, &ptl);

	if (vma_is_shmem(dst_vma)) {
		/* serialize against truncate with the page table lock */
		inode = dst_vma->vm_file->f_inode;
		offset = linear_page_index(dst_vma, dst_addr);
		max_off = DIV_ROUND_UP(i_size_read(inode), PAGE_SIZE);
		ret = -EFAULT;
		if (unlikely(offset >= max_off))
			goto out_unlock;
	}

	ret = -EEXIST;
	if (!pte_none(*dst_pte))
		goto out_unlock;

	if (page_in_cache)
		page_add_file_rmap(page, false);
	else
		page_add_new_anon_rmap(page, dst_vma, dst_addr, false);

	/*
	 * Must happen after rmap, as mm_counter() checks mapping (via
	 * PageAnon()), which is set by __page_set_anon_rmap().
	 */
	inc_mm_counter(dst_mm, mm_counter(page));

	if (newly_allocated)
		lru_cache_add_inactive_or_unevictable(page, dst_vma);

	set_pte_at(dst_mm, dst_addr, dst_pte, _dst_pte);

	/* No need to invalidate - it was non-present before */
	update_mmu_cache(dst_vma, dst_addr, dst_pte);
	ret = 0;
out_unlock:
	pte_unmap_unlock(dst_pte, ptl);
	return ret;
}

static int mcopy_atomic_pte(struct mm_struct *dst_mm,
			    pmd_t *dst_pmd,
			    struct vm_area_struct *dst_vma,
			    unsigned long dst_addr,
			    unsigned long src_addr,
			    struct page **pagep,
			    bool wp_copy)
{
	void *page_kaddr;
	int ret;
	struct page *page;

	if (!*pagep) {
		ret = -ENOMEM;
		page = alloc_page_vma(GFP_HIGHUSER_MOVABLE, dst_vma, dst_addr);
		if (!page)
			goto out;

		page_kaddr = kmap_atomic(page);
		ret = copy_from_user(page_kaddr,
				     (const void __user *) src_addr,
				     PAGE_SIZE);
		kunmap_atomic(page_kaddr);

		/* fallback to copy_from_user outside mmap_lock */
		if (unlikely(ret)) {
			ret = -ENOENT;
			*pagep = page;
			/* don't free the page */
			goto out;
		}
	} else {
		page = *pagep;
		*pagep = NULL;
	}

	/*
	 * The memory barrier inside __SetPageUptodate makes sure that
	 * preceding stores to the page contents become visible before
	 * the set_pte_at() write.
	 */
	__SetPageUptodate(page);

	ret = -ENOMEM;
	if (mem_cgroup_charge(page, dst_mm, GFP_KERNEL))
		goto out_release;

	ret = mfill_atomic_install_pte(dst_mm, dst_pmd, dst_vma, dst_addr,
				       page, true, wp_copy);
	if (ret)
		goto out_release;
out:
	return ret;
out_release:
	put_page(page);
	goto out;
}

static int mfill_zeropage_pte(struct mm_struct *dst_mm,
			      pmd_t *dst_pmd,
			      struct vm_area_struct *dst_vma,
			      unsigned long dst_addr)
{
	pte_t _dst_pte, *dst_pte;
	spinlock_t *ptl;
	int ret;
	pgoff_t offset, max_off;
	struct inode *inode;

	_dst_pte = pte_mkspecial(pfn_pte(my_zero_pfn(dst_addr),
					 dst_vma->vm_page_prot));
	dst_pte = pte_offset_map_lock(dst_mm, dst_pmd, dst_addr, &ptl);
	if (dst_vma->vm_file) {
		/* the shmem MAP_PRIVATE case requires checking the i_size */
		inode = dst_vma->vm_file->f_inode;
		offset = linear_page_index(dst_vma, dst_addr);
		max_off = DIV_ROUND_UP(i_size_read(inode), PAGE_SIZE);
		ret = -EFAULT;
		if (unlikely(offset >= max_off))
			goto out_unlock;
	}
	ret = -EEXIST;
	if (!pte_none(*dst_pte))
		goto out_unlock;
	set_pte_at(dst_mm, dst_addr, dst_pte, _dst_pte);
	/* No need to invalidate - it was non-present before */
	update_mmu_cache(dst_vma, dst_addr, dst_pte);
	ret = 0;
out_unlock:
	pte_unmap_unlock(dst_pte, ptl);
	return ret;
}

/* Handles UFFDIO_CONTINUE for all shmem VMAs (shared or private). */
static int mcontinue_atomic_pte(struct mm_struct *dst_mm,
				pmd_t *dst_pmd,
				struct vm_area_struct *dst_vma,
				unsigned long dst_addr,
				bool wp_copy)
{
	struct inode *inode = file_inode(dst_vma->vm_file);
	pgoff_t pgoff = linear_page_index(dst_vma, dst_addr);
	struct page *page;
	int ret;

	ret = shmem_getpage(inode, pgoff, &page, SGP_READ);
	if (ret)
		goto out;
	if (!page) {
		ret = -EFAULT;
		goto out;
	}

	ret = mfill_atomic_install_pte(dst_mm, dst_pmd, dst_vma, dst_addr,
				       page, false, wp_copy);
	if (ret)
		goto out_release;

	unlock_page(page);
	ret = 0;
out:
	return ret;
out_release:
	unlock_page(page);
	put_page(page);
	goto out;
}

static pmd_t *mm_alloc_pmd(struct mm_struct *mm, unsigned long address)
{
	pgd_t *pgd;
	p4d_t *p4d;
	pud_t *pud;

	pgd = pgd_offset(mm, address);
	p4d = p4d_alloc(mm, pgd, address);
	if (!p4d)
		return NULL;
	pud = pud_alloc(mm, p4d, address);
	if (!pud)
		return NULL;
	/*
	 * Note that we didn't run this because the pmd was
	 * missing, the *pmd may be already established and in
	 * turn it may also be a trans_huge_pmd.
	 */
	return pmd_alloc(mm, pud, address);
}

#ifdef CONFIG_HUGETLB_PAGE
/*
 * __mcopy_atomic processing for HUGETLB vmas.  Note that this routine is
 * called with mmap_lock held, it will release mmap_lock before returning.
 */
static __always_inline ssize_t __mcopy_atomic_hugetlb(struct mm_struct *dst_mm,
					      struct vm_area_struct *dst_vma,
					      unsigned long dst_start,
					      unsigned long src_start,
					      unsigned long len,
					      enum mcopy_atomic_mode mode)
{
	int vm_shared = dst_vma->vm_flags & VM_SHARED;
	ssize_t err;
	pte_t *dst_pte;
	unsigned long src_addr, dst_addr;
	long copied;
	struct page *page;
	unsigned long vma_hpagesize;
	pgoff_t idx;
	u32 hash;
	struct address_space *mapping;

	/*
	 * There is no default zero huge page for all huge page sizes as
	 * supported by hugetlb.  A PMD_SIZE huge pages may exist as used
	 * by THP.  Since we can not reliably insert a zero page, this
	 * feature is not supported.
	 */
	if (mode == MCOPY_ATOMIC_ZEROPAGE) {
		mmap_read_unlock(dst_mm);
		return -EINVAL;
	}

	src_addr = src_start;
	dst_addr = dst_start;
	copied = 0;
	page = NULL;
	vma_hpagesize = vma_kernel_pagesize(dst_vma);

	/*
	 * Validate alignment based on huge page size
	 */
	err = -EINVAL;
	if (dst_start & (vma_hpagesize - 1) || len & (vma_hpagesize - 1))
		goto out_unlock;

retry:
	/*
	 * On routine entry dst_vma is set.  If we had to drop mmap_lock and
	 * retry, dst_vma will be set to NULL and we must lookup again.
	 */
	if (!dst_vma) {
		err = -ENOENT;
		dst_vma = find_dst_vma(dst_mm, dst_start, len);
		if (!dst_vma || !is_vm_hugetlb_page(dst_vma))
			goto out_unlock;

		err = -EINVAL;
		if (vma_hpagesize != vma_kernel_pagesize(dst_vma))
			goto out_unlock;

		vm_shared = dst_vma->vm_flags & VM_SHARED;
	}

	/*
	 * If not shared, ensure the dst_vma has a anon_vma.
	 */
	err = -ENOMEM;
	if (!vm_shared) {
		if (unlikely(anon_vma_prepare(dst_vma)))
			goto out_unlock;
	}

	while (src_addr < src_start + len) {
		BUG_ON(dst_addr >= dst_start + len);

		/*
		 * Serialize via i_mmap_rwsem and hugetlb_fault_mutex.
		 * i_mmap_rwsem ensures the dst_pte remains valid even
		 * in the case of shared pmds.  fault mutex prevents
		 * races with other faulting threads.
		 */
		mapping = dst_vma->vm_file->f_mapping;
		i_mmap_lock_read(mapping);
		idx = linear_page_index(dst_vma, dst_addr);
		hash = hugetlb_fault_mutex_hash(mapping, idx);
		mutex_lock(&hugetlb_fault_mutex_table[hash]);

		err = -ENOMEM;
		dst_pte = huge_pte_alloc(dst_mm, dst_vma, dst_addr, vma_hpagesize);
		if (!dst_pte) {
			mutex_unlock(&hugetlb_fault_mutex_table[hash]);
			i_mmap_unlock_read(mapping);
			goto out_unlock;
		}

		if (mode != MCOPY_ATOMIC_CONTINUE &&
		    !huge_pte_none(huge_ptep_get(dst_pte))) {
			err = -EEXIST;
			mutex_unlock(&hugetlb_fault_mutex_table[hash]);
			i_mmap_unlock_read(mapping);
			goto out_unlock;
		}

		err = hugetlb_mcopy_atomic_pte(dst_mm, dst_pte, dst_vma,
					       dst_addr, src_addr, mode, &page);

		mutex_unlock(&hugetlb_fault_mutex_table[hash]);
		i_mmap_unlock_read(mapping);

		cond_resched();

		if (unlikely(err == -ENOENT)) {
			mmap_read_unlock(dst_mm);
			BUG_ON(!page);

			err = copy_huge_page_from_user(page,
						(const void __user *)src_addr,
						vma_hpagesize / PAGE_SIZE,
						true);
			if (unlikely(err)) {
				err = -EFAULT;
				goto out;
			}
			mmap_read_lock(dst_mm);

			dst_vma = NULL;
			goto retry;
		} else
			BUG_ON(page);

		if (!err) {
			dst_addr += vma_hpagesize;
			src_addr += vma_hpagesize;
			copied += vma_hpagesize;

			if (fatal_signal_pending(current))
				err = -EINTR;
		}
		if (err)
			break;
	}

out_unlock:
	mmap_read_unlock(dst_mm);
out:
	if (page)
		put_page(page);
	BUG_ON(copied < 0);
	BUG_ON(err > 0);
	BUG_ON(!copied && !err);
	return copied ? copied : err;
}
#else /* !CONFIG_HUGETLB_PAGE */
/* fail at build time if gcc attempts to use this */
extern ssize_t __mcopy_atomic_hugetlb(struct mm_struct *dst_mm,
				      struct vm_area_struct *dst_vma,
				      unsigned long dst_start,
				      unsigned long src_start,
				      unsigned long len,
				      enum mcopy_atomic_mode mode);
#endif /* CONFIG_HUGETLB_PAGE */

static __always_inline ssize_t mfill_atomic_pte(struct mm_struct *dst_mm,
						pmd_t *dst_pmd,
						struct vm_area_struct *dst_vma,
						unsigned long dst_addr,
						unsigned long src_addr,
						struct page **page,
						enum mcopy_atomic_mode mode,
						bool wp_copy)
{
	ssize_t err;

	if (mode == MCOPY_ATOMIC_CONTINUE) {
		return mcontinue_atomic_pte(dst_mm, dst_pmd, dst_vma, dst_addr,
					    wp_copy);
	}

	/*
	 * The normal page fault path for a shmem will invoke the
	 * fault, fill the hole in the file and COW it right away. The
	 * result generates plain anonymous memory. So when we are
	 * asked to fill an hole in a MAP_PRIVATE shmem mapping, we'll
	 * generate anonymous memory directly without actually filling
	 * the hole. For the MAP_PRIVATE case the robustness check
	 * only happens in the pagetable (to verify it's still none)
	 * and not in the radix tree.
	 */
	if (!(dst_vma->vm_flags & VM_SHARED)) {
		if (mode == MCOPY_ATOMIC_NORMAL)
			err = mcopy_atomic_pte(dst_mm, dst_pmd, dst_vma,
					       dst_addr, src_addr, page,
					       wp_copy);
		else
			err = mfill_zeropage_pte(dst_mm, dst_pmd,
						 dst_vma, dst_addr);
	} else {
		VM_WARN_ON_ONCE(wp_copy);
		err = shmem_mfill_atomic_pte(dst_mm, dst_pmd, dst_vma,
					     dst_addr, src_addr,
					     mode != MCOPY_ATOMIC_NORMAL,
					     page);
	}

	return err;
}

static __always_inline ssize_t __mcopy_atomic(struct mm_struct *dst_mm,
					      unsigned long dst_start,
					      unsigned long src_start,
					      unsigned long len,
					      enum mcopy_atomic_mode mcopy_mode,
					      atomic_t *mmap_changing,
					      __u64 mode)
{
	struct vm_area_struct *dst_vma;
	ssize_t err;
	pmd_t *dst_pmd;
	unsigned long src_addr, dst_addr;
	long copied;
	struct page *page;
	bool wp_copy;

	/*
	 * Sanitize the command parameters:
	 */
	BUG_ON(dst_start & ~PAGE_MASK);
	BUG_ON(len & ~PAGE_MASK);

	/* Does the address range wrap, or is the span zero-sized? */
	BUG_ON(src_start + len <= src_start);
	BUG_ON(dst_start + len <= dst_start);

	src_addr = src_start;
	dst_addr = dst_start;
	copied = 0;
	page = NULL;
retry:
	mmap_read_lock(dst_mm);

	/*
	 * If memory mappings are changing because of non-cooperative
	 * operation (e.g. mremap) running in parallel, bail out and
	 * request the user to retry later
	 */
	err = -EAGAIN;
	if (mmap_changing && atomic_read(mmap_changing))
		goto out_unlock;

	/*
	 * Make sure the vma is not shared, that the dst range is
	 * both valid and fully within a single existing vma.
	 */
	err = -ENOENT;
	dst_vma = find_dst_vma(dst_mm, dst_start, len);
	if (!dst_vma)
		goto out_unlock;

	err = -EINVAL;
	/*
	 * shmem_zero_setup is invoked in mmap for MAP_ANONYMOUS|MAP_SHARED but
	 * it will overwrite vm_ops, so vma_is_anonymous must return false.
	 */
	if (WARN_ON_ONCE(vma_is_anonymous(dst_vma) &&
	    dst_vma->vm_flags & VM_SHARED))
		goto out_unlock;

	/*
	 * validate 'mode' now that we know the dst_vma: don't allow
	 * a wrprotect copy if the userfaultfd didn't register as WP.
	 */
	wp_copy = mode & UFFDIO_COPY_MODE_WP;
	if (wp_copy && !(dst_vma->vm_flags & VM_UFFD_WP))
		goto out_unlock;

	/*
	 * If this is a HUGETLB vma, pass off to appropriate routine
	 */
	if (is_vm_hugetlb_page(dst_vma))
		return  __mcopy_atomic_hugetlb(dst_mm, dst_vma, dst_start,
						src_start, len, mcopy_mode);

	if (!vma_is_anonymous(dst_vma) && !vma_is_shmem(dst_vma))
		goto out_unlock;
	if (!vma_is_shmem(dst_vma) && mcopy_mode == MCOPY_ATOMIC_CONTINUE)
		goto out_unlock;

	/*
	 * Ensure the dst_vma has a anon_vma or this page
	 * would get a NULL anon_vma when moved in the
	 * dst_vma.
	 */
	err = -ENOMEM;
	if (!(dst_vma->vm_flags & VM_SHARED) &&
	    unlikely(anon_vma_prepare(dst_vma)))
		goto out_unlock;

	while (src_addr < src_start + len) {
		pmd_t dst_pmdval;

		BUG_ON(dst_addr >= dst_start + len);

		dst_pmd = mm_alloc_pmd(dst_mm, dst_addr);
		if (unlikely(!dst_pmd)) {
			err = -ENOMEM;
			break;
		}

		dst_pmdval = pmd_read_atomic(dst_pmd);
		/*
		 * If the dst_pmd is mapped as THP don't
		 * override it and just be strict.
		 */
		if (unlikely(pmd_trans_huge(dst_pmdval))) {
			err = -EEXIST;
			break;
		}
		if (unlikely(pmd_none(dst_pmdval)) &&
		    unlikely(__pte_alloc(dst_mm, dst_pmd))) {
			err = -ENOMEM;
			break;
		}
		/* If an huge pmd materialized from under us fail */
		if (unlikely(pmd_trans_huge(*dst_pmd))) {
			err = -EFAULT;
			break;
		}

		BUG_ON(pmd_none(*dst_pmd));
		BUG_ON(pmd_trans_huge(*dst_pmd));

		err = mfill_atomic_pte(dst_mm, dst_pmd, dst_vma, dst_addr,
				       src_addr, &page, mcopy_mode, wp_copy);
		cond_resched();

		if (unlikely(err == -ENOENT)) {
			void *page_kaddr;

			mmap_read_unlock(dst_mm);
			BUG_ON(!page);

			page_kaddr = kmap(page);
			err = copy_from_user(page_kaddr,
					     (const void __user *) src_addr,
					     PAGE_SIZE);
			kunmap(page);
			if (unlikely(err)) {
				err = -EFAULT;
				goto out;
			}
			goto retry;
		} else
			BUG_ON(page);

		if (!err) {
			dst_addr += PAGE_SIZE;
			src_addr += PAGE_SIZE;
			copied += PAGE_SIZE;

			if (fatal_signal_pending(current))
				err = -EINTR;
		}
		if (err)
			break;
	}

out_unlock:
	mmap_read_unlock(dst_mm);
out:
	if (page)
		put_page(page);
	BUG_ON(copied < 0);
	BUG_ON(err > 0);
	BUG_ON(!copied && !err);
	return copied ? copied : err;
}

static void hemem_dma_tx_callback(void *dma_async_param)
{
	struct tx_dma_param *tx_dma_param = (struct tx_dma_param*)dma_async_param;
    struct mutex *tx_dma_mutex = &(tx_dma_param->tx_dma_mutex);
    mutex_lock(tx_dma_mutex);
	(tx_dma_param->wakeup_count)++;
	if (tx_dma_param->wakeup_count < tx_dma_param->expect_count) {
        mutex_unlock(tx_dma_mutex);
		return;
	}
    mutex_unlock(tx_dma_mutex);
	wake_up_interruptible(&wq);
}

static int bad_address(void *p)
{
	unsigned long dummy;

	return get_kernel_nofault(dummy, (unsigned long *)p);
}

static void  page_walk(u64 address, u64* phy_addr)
{

	pgd_t *base = __va(read_cr3_pa());
	pgd_t *pgd = base + pgd_index(address);
        p4d_t *p4d;
        pud_t *pud;
        pmd_t *pmd;
        pte_t *pte;
	u64 page_addr;
	u64 page_offset;
 	int present = 0;	
	int write = 0;

	if (bad_address(pgd))
		goto out;

	if (!pgd_present(*pgd))
		goto out;

	p4d = p4d_offset(pgd, address);
	if (bad_address(p4d))
		goto out;

	if (!p4d_present(*p4d) || p4d_large(*p4d))
		goto out;

	pud = pud_offset(p4d, address);
	if (bad_address(pud))
		goto out;

	if (!pud_present(*pud) || pud_large(*pud))
		goto out;

	pmd = pmd_offset(pud, address);
	if (bad_address(pmd))
		goto out;

    if (pmd_large(*pmd)) {
	    page_addr = pmd_val(*pmd) & 0x000FFFFFFFE00000;
	    page_offset = address & ~HPAGE_MASK;
    }
    else {
        if (!pmd_present(*pmd))
            goto out;

        pte = pte_offset_kernel(pmd, address);
        if (bad_address(pte))
            goto out;

        present = pte_present(*pte);
        write = pte_write(*pte);
        
        if (present != 1 || write == 0) {
            printk("in page_walk, address=%llu, present=%d, write=%d\n", address, present, write); 
        }

        page_addr = pte_val(*pte) & 0x000FFFFFFFFFF000;
        page_offset = address & ~PAGE_MASK;
    }

	*phy_addr = page_addr | page_offset;
    return;

out:
	pr_info("BAD\n");
}

int dma_request_channs(struct uffdio_dma_channs* uffdio_dma_channs)
{
    struct dma_chan *chan = NULL;
    dma_cap_mask_t mask;
    int index;
    int num_channs;

    if (uffdio_dma_channs == NULL) {
        return -1;
    }

    num_channs = uffdio_dma_channs->num_channs;
    if (num_channs > MAX_DMA_CHANS) {
        num_channs = MAX_DMA_CHANS;
    }

    size_per_dma_request = uffdio_dma_channs->size_per_dma_request;
    if (size_per_dma_request > MAX_SIZE_PER_DMA_REQUEST) {
        size_per_dma_request = MAX_SIZE_PER_DMA_REQUEST;
    }

    dma_cap_zero(mask);
    dma_cap_set(DMA_MEMCPY, mask);
    for (index = 0; index < num_channs; index++) {
        if (chans[index]) {
            continue;
        }

        chan = dma_request_channel(mask, NULL, NULL);
        if (chan == NULL) {
            printk("wei: error when dma_request_channel, index=%d, num_channs=%u\n", index, num_channs);
            goto out;
        }

        chans[index] = chan;
    }

    dma_channs = num_channs;
    return 0;
out:
    while (index >= 0) {
        if (chans[index]) {
            dma_release_channel(chans[index]);
            chans[index] = NULL;
        }
    }

    return -1;
}

int dma_release_channs(void)
{
    int index;

    for (index = 0; index < dma_channs; index++) {
        if (chans[index]) {
            dma_release_channel(chans[index]);
            chans[index] = NULL;
        }
    }

    dma_channs = 0;
    size_per_dma_request = MAX_SIZE_PER_DMA_REQUEST;
    return 0;
}

static __always_inline ssize_t __dma_mcopy_pages(struct mm_struct *dst_mm,
					      struct uffdio_dma_copy *uffdio_dma_copy,
					      atomic_t *mmap_changing)
{
	struct vm_area_struct *dst_vma;
	ssize_t err;
	long copied = 0;
	bool wp_copy;
	u64 src_start;
	u64 dst_start;
  u64 src_cur;
  u64 dst_cur;
	dma_addr_t src_phys;
	dma_addr_t dst_phys;
	u64 len;
  u64 len_cur;
	struct dma_chan *chan = NULL;
	dma_cap_mask_t mask;
	struct dma_async_tx_descriptor *tx = NULL;
	dma_cookie_t dma_cookie;
	struct dma_device *dma;
	struct device *dev;
	struct mm_struct *mm = current->mm;
	int present;
  int index = 0;
	u64 count = 0;
  u64 expect_count = 0;
  static u64 dma_assign_index = 0;
	struct tx_dma_param tx_dma_param;
  u64 dma_len = 0;
  u64 start, end;
  u64 start_walk, end_walk;
  u64 start_copy, end_copy;

#ifdef DEBUG_TM
  start = rdtsc();
#endif
	mmap_read_lock(dst_mm);
    /*
	 * If memory mappings are changing because of non-cooperative
	 * operation (e.g. mremap) running in parallel, bail out and
	 * request the user to retry later
	 */
	err = -EAGAIN;
	if (mmap_changing && atomic_read(mmap_changing))
		goto out_unlock;

	BUG_ON(uffdio_dma_copy == NULL);
	count = uffdio_dma_copy->count;
    for (index = 0; index < count; index++) {
        if (uffdio_dma_copy->len[index] % size_per_dma_request == 0) {
            expect_count += uffdio_dma_copy->len[index] / size_per_dma_request;
        }
        else {
            expect_count += uffdio_dma_copy->len[index] / size_per_dma_request + 1;
        }
    }

	tx_dma_param.wakeup_count = 0;
	tx_dma_param.expect_count = expect_count;
  mutex_init(&(tx_dma_param.tx_dma_mutex));
        
  for (index  = 0; index < count; index++) {
		dst_start = uffdio_dma_copy->dst[index];
		src_start = uffdio_dma_copy->src[index];
		len = uffdio_dma_copy->len[index];

		/*
		 * Sanitize the command parameters:
		 */
		BUG_ON(dst_start & ~PAGE_MASK);
		BUG_ON(len & ~PAGE_MASK);

		/* Does the address range wrap, or is the span zero-sized? */
		BUG_ON(src_start + len <= src_start);
		BUG_ON(dst_start + len <= dst_start);

#ifdef DEBUG_TM
    start_walk = rdtsc();
#endif
    page_walk(src_start, &src_phys);
    page_walk(dst_start, &dst_phys);
#ifdef DEBUG_TM
    end_walk = rdtsc();
    start_copy = rdtsc();
#endif
    for (src_cur = src_start, dst_cur = dst_start, len_cur = 0; len_cur < len;) {
      err = 0;
		  chan = chans[dma_assign_index++ % dma_channs];
      if (len_cur + size_per_dma_request > len) {
        dma_len = len - len_cur; 
       }
       else {
         dma_len = size_per_dma_request;
        }

       tx = dmaengine_prep_dma_memcpy(chan, dst_phys, src_phys, dma_len, DMA_PREP_INTERRUPT | DMA_CTRL_ACK);
       if (tx == NULL) {
         printk("wei: error when dmaengine_prep_dma_memcpy, dma_chans=%d\n", dma_channs);
         goto out_unlock;
       }

       tx->callback = hemem_dma_tx_callback;
       tx->callback_param = &tx_dma_param;
       tx->cookie = chan->cookie;
       dma_cookie = dmaengine_submit(tx);
       if (dma_submit_error(dma_cookie)) {
         printk("wei: Failed to do DMA tx_submit\n");
         goto out_unlock;
       }

       dma_async_issue_pending(chan);
       len_cur += dma_len;
       src_cur += dma_len;
       dst_cur += dma_len;
       src_phys += dma_len;
       dst_phys += dma_len;
    }
	}

	wait_event_interruptible(wq, tx_dma_param.wakeup_count >= tx_dma_param.expect_count);
#ifdef DEBUG_TM
  end_copy = rdtsc();
#endif
	for (index = 0; index < count; index++) {
		copied += uffdio_dma_copy->len[index];
	}

out_unlock:
	mmap_read_unlock(dst_mm);
out:
  BUG_ON(copied < 0);
	BUG_ON(err > 0);
	BUG_ON(!copied && !err);
#ifdef DEBUG_TM
    end = rdtsc();
    printk("dma_memcpy_fun: %llu, page_walk: %llu, only_dma_op:%llu\n", end - start, end_copy - start_copy, end_walk - start_walk);
#endif
	return copied ? copied : err;
}

ssize_t mcopy_atomic(struct mm_struct *dst_mm, unsigned long dst_start,
		     unsigned long src_start, unsigned long len,
		     atomic_t *mmap_changing, __u64 mode)
{
	return __mcopy_atomic(dst_mm, dst_start, src_start, len,
			      MCOPY_ATOMIC_NORMAL, mmap_changing, mode);
}

ssize_t dma_mcopy_pages(struct mm_struct *dst_mm,
		     struct uffdio_dma_copy *uffdio_dma_copy,
		     atomic_t *mmap_changing)
{
	return __dma_mcopy_pages(dst_mm, 
			      uffdio_dma_copy,
			      mmap_changing);
}

ssize_t mfill_zeropage(struct mm_struct *dst_mm, unsigned long start,
		       unsigned long len, atomic_t *mmap_changing)
{
	return __mcopy_atomic(dst_mm, start, 0, len, MCOPY_ATOMIC_ZEROPAGE,
			      mmap_changing, 0);
}

ssize_t mcopy_continue(struct mm_struct *dst_mm, unsigned long start,
		       unsigned long len, atomic_t *mmap_changing)
{
	return __mcopy_atomic(dst_mm, start, 0, len, MCOPY_ATOMIC_CONTINUE,
			      mmap_changing, 0);
}

int mwriteprotect_range(struct mm_struct *dst_mm, unsigned long start,
			unsigned long len, bool enable_wp,
			atomic_t *mmap_changing)
{
	struct vm_area_struct *dst_vma;
	pgprot_t newprot;
	int err;

	/*
	 * Sanitize the command parameters:
	 */
	BUG_ON(start & ~PAGE_MASK);
	BUG_ON(len & ~PAGE_MASK);

	/* Does the address range wrap, or is the span zero-sized? */
	BUG_ON(start + len <= start);

	mmap_read_lock(dst_mm);

	/*
	 * If memory mappings are changing because of non-cooperative
	 * operation (e.g. mremap) running in parallel, bail out and
	 * request the user to retry later
	 */
	err = -EAGAIN;
	if (mmap_changing && atomic_read(mmap_changing))
		goto out_unlock;

	err = -ENOENT;
	dst_vma = find_dst_vma(dst_mm, start, len);
	/*
	 * Make sure the vma is not shared, that the dst range is
	 * both valid and fully within a single existing vma.
	 */
	if (!dst_vma || ((dst_vma->vm_flags & VM_SHARED) && !vma_is_dax(dst_vma))) {
		printk("mm/userfaultfd.c: mwriteprotect_range: dst_vma is null\n");
		goto out_unlock;
	}
	if (!userfaultfd_wp(dst_vma)) {
		printk("mm/userfaultfd.c: mwriteprotect_range: dst_vma is not userfaultfd_wp\n");
		goto out_unlock;
	}
	if (!(vma_is_anonymous(dst_vma) || vma_is_dax(dst_vma))) {
		printk("mm/userfaultfd.c: mwriteprotect_range: dst_vma is not anonymous or dax\n");
		goto out_unlock;
	}

	if (enable_wp)
		newprot = vm_get_page_prot(dst_vma->vm_flags & ~(VM_WRITE));
	else
		newprot = vm_get_page_prot(dst_vma->vm_flags);

	change_protection(dst_vma, start, start + len, newprot,
			  enable_wp ? MM_CP_UFFD_WP : MM_CP_UFFD_WP_RESOLVE);

	err = 0;
out_unlock:
	mmap_read_unlock(dst_mm);
	return err;
}
