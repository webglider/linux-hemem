/* SPDX-License-Identifier: GPL-2.0 */

/*
 * Linux Security Module Hook declarations.
 *
 * Copyright (C) 2001 WireX Communications, Inc <chris@wirex.com>
 * Copyright (C) 2001 Greg Kroah-Hartman <greg@kroah.com>
 * Copyright (C) 2001 Networks Associates Technology, Inc <ssmalley@nai.com>
 * Copyright (C) 2001 James Morris <jmorris@intercode.com.au>
 * Copyright (C) 2001 Silicon Graphics, Inc. (Trust Technology Group)
 * Copyright (C) 2015 Intel Corporation.
 * Copyright (C) 2015 Casey Schaufler <casey@schaufler-ca.com>
 * Copyright (C) 2016 Mellanox Techonologies
 * Copyright (C) 2020 Google LLC.
 */

/*
 * The macro LSM_HOOK is used to define the data structures required by
 * the LSM framework using the pattern:
 *
 *	LSM_HOOK(<return_type>, <default_value>, <hook_name>, args...)
 *
 * struct security_hook_heads {
 *   #define LSM_HOOK(RET, DEFAULT, NAME, ...) struct hlist_head NAME;
 *   #include <linux/lsm_hook_defs.h>
 *   #undef LSM_HOOK
 * };
 */
LSM_HOOK(int, 0, locked_down, enum lockdown_reason what)

