/*
 * Copyright (C) Internet Systems Consortium, Inc. ("ISC")
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 *
 * See the COPYRIGHT file distributed with this work for additional
 * information regarding copyright ownership.
 */

/*! \file */

#include <isc/result_isccc.h>

static const char *isccc_result_descriptions[ISCCC_R_NRESULTS] = {
	"unknown version", /* 1 */
	"syntax error",	   /* 2 */
	"bad auth",	   /* 3 */
	"expired",	   /* 4 */
	"clock skew",	   /* 5 */
	"duplicate"	   /* 6 */
};

static const char *isccc_result_ids[ISCCC_R_NRESULTS] = {
	"ISCCC_R_UNKNOWNVERSION", "ISCCC_R_SYNTAX",    "ISCCC_R_BADAUTH",
	"ISCCC_R_EXPIRED",	  "ISCCC_R_CLOCKSKEW", "ISCCC_R_DUPLICATE",
};
