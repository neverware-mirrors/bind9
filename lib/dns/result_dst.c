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

#include <isc/result.h>

static const char *dst_result_descriptions[DST_R_NRESULTS] = {
	"algorithm is unsupported",		 /*%< 0 */
	"crypto failure",			 /*%< 1 */
	"built with no crypto support",		 /*%< 2 */
	"illegal operation for a null key",	 /*%< 3 */
	"public key is invalid",		 /*%< 4 */
	"private key is invalid",		 /*%< 5 */
	"external key",				 /*%< 6 */
	"error occurred writing key to disk",	 /*%< 7 */
	"invalid algorithm specific parameter",	 /*%< 8 */
	"UNUSED9",				 /*%< 9 */
	"UNUSED10",				 /*%< 10 */
	"sign failure",				 /*%< 11 */
	"UNUSED12",				 /*%< 12 */
	"UNUSED13",				 /*%< 13 */
	"verify failure",			 /*%< 14 */
	"not a public key",			 /*%< 15 */
	"not a private key",			 /*%< 16 */
	"not a key that can compute a secret",	 /*%< 17 */
	"failure computing a shared secret",	 /*%< 18 */
	"no randomness available",		 /*%< 19 */
	"bad key type",				 /*%< 20 */
	"no engine",				 /*%< 21 */
	"illegal operation for an external key", /*%< 22 */
};

static const char *dst_result_ids[DST_R_NRESULTS] = {
	"DST_R_UNSUPPORTEDALG",
	"DST_R_CRYPTOFAILURE",
	"DST_R_NOCRYPTO",
	"DST_R_NULLKEY",
	"DST_R_INVALIDPUBLICKEY",
	"DST_R_INVALIDPRIVATEKEY",
	"UNUSED",
	"DST_R_WRITEERROR",
	"DST_R_INVALIDPARAM",
	"UNUSED",
	"UNUSED",
	"DST_R_SIGNFAILURE",
	"UNUSED",
	"UNUSED",
	"DST_R_VERIFYFAILURE",
	"DST_R_NOTPUBLICKEY",
	"DST_R_NOTPRIVATEKEY",
	"DST_R_KEYCANNOTCOMPUTESECRET",
	"DST_R_COMPUTESECRETFAILURE",
	"DST_R_NORANDOMNESS",
	"DST_R_BADKEYTYPE",
	"DST_R_NOENGINE",
	"DST_R_EXTERNALKEY",
};

/*! \file */
