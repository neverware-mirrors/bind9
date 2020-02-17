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

#ifndef ISCCC_RESULT_H
#define ISCCC_RESULT_H 1

/*! \file isccc/result.h */

#include <isc/resultclass.h>

/*% Unknown Version */
#define ISCCC_R_UNKNOWNVERSION ISC_RESULTCODE_ISCCC(0)
/*% Syntax Error */
#define ISCCC_R_SYNTAX ISC_RESULTCODE_ISCCC(1)
/*% Bad Authorization */
#define ISCCC_R_BADAUTH ISC_RESULTCODE_ISCCC(2)
/*% Expired */
#define ISCCC_R_EXPIRED ISC_RESULTCODE_ISCCC(3)
/*% Clock Skew */
#define ISCCC_R_CLOCKSKEW ISC_RESULTCODE_ISCCC(4)
/*% Duplicate */
#define ISCCC_R_DUPLICATE ISC_RESULTCODE_ISCCC(5)

#define ISCCC_R_NRESULTS 6 /*%< Number of results */

#endif /* ISCCC_RESULT_H */
