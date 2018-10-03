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

/* RFC1183 */

#ifndef RDATA_GENERIC_RT_21_C
#define RDATA_GENERIC_RT_21_C

#define RRTYPE_RT_ATTRIBUTES (0)

static inline isc_result_t
fromtext_rt(ARGS_FROMTEXT) {
	isc_token_t token;
	dns_name_t name;
	isc_buffer_t buffer;
	bool ok;

	REQUIRE(type == dns_rdatatype_rt);

	UNUSED(type);
	UNUSED(rdclass);
	UNUSED(callbacks);

	RETERR(isc_lex_getmastertoken(lexer, &token, isc_tokentype_number,
				      false));
	if (token.value.as_ulong > 0xffffU)
		RETTOK(ISC_R_RANGE);
	RETERR(uint16_tobuffer(token.value.as_ulong, target));

	RETERR(isc_lex_getmastertoken(lexer, &token, isc_tokentype_string,
				      false));

	dns_name_init(&name, NULL);
	buffer_fromregion(&buffer, &token.value.as_region);
	if (origin == NULL)
		origin = dns_rootname;
	RETTOK(dns_name_fromtext(&name, &buffer, origin, options, target));
	ok = true;
	if ((options & DNS_RDATA_CHECKNAMES) != 0)
		ok = dns_name_ishostname(&name, false);
	if (!ok && (options & DNS_RDATA_CHECKNAMESFAIL) != 0)
		RETTOK(DNS_R_BADNAME);
	if (!ok && callbacks != NULL)
		warn_badname(&name, lexer, callbacks);
	return (ISC_R_SUCCESS);
}

static inline isc_result_t
totext_rt(ARGS_TOTEXT) {
	isc_region_t region;
	dns_name_t name;
	dns_name_t prefix;
	bool sub;
	char buf[sizeof("64000")];
	unsigned short num;

	REQUIRE(rdata->type == dns_rdatatype_rt);
	REQUIRE(rdata->length != 0);

	dns_name_init(&name, NULL);
	dns_name_init(&prefix, NULL);

	dns_rdata_toregion(rdata, &region);
	num = uint16_fromregion(&region);
	isc_region_consume(&region, 2);
	snprintf(buf, sizeof(buf), "%u", num);
	RETERR(str_totext(buf, target));
	RETERR(str_totext(" ", target));
	dns_name_fromregion(&name, &region);
	sub = name_prefix(&name, tctx->origin, &prefix);
	return (dns_name_totext(&prefix, sub, target));
}

static inline isc_result_t
fromwire_rt(ARGS_FROMWIRE) {
	dns_name_t name;
	isc_region_t sregion;
	isc_region_t tregion;

	REQUIRE(type == dns_rdatatype_rt);

	UNUSED(type);
	UNUSED(rdclass);

	dns_decompress_setmethods(dctx, DNS_COMPRESS_NONE);

	dns_name_init(&name, NULL);

	isc_buffer_activeregion(source, &sregion);
	isc_buffer_availableregion(target, &tregion);
	if (tregion.length < 2)
		return (ISC_R_NOSPACE);
	if (sregion.length < 2)
		return (ISC_R_UNEXPECTEDEND);
	memmove(tregion.base, sregion.base, 2);
	isc_buffer_forward(source, 2);
	isc_buffer_add(target, 2);
	return (dns_name_fromwire(&name, source, dctx, options, target));
}

static inline isc_result_t
towire_rt(ARGS_TOWIRE) {
	dns_name_t name;
	dns_offsets_t offsets;
	isc_region_t region;
	isc_region_t tr;

	REQUIRE(rdata->type == dns_rdatatype_rt);
	REQUIRE(rdata->length != 0);

	dns_compress_setmethods(cctx, DNS_COMPRESS_NONE);
	isc_buffer_availableregion(target, &tr);
	dns_rdata_toregion(rdata, &region);
	if (tr.length < 2)
		return (ISC_R_NOSPACE);
	memmove(tr.base, region.base, 2);
	isc_region_consume(&region, 2);
	isc_buffer_add(target, 2);

	dns_name_init(&name, offsets);
	dns_name_fromregion(&name, &region);

	return (dns_name_towire(&name, cctx, target));
}

static inline int
compare_rt(ARGS_COMPARE) {
	dns_name_t name1;
	dns_name_t name2;
	isc_region_t region1;
	isc_region_t region2;
	int order;

	REQUIRE(rdata1->type == rdata2->type);
	REQUIRE(rdata1->rdclass == rdata2->rdclass);
	REQUIRE(rdata1->type == dns_rdatatype_rt);
	REQUIRE(rdata1->length != 0);
	REQUIRE(rdata2->length != 0);

	order = memcmp(rdata1->data, rdata2->data, 2);
	if (order != 0)
		return (order < 0 ? -1 : 1);

	dns_name_init(&name1, NULL);
	dns_name_init(&name2, NULL);

	dns_rdata_toregion(rdata1, &region1);
	dns_rdata_toregion(rdata2, &region2);

	isc_region_consume(&region1, 2);
	isc_region_consume(&region2, 2);

	dns_name_fromregion(&name1, &region1);
	dns_name_fromregion(&name2, &region2);

	return (dns_name_rdatacompare(&name1, &name2));
}

static inline isc_result_t
fromstruct_rt(ARGS_FROMSTRUCT) {
	dns_rdata_rt_t *rt = source;
	isc_region_t region;

	REQUIRE(type == dns_rdatatype_rt);
	REQUIRE(source != NULL);
	REQUIRE(rt->common.rdtype == type);
	REQUIRE(rt->common.rdclass == rdclass);

	UNUSED(type);
	UNUSED(rdclass);

	RETERR(uint16_tobuffer(rt->preference, target));
	dns_name_toregion(&rt->host, &region);
	return (isc_buffer_copyregion(target, &region));
}

static inline isc_result_t
tostruct_rt(ARGS_TOSTRUCT) {
	isc_region_t region;
	dns_rdata_rt_t *rt = target;
	dns_name_t name;

	REQUIRE(rdata->type == dns_rdatatype_rt);
	REQUIRE(target != NULL);
	REQUIRE(rdata->length != 0);

	rt->common.rdclass = rdata->rdclass;
	rt->common.rdtype = rdata->type;
	ISC_LINK_INIT(&rt->common, link);

	dns_name_init(&name, NULL);
	dns_rdata_toregion(rdata, &region);
	rt->preference = uint16_fromregion(&region);
	isc_region_consume(&region, 2);
	dns_name_fromregion(&name, &region);
	dns_name_init(&rt->host, NULL);
	name_duporclone(&name, mctx, &rt->host);

	rt->mctx = mctx;
	return (ISC_R_SUCCESS);
}

static inline void
freestruct_rt(ARGS_FREESTRUCT) {
	dns_rdata_rt_t *rt = source;

	REQUIRE(source != NULL);
	REQUIRE(rt->common.rdtype == dns_rdatatype_rt);

	if (rt->mctx == NULL)
		return;

	dns_name_free(&rt->host, rt->mctx);
	rt->mctx = NULL;
}

static inline isc_result_t
additionaldata_rt(ARGS_ADDLDATA) {
	dns_name_t name;
	dns_offsets_t offsets;
	isc_region_t region;
	isc_result_t result;

	REQUIRE(rdata->type == dns_rdatatype_rt);

	dns_name_init(&name, offsets);
	dns_rdata_toregion(rdata, &region);
	isc_region_consume(&region, 2);
	dns_name_fromregion(&name, &region);

	result = (add)(arg, &name, dns_rdatatype_x25);
	if (result != ISC_R_SUCCESS)
		return (result);
	result = (add)(arg, &name, dns_rdatatype_isdn);
	if (result != ISC_R_SUCCESS)
		return (result);
	return ((add)(arg, &name, dns_rdatatype_a));
}

static inline isc_result_t
digest_rt(ARGS_DIGEST) {
	isc_region_t r1, r2;
	isc_result_t result;
	dns_name_t name;

	REQUIRE(rdata->type == dns_rdatatype_rt);

	dns_rdata_toregion(rdata, &r1);
	r2 = r1;
	isc_region_consume(&r2, 2);
	r1.length = 2;
	result = (digest)(arg, &r1);
	if (result != ISC_R_SUCCESS)
		return (result);
	dns_name_init(&name, NULL);
	dns_name_fromregion(&name, &r2);
	return (dns_name_digest(&name, digest, arg));
}

static inline bool
checkowner_rt(ARGS_CHECKOWNER) {

	REQUIRE(type == dns_rdatatype_rt);

	UNUSED(name);
	UNUSED(type);
	UNUSED(rdclass);
	UNUSED(wildcard);

	return (true);
}

static inline bool
checknames_rt(ARGS_CHECKNAMES) {
	isc_region_t region;
	dns_name_t name;

	REQUIRE(rdata->type == dns_rdatatype_rt);

	UNUSED(owner);

	dns_rdata_toregion(rdata, &region);
	isc_region_consume(&region, 2);
	dns_name_init(&name, NULL);
	dns_name_fromregion(&name, &region);
	if (!dns_name_ishostname(&name, false)) {
		if (bad != NULL)
			dns_name_clone(&name, bad);
		return (false);
	}
	return (true);
}

static inline int
casecompare_rt(ARGS_COMPARE) {
	return (compare_rt(rdata1, rdata2));
}

#endif	/* RDATA_GENERIC_RT_21_C */
