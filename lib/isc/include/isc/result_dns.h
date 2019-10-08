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

#ifndef ISC_DNS_RESULT_H
#define ISC_DNS_RESULT_H 1

/*! \file isc/result_dns.h */

#include <isc/resultclass.h>

/*
 * DNS library result codes
 */
#define DNS_R_LABELTOOLONG ISC_RESULTCODE_DNS(0)
#define DNS_R_BADESCAPE	   ISC_RESULTCODE_DNS(1)
/*
 * Since we dropped the support of bitstring labels, deprecate the related
 * result codes too.

#define DNS_R_BADBITSTRING		ISC_RESULTCODE_DNS(2)
#define DNS_R_BITSTRINGTOOLONG		ISC_RESULTCODE_DNS(3)
*/
#define DNS_R_EMPTYLABEL	ISC_RESULTCODE_DNS(4)
#define DNS_R_BADDOTTEDQUAD	ISC_RESULTCODE_DNS(5)
#define DNS_R_INVALIDNS		ISC_RESULTCODE_DNS(6)
#define DNS_R_UNKNOWN		ISC_RESULTCODE_DNS(7)
#define DNS_R_BADLABELTYPE	ISC_RESULTCODE_DNS(8)
#define DNS_R_BADPOINTER	ISC_RESULTCODE_DNS(9)
#define DNS_R_TOOMANYHOPS	ISC_RESULTCODE_DNS(10)
#define DNS_R_DISALLOWED	ISC_RESULTCODE_DNS(11)
#define DNS_R_EXTRATOKEN	ISC_RESULTCODE_DNS(12)
#define DNS_R_EXTRADATA		ISC_RESULTCODE_DNS(13)
#define DNS_R_TEXTTOOLONG	ISC_RESULTCODE_DNS(14)
#define DNS_R_NOTZONETOP	ISC_RESULTCODE_DNS(15)
#define DNS_R_SYNTAX		ISC_RESULTCODE_DNS(16)
#define DNS_R_BADCKSUM		ISC_RESULTCODE_DNS(17)
#define DNS_R_BADAAAA		ISC_RESULTCODE_DNS(18)
#define DNS_R_NOOWNER		ISC_RESULTCODE_DNS(19)
#define DNS_R_NOTTL		ISC_RESULTCODE_DNS(20)
#define DNS_R_BADCLASS		ISC_RESULTCODE_DNS(21)
#define DNS_R_NAMETOOLONG	ISC_RESULTCODE_DNS(22)
#define DNS_R_PARTIALMATCH	ISC_RESULTCODE_DNS(23)
#define DNS_R_NEWORIGIN		ISC_RESULTCODE_DNS(24)
#define DNS_R_UNCHANGED		ISC_RESULTCODE_DNS(25)
#define DNS_R_BADTTL		ISC_RESULTCODE_DNS(26)
#define DNS_R_NOREDATA		ISC_RESULTCODE_DNS(27)
#define DNS_R_CONTINUE		ISC_RESULTCODE_DNS(28)
#define DNS_R_DELEGATION	ISC_RESULTCODE_DNS(29)
#define DNS_R_GLUE		ISC_RESULTCODE_DNS(30)
#define DNS_R_DNAME		ISC_RESULTCODE_DNS(31)
#define DNS_R_CNAME		ISC_RESULTCODE_DNS(32)
#define DNS_R_BADDB		ISC_RESULTCODE_DNS(33)
#define DNS_R_ZONECUT		ISC_RESULTCODE_DNS(34)
#define DNS_R_BADZONE		ISC_RESULTCODE_DNS(35)
#define DNS_R_MOREDATA		ISC_RESULTCODE_DNS(36)
#define DNS_R_UPTODATE		ISC_RESULTCODE_DNS(37)
#define DNS_R_TSIGVERIFYFAILURE ISC_RESULTCODE_DNS(38)
#define DNS_R_TSIGERRORSET	ISC_RESULTCODE_DNS(39)
#define DNS_R_SIGINVALID	ISC_RESULTCODE_DNS(40)
#define DNS_R_SIGEXPIRED	ISC_RESULTCODE_DNS(41)
#define DNS_R_SIGFUTURE		ISC_RESULTCODE_DNS(42)
#define DNS_R_KEYUNAUTHORIZED	ISC_RESULTCODE_DNS(43)
#define DNS_R_INVALIDTIME	ISC_RESULTCODE_DNS(44)
#define DNS_R_EXPECTEDTSIG	ISC_RESULTCODE_DNS(45)
#define DNS_R_UNEXPECTEDTSIG	ISC_RESULTCODE_DNS(46)
#define DNS_R_INVALIDTKEY	ISC_RESULTCODE_DNS(47)
#define DNS_R_HINT		ISC_RESULTCODE_DNS(48)
#define DNS_R_DROP		ISC_RESULTCODE_DNS(49)
#define DNS_R_NOTLOADED		ISC_RESULTCODE_DNS(50)
#define DNS_R_NCACHENXDOMAIN	ISC_RESULTCODE_DNS(51)
#define DNS_R_NCACHENXRRSET	ISC_RESULTCODE_DNS(52)
#define DNS_R_WAIT		ISC_RESULTCODE_DNS(53)
#define DNS_R_NOTVERIFIEDYET	ISC_RESULTCODE_DNS(54)
#define DNS_R_NOIDENTITY	ISC_RESULTCODE_DNS(55)
#define DNS_R_NOJOURNAL		ISC_RESULTCODE_DNS(56)
#define DNS_R_ALIAS		ISC_RESULTCODE_DNS(57)
#define DNS_R_USETCP		ISC_RESULTCODE_DNS(58)
#define DNS_R_NOVALIDSIG	ISC_RESULTCODE_DNS(59)
#define DNS_R_NOVALIDNSEC	ISC_RESULTCODE_DNS(60)
#define DNS_R_NOTINSECURE	ISC_RESULTCODE_DNS(61)
#define DNS_R_UNKNOWNSERVICE	ISC_RESULTCODE_DNS(62)
#define DNS_R_RECOVERABLE	ISC_RESULTCODE_DNS(63)
#define DNS_R_UNKNOWNOPT	ISC_RESULTCODE_DNS(64)
#define DNS_R_UNEXPECTEDID	ISC_RESULTCODE_DNS(65)
#define DNS_R_SEENINCLUDE	ISC_RESULTCODE_DNS(66)
#define DNS_R_NOTEXACT		ISC_RESULTCODE_DNS(67)
#define DNS_R_BLACKHOLED	ISC_RESULTCODE_DNS(68)
#define DNS_R_BADALG		ISC_RESULTCODE_DNS(69)
#define DNS_R_METATYPE		ISC_RESULTCODE_DNS(70)
#define DNS_R_CNAMEANDOTHER	ISC_RESULTCODE_DNS(71)
#define DNS_R_SINGLETON		ISC_RESULTCODE_DNS(72)
#define DNS_R_HINTNXRRSET	ISC_RESULTCODE_DNS(73)
#define DNS_R_NOMASTERFILE	ISC_RESULTCODE_DNS(74)
#define DNS_R_UNKNOWNPROTO	ISC_RESULTCODE_DNS(75)
#define DNS_R_CLOCKSKEW		ISC_RESULTCODE_DNS(76)
#define DNS_R_BADIXFR		ISC_RESULTCODE_DNS(77)
#define DNS_R_NOTAUTHORITATIVE	ISC_RESULTCODE_DNS(78)
#define DNS_R_NOVALIDKEY	ISC_RESULTCODE_DNS(79)
#define DNS_R_OBSOLETE		ISC_RESULTCODE_DNS(80)
#define DNS_R_FROZEN		ISC_RESULTCODE_DNS(81)
#define DNS_R_UNKNOWNFLAG	ISC_RESULTCODE_DNS(82)
#define DNS_R_EXPECTEDRESPONSE	ISC_RESULTCODE_DNS(83)
#define DNS_R_NOVALIDDS		ISC_RESULTCODE_DNS(84)
#define DNS_R_NSISADDRESS	ISC_RESULTCODE_DNS(85)
#define DNS_R_REMOTEFORMERR	ISC_RESULTCODE_DNS(86)
#define DNS_R_TRUNCATEDTCP	ISC_RESULTCODE_DNS(87)
#define DNS_R_LAME		ISC_RESULTCODE_DNS(88)
#define DNS_R_UNEXPECTEDRCODE	ISC_RESULTCODE_DNS(89)
#define DNS_R_UNEXPECTEDOPCODE	ISC_RESULTCODE_DNS(90)
#define DNS_R_CHASEDSSERVERS	ISC_RESULTCODE_DNS(91)
#define DNS_R_EMPTYNAME		ISC_RESULTCODE_DNS(92)
#define DNS_R_EMPTYWILD		ISC_RESULTCODE_DNS(93)
#define DNS_R_BADBITMAP		ISC_RESULTCODE_DNS(94)
#define DNS_R_FROMWILDCARD	ISC_RESULTCODE_DNS(95)
#define DNS_R_BADOWNERNAME	ISC_RESULTCODE_DNS(96)
#define DNS_R_BADNAME		ISC_RESULTCODE_DNS(97)
#define DNS_R_DYNAMIC		ISC_RESULTCODE_DNS(98)
#define DNS_R_UNKNOWNCOMMAND	ISC_RESULTCODE_DNS(99)
#define DNS_R_MUSTBESECURE	ISC_RESULTCODE_DNS(100)
#define DNS_R_COVERINGNSEC	ISC_RESULTCODE_DNS(101)
#define DNS_R_MXISADDRESS	ISC_RESULTCODE_DNS(102)
#define DNS_R_DUPLICATE		ISC_RESULTCODE_DNS(103)
#define DNS_R_INVALIDNSEC3	ISC_RESULTCODE_DNS(104)
#define DNS_R_NOTMASTER		ISC_RESULTCODE_DNS(105)
#define DNS_R_BROKENCHAIN	ISC_RESULTCODE_DNS(106)
#define DNS_R_EXPIRED		ISC_RESULTCODE_DNS(107)
#define DNS_R_NOTDYNAMIC	ISC_RESULTCODE_DNS(108)
#define DNS_R_BADEUI		ISC_RESULTCODE_DNS(109)
#define DNS_R_NTACOVERED	ISC_RESULTCODE_DNS(110)
#define DNS_R_BADCDS		ISC_RESULTCODE_DNS(111)
#define DNS_R_BADCDNSKEY	ISC_RESULTCODE_DNS(112)
#define DNS_R_OPTERR		ISC_RESULTCODE_DNS(113)
#define DNS_R_BADDNSTAP		ISC_RESULTCODE_DNS(114)
#define DNS_R_BADTSIG		ISC_RESULTCODE_DNS(115)
#define DNS_R_BADSIG0		ISC_RESULTCODE_DNS(116)
#define DNS_R_TOOMANYRECORDS	ISC_RESULTCODE_DNS(117)
#define DNS_R_VERIFYFAILURE	ISC_RESULTCODE_DNS(118)

#define DNS_R_NRESULTS 119 /*%< Number of results */

/*
 * DNS wire format rcodes.
 *
 * By making these their own class we can easily convert them into the
 * wire-format rcode value simply by masking off the resultclass.
 */
#define DNS_R_NOERROR  ISC_RESULTCODE_DNSRCODE(0)
#define DNS_R_FORMERR  ISC_RESULTCODE_DNSRCODE(1)
#define DNS_R_SERVFAIL ISC_RESULTCODE_DNSRCODE(2)
#define DNS_R_NXDOMAIN ISC_RESULTCODE_DNSRCODE(3)
#define DNS_R_NOTIMP   ISC_RESULTCODE_DNSRCODE(4)
#define DNS_R_REFUSED  ISC_RESULTCODE_DNSRCODE(5)
#define DNS_R_YXDOMAIN ISC_RESULTCODE_DNSRCODE(6)
#define DNS_R_YXRRSET  ISC_RESULTCODE_DNSRCODE(7)
#define DNS_R_NXRRSET  ISC_RESULTCODE_DNSRCODE(8)
#define DNS_R_NOTAUTH  ISC_RESULTCODE_DNSRCODE(9)
#define DNS_R_NOTZONE  ISC_RESULTCODE_DNSRCODE(10)
#define DNS_R_RCODE11  ISC_RESULTCODE_DNSRCODE(11)
#define DNS_R_RCODE12  ISC_RESULTCODE_DNSRCODE(12)
#define DNS_R_RCODE13  ISC_RESULTCODE_DNSRCODE(13)
#define DNS_R_RCODE14  ISC_RESULTCODE_DNSRCODE(14)
#define DNS_R_RCODE15  ISC_RESULTCODE_DNSRCODE(15)
#define DNS_R_BADVERS  ISC_RESULTCODE_DNSRCODE(16)

#define DNS_R_NRCODERESULTS 17 /*%< Number of rcode results */

#endif /* ISC_DNS_RESULT_H */
