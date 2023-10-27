/*
 * pkcs11_utils.h
 *
 *  Created on: Nov 27, 2017
 *      Author: Matthias Stockmayer
 */

#ifndef GUESTS_PKCS11_SRC_PKCS11_UTILS_H_
#define GUESTS_PKCS11_SRC_PKCS11_UTILS_H_

#include "pkcs11_library.h"


#define PKCS11_INVALID_TEMPLATE -1
#define PKCS11_TRUSTED_TEMPLATE 0
#define PKCS11_USAGE_TEMPLATE 1
#define PKCS11_UNTRUSTED_TEMPLATE 2


#define PKCS11_CKA_WRAP					0x00000001UL
#define PKCS11_CKA_UNWRAP				0x00000002UL
#define PKCS11_CKA_ENCRYPT				0x00000004UL
#define PKCS11_CKA_DECRYPT				0x00000008UL
#define PKCS11_CKA_SENSITIVE			0x00000010UL
#define PKCS11_CKA_EXTRACTABLE			0x00000020UL
#define PKCS11_CKA_TRUSTED				0x00000040UL
#define PKCS11_CKA_WRAP_WITH_TRUSTED	0x00000080UL
#define PKCS11_CKA_WRAP_TEMPLATE 		0x00000100UL
#define PKCS11_CKA_UNWRAP_TEMPLATE		0x00000200UL



#ifndef NULL
#define NULL ((void*) 0)
#endif

#define BLOCKLENGTH 16

void print_hex(unsigned char *bytes, int count);

int parse_template(CK_ATTRIBUTE_PTR pMechanism, CK_ULONG ulCount, int recLimit);


#endif /* GUESTS_PKCS11_SRC_PKCS11_UTILS_H_ */
