/*
 * Utility functionality for the pkcs11 library
 * Mainly template parsing
 *
 * Author: MAtthias Stockmayer
 *
 */

#include "../../pkcs11/src/pkcs11_utils.h"


/* Parse template
 * return either trusted, usage or untrusted
 */
int parse_template(CK_ATTRIBUTE_PTR pMechanism, CK_ULONG ulCount, int recLimit) {

	if (! (--recLimit)) {
		printf("MAx Recursion reached: %d", recLimit);
		return PKCS11_INVALID_TEMPLATE;
	}

	CK_FLAGS flags = 0x00000000UL;
	CK_FLAGS wrapping_template;






	CK_FLAGS trusted = PKCS11_CKA_WRAP
			| PKCS11_CKA_UNWRAP
			| PKCS11_CKA_UNWRAP
			| PKCS11_CKA_SENSITIVE
			| PKCS11_CKA_EXTRACTABLE
			| PKCS11_CKA_TRUSTED
			| PKCS11_CKA_WRAP_WITH_TRUSTED
			| PKCS11_CKA_WRAP_TEMPLATE
			| PKCS11_CKA_UNWRAP_TEMPLATE;


	CK_FLAGS usage = PKCS11_CKA_ENCRYPT
			| PKCS11_CKA_DECRYPT
			| PKCS11_CKA_SENSITIVE
			| PKCS11_CKA_EXTRACTABLE
			| PKCS11_CKA_WRAP_WITH_TRUSTED;

	CK_FLAGS untrusted = PKCS11_CKA_ENCRYPT
			| PKCS11_CKA_DECRYPT
			| PKCS11_CKA_SENSITIVE
			| PKCS11_CKA_EXTRACTABLE;

	int i;

	for (i = 0; i < ulCount; i ++) {
		if ((pMechanism[i].pValue  == NULL) || (pMechanism[i].ulValueLen <= 0))
			return PKCS11_INVALID_TEMPLATE;

		switch (pMechanism[i].type) {
		case CKA_WRAP:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_WRAP;
			// printf("Wrap\n");
			break;
		case CKA_UNWRAP:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_UNWRAP;
			// printf("Unwrap\n");
			break;
		case CKA_ENCRYPT:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_ENCRYPT;
			// printf("Encrypt\n");
			break;
		case CKA_DECRYPT:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_DECRYPT;
			// printf("Decrypt\n");
			break;
		case CKA_SENSITIVE:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_SENSITIVE;
			// printf("Sensitive\n");
			break;
		case CKA_EXTRACTABLE:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_EXTRACTABLE;
			// printf("Extractable\n");
			break;
		case CKA_TRUSTED:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_TRUSTED;
			// printf("Trusted\n");
			break;
		case CKA_WRAP_WITH_TRUSTED:
			if (*(CK_BBOOL*) pMechanism[i].pValue == CK_TRUE)
				flags |= PKCS11_CKA_WRAP_WITH_TRUSTED;
			// printf("WWT\n");
			break;
		case CKA_WRAP_TEMPLATE:

			wrapping_template = parse_template(pMechanism[i].pValue, pMechanism[i].ulValueLen, recLimit);
			if (wrapping_template == PKCS11_USAGE_TEMPLATE)
				flags |= PKCS11_CKA_WRAP_TEMPLATE;
			else
				return PKCS11_INVALID_TEMPLATE;
			// printf("wt\n");

			break;
		case CKA_UNWRAP_TEMPLATE:
			// printf("ut\n");
			wrapping_template = parse_template(pMechanism[i].pValue, pMechanism[i].ulValueLen, recLimit);
			if (wrapping_template == PKCS11_USAGE_TEMPLATE)
				flags |= PKCS11_CKA_UNWRAP_TEMPLATE;
			else
				return PKCS11_INVALID_TEMPLATE;
			break;
		}
	}

	// printf("Template flags: %x\n", flags);
	// printf("Trusted Flags: %x\n", trusted);
	// printf("Usage Flags: %x\n", usage);
	// printf("Untrusted FLags: %x\n", untrusted);
	if (flags == trusted ) {
		// printf("Trusted Template\n");
		return PKCS11_TRUSTED_TEMPLATE;

	}
	if (flags == usage) {
		// printf("Usage Template \n");
		return PKCS11_USAGE_TEMPLATE;
	}
	if (flags == untrusted) {
		// printf("Untrusted Template\n");
		return PKCS11_UNTRUSTED_TEMPLATE;
	}

	// printf("Invalid Template\n");
	return PKCS11_INVALID_TEMPLATE;
}


void print_hex(unsigned char *bytes, int count) {
	int i;
	for (i = 0; i < count; i++) {
		if (i % BLOCKLENGTH == 0)
			printf("\n");
		printf("%2", bytes[i]);
	}
	printf("\n");
}




