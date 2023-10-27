#include <lib.h>
#include <types.h>
#include <uclib.h>
#include "pw_manager.h"
#include "../../pkcs11/src/communication.h"
#include "../../pkcs11/src/pkcs11_utils.h"
#include "../../pkcs11/src/pw_manager.h"
#include "pkcs11_library.h"

void test_initialize()
{
	InitArgs initArgs;
	uint32_t res;
	unsigned char entropy[32] = {
		0x41, 0x9A, 0x17, 0xB2,
		0x6E, 0x3F, 0x49, 0xC4,
		0xB9, 0x83, 0x80, 0xAD,
		0x70, 0xE1, 0x95, 0xAC,
		0xAB, 0x2A, 0x7A, 0x49,
		0x61, 0xCB, 0x19, 0xC9,
		0x21, 0x3D, 0x5B, 0x02,
		0xAC, 0x08, 0xDB, 0x00
	};

	initArgs.entropy = entropy;
	res = call_hypervisor(CMD_INITIALIZE, (uint32_t) &initArgs, 0, 0);
	if (res == RV_SUCCESS) {
		printf("Token initialized\n");
	}
	else {
		printf("Failed to initialize Token.\n");
	}
}


void test_generate_key() {
	printf("\n\nTEST GENERATE KEY\n");
	CK_RV res;
	CK_SESSION_HANDLE hSession = 1;
	CK_OBJECT_HANDLE phKey;
	CK_MECHANISM mechanism = { CKM_AES_CTR, 0, 0 };
	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_BBOOL true = CK_TRUE;


	CK_ATTRIBUTE wrappingTemplate[] = {
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};
	CK_ATTRIBUTE keyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_WRAP, &true, sizeof(true)},
			{CKA_UNWRAP, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_TEMPLATE, &wrappingTemplate, 5},
			{CKA_UNWRAP_TEMPLATE, &wrappingTemplate, 5}
	};
	res = C_GenerateKey(hSession, &mechanism, keyTemplate, 10, &phKey);

	if (res == CKR_OK) {
		printf("Key Handle: %x\n", phKey);
		printf("TEST GENERATE KEY: SUCCESS\n");
	}
	else
		printf("TEST GENERATE KEY: FAILED\n");
}

/*
 * 1. create two keys (trusted, usage)
 * 2. wrap usage key with trusted key
 */

void test_wrap_key() {

	printf("\n\nTEST WRAP KEY \n");
	uint32_t res;
	CK_RV rv;

	CK_SESSION_HANDLE hSession = 1;
	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_MECHANISM mechanism = { CKM_AES_CTR, NULL_PTR, 0 };
	CK_BBOOL true = CK_TRUE;
	CK_BYTE pWrappedKey[16];
	CK_OBJECT_HANDLE hWrappingKey, hUsageKey;
	CK_ULONG ulWrappedKeyLen;


	/* trusted key template */
	CK_ATTRIBUTE wrappingTemplate[] = {
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};
	CK_ATTRIBUTE keyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_WRAP, &true, sizeof(true)},
			{CKA_UNWRAP, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_TEMPLATE, &wrappingTemplate, 5},
			{CKA_UNWRAP_TEMPLATE, &wrappingTemplate, 5}
	};


	rv = C_GenerateKey(hSession, &mechanism, keyTemplate, 10, &hWrappingKey);
	if (rv != CKR_OK ) {
		printf("TEST WRAP KEY: FAILED with %d\n", rv);
		return;
	}

	/* generate usage key */
	CK_ATTRIBUTE usageKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};

	rv = C_GenerateKey(hSession, &mechanism, usageKeyTemplate, 7, &hUsageKey);
	if (rv != CKR_OK) {
		printf("TEST WRAP KEY: FAILED with %d\n", rv);
		return;
	}

	/* Wrap Key */
	rv = C_WrapKey(hSession, &mechanism, hWrappingKey, hUsageKey, pWrappedKey, &ulWrappedKeyLen);
	if (rv != CKR_OK) {
		printf("TEST WRAP KEY: FAILED with %d\n", rv);
		return;
	} else {
		printf("Wrapped Key:");
		print_hex(pWrappedKey, 16);
		printf("TEST WRAP KEY: SUCCESS\n");

	}
}

/*
 * 1. Genertate two keys
 * 2. Wrap key
 * 3. unwrap key
 */
void test_unwrap_key() {
	printf("\n\nTEST UNWRAP KEY\n");
	CK_SESSION_HANDLE hSession = 1;
	CK_MECHANISM mechanism = { CKM_AES_CTR, NULL_PTR, 0 };
	CK_OBJECT_HANDLE hWrappingKey, hUsageKey, hKey;
	CK_BBOOL true = CK_TRUE;
	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_ULONG ulWrappedKeyLen;
	CK_BYTE pWrappedKey[16];

	CK_RV rv;


	/* trusted key */
	CK_ATTRIBUTE wrappingTemplate[] = {
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};
	CK_ATTRIBUTE keyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_WRAP, &true, sizeof(true)},
			{CKA_UNWRAP, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_TEMPLATE, &wrappingTemplate, 5},
			{CKA_UNWRAP_TEMPLATE, &wrappingTemplate, 5}
	};

	rv = C_GenerateKey(hSession, &mechanism, keyTemplate, 10, &hWrappingKey);
	if (rv != CKR_OK) {
		printf("TEST UNWRAP KEY: FAILURE\n");
		return;
	}

	/* generate usage key */
	CK_ATTRIBUTE usageKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};

	rv = C_GenerateKey(hSession, &mechanism, usageKeyTemplate, 7, &hUsageKey);
	if (rv != CKR_OK) {
		printf("TEST UNWRAP KEY: FAILURE\n");
		return;
	}


	/* Wrap usagekey using trusted key */
	rv = C_WrapKey(hSession, &mechanism, hWrappingKey, hUsageKey, pWrappedKey, &ulWrappedKeyLen);
	if (rv != CKR_OK) {
		printf("TEST UNWRAP KEY: FAILURE\n");
		return;
	}

	/* ... and unwrap it again */
	rv = C_UnwrapKey(hSession, &mechanism, hWrappingKey, pWrappedKey, 16, usageKeyTemplate, 7, &hKey);
	if (rv != CKR_OK) {
		printf("TEST UNWRAPPING KEY: FAILURE\n");
		return;
	} else {
		printf("TEST UNWRAPPING KEY: SUCCESS\n");
	}

	return;
}

/*
void test_crypto_correct() {
	uint32_t res;
	res = call_hypervisor(CMD_TEST_CRYPTO, 0, 0, 0);

} */

void test_generate_random() {
	printf("TEST GENERATE RANDOM\n");
	CK_SESSION_HANDLE hSession = 1;
	CK_RV rv;
	unsigned char rand[64];
	CK_ULONG ulRandomLen = 64;

	rv = C_GenerateRandom(hSession, rand, ulRandomLen);
	print_hex(rand, 64);
	if (rv != CKR_OK)
		printf("TEST GENERATE RANDOM: FAILED\n");
	else
		printf("TEST_GENERATE RANDOM: SUCCESS\n");
}

/*
 * A lot is going on in this function:
 * 1. General Session Management (SO and user)
 * 2. Key Generation
 * 3. Clulow's attack
 */
void test_attack() {

	CK_BYTE cb[] = {
			0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x13, 0x37
	};




	CK_RV rv;


	CK_SESSION_HANDLE hSession = 1;
	CK_MECHANISM mechanism = { CKM_AES_CTR, NULL_PTR, 0 };
	CK_OBJECT_HANDLE hTrustedKey, hUsageKey, hKey;
	CK_BBOOL true = CK_TRUE;
	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_ULONG ulWrappedKeyLen;
	CK_BYTE pWrappedKey[16];



	/* trusted key */
	CK_ATTRIBUTE wrappingTemplate[] = {
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};
	CK_ATTRIBUTE trustedKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_WRAP, &true, sizeof(true)},
			{CKA_UNWRAP, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_TEMPLATE, &wrappingTemplate, 5},
			{CKA_UNWRAP_TEMPLATE, &wrappingTemplate, 5}
	};

	/* usage key */
	CK_ATTRIBUTE usageKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};

	/* 1. Cannot create key without initialization */
	rv = C_GenerateKey(1, &mechanism, usageKeyTemplate, 7, &hUsageKey);
	if (rv == CKR_OK) {
		printf("Test 1 failed! %x\n", rv);
	} else {
		printf("Test 1 successful: %x\n", rv);
	}

	/* 2. User cannot open Session until PIN is initialized by SO */
	C_Initialize(NULL);

	CK_BYTE usrPIN[4] = {0x13, 0x37, 0xFA, 0x1l };
	CK_BYTE soPin[4] = { 0x01, 0x02, 0x03, 0x04 };
	CK_FLAGS flags  = CKF_SERIAL_SESSION | CKF_RW_SESSION;
	rv = C_OpenSession(1, flags, NULL, NULL, &hSession);
	if (rv == CKR_OK) {
		printf("Test 2 failed! %x\n", rv);
	} else {
		printf("Test 2 successful: %x\n", rv);
	}

	/* 3. SO can set its own PIn and user PIN */
	CK_SLOT_ID slotId = 1;
	CK_UTF8CHAR pLabel[16] = "Test Token";

	rv = C_InitToken(slotId, soPin, 4, pLabel);
	if (rv != CKR_OK) {
		printf("Test 3.1  failed! %x\n", rv);
	} else {
		printf("Test 3.1 successful: %x\n", rv);
	}


	rv = C_OpenSession(slotId, flags, NULL, NULL, &hSession);
	if (rv != CKR_OK) {
		printf("Test 3.2 failed! %x\n", rv);
	} else {
		printf("Test 3.2 successful: %x\n", rv);
	}

	rv = C_Login(hSession, CKU_SO, soPin, 4);
	if (rv != CKR_OK) {
		printf("Test 3.3 failed! %x\n", rv);
	} else {
		printf("Test 3.3 successful: %x\n", rv);
	}


	rv = C_InitPIN(hSession, usrPIN, 4);
	if (rv != CKR_OK) {
		printf("Test 3.4 failed! %x\n", rv);
	} else {
		printf("Test 3.4 successful: %x\n", rv);
	}

	/* 4. SO can create TRUSTED key */
	rv = C_GenerateKey(hSession, &mechanism, trustedKeyTemplate, 10, &hTrustedKey);
	if (rv != CKR_OK) {
		printf("Test 4.1 failed! %x\n", rv);
	} else {
		printf("Test 4.1 successful: %x\n", rv);
	}

	rv = C_Logout(hSession);
	if (rv != CKR_OK) {
		printf("Test 4.2 failed! %x\n", rv);
	} else {
		printf("Test 4.2 successful: %x\n", rv);
	}

	/* 5. User can create usage key and not wrap trusted key */
	rv = C_Login(hSession, CKU_USER, usrPIN, 4);
	if (rv != CKR_OK) {
		printf("Test 5.1 failed! %x\n", rv);
	} else {
		printf("Test 5.1 successful: %x\n", rv);
	}

	rv = C_GenerateKey(hSession, &mechanism, trustedKeyTemplate, 10, &hTrustedKey);
	if (rv == CKR_OK) {
		printf("Test 5.2 failed! %x\n", rv);
	} else {
		printf("Test 5.2 successful: %x\n", rv);
	}

	rv = C_GenerateKey(hSession, &mechanism, usageKeyTemplate, 7, &hUsageKey);
	if (rv != CKR_OK) {
		printf("Test 5.3 failed %x\n", rv);
	} else {
		printf("Test 5.3 successful: %x\n", rv);
	}

	CK_MECHANISM wrapMechanism;
	CK_AES_CTR_PARAMS ctrParams;
	memcpy(ctrParams.cb, cb, 16);
	ctrParams.ulCounterBits = 128;
	wrapMechanism.mechanism = CKM_AES_CTR;

	wrapMechanism.pParameter = (CK_VOID_PTR) &ctrParams;
	wrapMechanism.ulParameterLen = sizeof(ctrParams);
	CK_BYTE wrappedKey[16];
	CK_ULONG wrappedKeyLen;

	rv = C_WrapKey(hSession, &wrapMechanism, hTrustedKey, hTrustedKey, wrappedKey, &wrappedKeyLen);
	if (rv == CKR_OK) {
		printf("Test 5.4 failed! %x\n", rv);
	} else {
		printf("Test 5.4 successful: %x\n", rv);
	}


	cb[14] = 0xAB; // poor mans increment
	memcpy(ctrParams.cb, cb, 16);
	rv = C_WrapKey(hSession, &wrapMechanism, hTrustedKey, hUsageKey, wrappedKey, &wrappedKeyLen);
	if (rv != CKR_OK) {
		printf("Test 5.5 failed! %x\n", rv);
	} else {
		printf("Test 5.5 successful : %x\n", rv);
	}

	CK_ULONG hUnwrappedKey;
	rv = C_UnwrapKey(hSession, &wrapMechanism, hTrustedKey, wrappedKey, 16, usageKeyTemplate, 7, &hUnwrappedKey);
	if (rv != CKR_OK) {
		printf("Test 5.6 failed! %x\n", rv);
	} else  {
		printf("Test 5.6 successful : %x\n", rv); // Enable token debug to see if keys match!
	}

	/* This is exactly Clulow's attack */

	CK_MECHANISM encryptMechansims;
	cb[13] = 0xFF; // even more poor mans increment
	memcpy(ctrParams.cb, cb, 16);

	encryptMechansims.mechanism = CKM_AES_CTR;
	encryptMechansims.pParameter = (CK_VOID_PTR) &ctrParams;
	encryptMechansims.ulParameterLen = 2;
	CK_BYTE_PTR decrypted[16];
	CK_ULONG decryptedLen;
	rv = C_DecryptInit(hSession, &encryptMechansims, hTrustedKey);
	if (rv == CKR_OK) {
		printf("Test 5.7 (Clulow) failed! %x\n", rv);
	} else {
		printf("Test 5.7 successful: %x\n", rv);
	}

	rv = C_Decrypt(hSession, wrappedKey, 16, decrypted, &decryptedLen);
	if (rv == CKR_OK) {
		printf("Test 5.8 failed! %x\n", rv);
	} else {
		printf("Test 5.8 successful: %x\n", rv);
	}
	return;
}


/*
void test_hyp() {
	uint32_t res = call_hypervisor(CMD_TEST_HYP, 0, 0, 0);
}
*/

void _main()
{

	//test_attack();
	pw_manager();
}


/* each guest has to provide a handler rpc */
void handler_rpc(unsigned callNum, void *params)
{
	return;
}
