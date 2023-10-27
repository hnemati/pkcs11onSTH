/*
 * This Header file contains #defines and Data Structures
 * that all guests and the hypervisor require
 */

#ifndef GUESTS_P11_LIB_SRC_PKCS11_MACROS_H_
#define GUESTS_P11_LIB_SRC_PKCS11_MACROS_H_

enum pkcs11_commands {
	CMD_INITIALIZE = 0,
	CMD_IS_INITIALIZED,
	CMD_FINALIZE,
	CMD_GENERATE_KEY,
	CMD_WRAP_KEY,
	CMD_UNWRAP_KEY,
	CMD_ENCRYPT_INIT,
	CMD_ENCRYPT,
	CMD_DECRYPT_INIT,
	CMD_DECRYPT,
	CMD_DESTROY_EVERYTHING
};

#define RV_SUCCESS 0
#define RV_FAILURE -1

/* Templates */
enum TEMPLATE {
	TRUSTED_TEMPLATE,
	USAGE_TEMPLATE,
	UNTRUSTED_TEMPLATE
};

/* Internal Data Structures */
#include "pkcs11t.h"

/*
 * PKCS11 Object
 * handle: 		Unique ID
 * template: 	One of the three templates supported (see description!)
 * data: 		key, encrypted data, or plain data
 */
typedef struct pkcs11_object_ {
	CK_OBJECT_HANDLE		handle;
	CK_ULONG				template;
	CK_BYTE_PTR				key;
	struct pkcs11_object_ 	*next;
} pkcs11_object;

/*
 * PKCS11 Context
 * intialized: 		CK_True, if token is initialized
 * ctr_drbg_ctx: 	State of CTR_DRBG
 * head:			Current head of list containing PKCS11 Objects
 * state:			Current state of operation (Encrypt Init, Encrypt, Encrypt final,...)
 * iv: 				Initialization Vector, incremented after each encryption
 */
typedef struct {
	CK_BBOOL 			initialized;
	ctr_drbg_ctx		ctr_ctx[1];
	pkcs11_object * 	head;
	CK_ULONG 			state; // 1: EncryptInit, 2: DecryptInit, 0: Nothing Init
	CK_OBJECT_HANDLE 	current_key; // Key specified in EncryptInit / DecryptInit
	CK_BYTE_PTR			iv;
} pkcs11_ctx;

/* Struct in which hypervisor passes Arguments */

typedef struct {
	unsigned char * entropy;
} InitArgs;

typedef struct {
	CK_ULONG 				template;
	CK_OBJECT_HANDLE_PTR 	handle_ptr;
} GenerateKeyArgs;

typedef struct {
	CK_OBJECT_HANDLE 	hWrappingKey;
	CK_OBJECT_HANDLE	hKey;
	CK_BYTE_PTR 		pWrappedKey;
	CK_ULONG_PTR		pulWrappedKeyLen;
} WrapKeyArgs;

typedef struct {
	CK_OBJECT_HANDLE 	hUnwrappingKey;
	CK_BYTE_PTR			pWrappedKey;
	CK_ULONG			ulWrappedKeyLen;
	CK_ULONG			template;
	CK_OBJECT_HANDLE_PTR phKey;
} UnwrapKeyArgs;

typedef struct {
	CK_BYTE_PTR 		pData;
	CK_ULONG			ulDataLen;
	CK_BYTE_PTR 		pEncryptedData;
	CK_ULONG_PTR		pulEncryptedDataLen;
} EncryptArgs;

typedef struct {
	CK_BYTE_PTR			pEncryptedData;
	CK_ULONG 			ulEncryptedDataLen;
	CK_BYTE_PTR			pData;
	CK_BYTE_PTR			pulDataLen;
} DecryptArgs;

typedef struct {
	CK_OBJECT_HANDLE 	hKey;
} CryptInitArgs;


#endif /* GUESTS_P11_LIB_SRC_PKCS11_MACROS_H_ */
