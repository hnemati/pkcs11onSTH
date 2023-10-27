/*
 * This Header file contains #defines and Data Structures
 * that all guests and the hypervisor require
 * should be consistent with header files deployed
 * in the library
 *
 * Author: Matthias Stockmayer
 */

#ifndef _PKCS11_MACROS_H_
#define _PKCS11_MACROS_H_

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

#include "cryptoki/pkcs11t.h"

/* Structs that the Guests use to pass arguments
 *
 * NOTE: If you change anything here, make sure to also
 * change in the same file in the Guest!!
 */


/* On Initialization, Guest provides good randomness */
typedef struct {
	unsigned char * entropy;
} InitArgs;

typedef struct GenerateKeyArgs {
	CK_ULONG 				template;
	CK_OBJECT_HANDLE_PTR 	handle_ptr;
} GenerateKeyArgs;

typedef struct WrapKeyArgs {
	CK_OBJECT_HANDLE 	hWrappingKey;
	CK_OBJECT_HANDLE	hKey;
	CK_BYTE_PTR 		pWrappedKey;
	CK_ULONG_PTR		pulWrappedKeyLen;
	CK_BYTE				cb[16];
} WrapKeyArgs;

typedef struct UnwrapKeyArgs {
	CK_OBJECT_HANDLE 	hUnwrappingKey;
	CK_BYTE_PTR			pWrappedKey;
	CK_ULONG			ulWrappedKeyLen;
	CK_ULONG			template;
	CK_OBJECT_HANDLE_PTR phKey;
	CK_BYTE				cb[16];
} UnwrapKeyArgs;

typedef struct EncryptArgs {
	CK_BYTE_PTR 		pData;
	CK_ULONG			ulDataLen;
	CK_BYTE_PTR 		pEncryptedData;
	CK_ULONG_PTR		pulEncryptedDataLen;
} EncryptArgs;

typedef struct DecryptArgs {
	CK_BYTE_PTR			pEncryptedData;
	CK_ULONG 			ulEncryptedDataLen;
	CK_BYTE_PTR			pData;
	CK_BYTE_PTR			pulDataLen;
} DecryptArgs;

typedef struct CryptInitArgs {
	CK_OBJECT_HANDLE 	hKey;
	CK_BYTE				cb[16];
} CryptInitArgs;


#endif /* _PKCS11_MACROS_H_ */
