/*
 * pkcs11_token.h
 *
 * Should be consitent with the header files
 * deployed in the guest
 *
 *      Author: Matthias Stockmayer
 *
 */

#ifndef _MINIMAL_PKCS11_H_
#define _MINIMAL_PKCS11_H_

// define pkcs11 related stuff st we can include the header files

#define CK_PTR *
#define CK_DEFINE_FUNCTION(returnType, name) returnType name
#define CK_DECLARE_FUNCTION(returnType, name) returnType name
#define CK_DECLARE_FUNCTION_POINTER(returnType, name) returnType (* name)
#define CK_CALLBACK_FUNCTION(returnType, name) returnType (* name)

#ifndef NULL_PTR
#define NULL_PTR 0
#endif

#ifndef NULL
#define NULL ((void *) 0)
#endif

// now we can include the "official" header files
#include "include/cryptoki/pkcs11.h"
// and header files containing additional definitions
#include "include/pkcs11_macros.h"
#include "ctr_drbg.h"


#define RV_SUCCESS 0
#define RV_FAILURE -1
#define RV_ALREADY_INITIALIZED 1

// some definitions to mimic "real" behavior of a token

#define IGNORE(P) (void) (P)

#define PKCS11_CK_INFO_MANUFACTURER_ID "Saarland University"
#define PKCS11_CK_INFO_LIBRARY_DESCRIPTION "Test Module"
#define PKCS11_CK_INFO_LIBRARY_VERSION_MAJOR 0x01
#define PKCS11_CK_INFO_LIBRARY_VERSION_MINOR 0x00

#define PKCS11_CK_SLOT_ID 1
#define PKCS11_CK_SLOT_INFO_DESCRIPTION "Test Slot"
#define PKCS11_CK_SLOT_INFO_MANUFACTURER_ID "Saarland University"

#define PKCS11_CK_TOKEN_INFO_LABEL "Saarland University"
#define PKCS11_CK_TOKEN_INFO_MANUFACTURER_ID "Saarland University"
#define PKCS11_CK_TOKEN_INFO_MODEL "Test Token"
#define PKCS11_CK_TOKEN_INFO_SERIAL_NUMBER "1337"
#define PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN 2048
#define PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN 1

// we only suport 1 session
#define PKCS11_CK_SESSION_ID 1

/* Cryptographic Parameters */
#define BLOCKLEN 16 // for 128 bit AES Keys and CTR Mode
#define BLOCKLENGTH 16
#define MAX_HANDLE 500 // upper limit of handles


/* The Standard requires to call C_EncryptInit before
 * C_Encrypt, so we need to maintain state
 */
enum crypt_state {
	CRYPT_UNINITIALIZED = 0,
	CRYPT_ENCRYPT_INIT,
	CRYPT_DECRYPT_INIT
};

/* Internal Data Structures */
/*
 * PKCS11 Object
 * handle: 		Unique ID
 * template: 	One of the three templates supported (see description!)
 * key: 		the value of the key
 */
typedef struct pkcs11_object_ {
	CK_OBJECT_HANDLE		handle;
	CK_ULONG				template;
	CK_BYTE					key[BLOCKLEN];
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

	CK_BBOOL 			initialized; // Entropy initialized
	CK_ULONG 			state; // State of encryption functions  1: EncryptInit, 2: DecryptInit, 0: Nothing Init

	CK_OBJECT_HANDLE 	current_key; // Key specified in EncryptInit / DecryptInit
	CK_BYTE				iv[16]; // The last Iv used



	ctr_drbg_ctx		ctr_ctx[1]; // CTR DRBG State
	pkcs11_object 		object_storage[MAX_HANDLE +1 ]; // Storage of 500 Keys
	CK_ULONG 			key_count; // count current keys stored

} pkcs11_ctx;

// int handler(CK_ULONG cmd, CK_VOID_PTR *params);


#endif /* _MINIMAL_PKCS11_H_ */
