/*
 * minimal_pkcs11.h

 *
 *  Created on: 14.11.2017
 *      Author: Matthias Stockmayer
 *      inspired by pkcs11-mock implementation by Pkcs11Interop Project
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
#include "../../pkcs11/src/cryptoki/pkcs11.h"
#include "../../pkcs11/src/include/pkcs11_macros.h"


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
#define PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN 4
#define PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN 4


#define PKCS11_CK_SESSION_ID 1

#endif /* _MINIMAL_PKCS11_H_ */
