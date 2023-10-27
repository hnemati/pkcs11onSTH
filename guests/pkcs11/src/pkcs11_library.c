/*
 * The real library.
 * Should be comoiled to an .so if deployed on a real linux,
 * otherwise the header filed pkcs11_library.h should be
 * inlcuded to mimic library
 *
 * Author: Matthias Stockmyer
 *
 */

#include <uclib.h>
#include "communication.h"

#include "pkcs11_library.h"
#include "pkcs11_utils.h"

//#define PKCS_DEBUG
/* Global Variables managing token and session states */


CK_UTF8CHAR soPin[4];
CK_UTF8CHAR usrPin[4];

// Token Initialized: SO successfully logged in at least once
// different from token seeded!
CK_BBOOL token_initialized = CK_FALSE;
CK_BBOOL session_open = CK_FALSE;

CK_ULONG session_state = CKS_RO_PUBLIC_SESSION;


/* Function List containing addresses of all functions */

CK_FUNCTION_LIST function_list =
{
		/* Version */
		{2, 40},
		/* General-Purpose functions */
		&C_Initialize,
		&C_Finalize,
		&C_GetInfo,
		&C_GetFunctionList,
		/* Slot and Token Management */
		&C_GetSlotList,
		&C_GetSlotInfo,
		&C_GetTokenInfo,
		&C_GetMechanismList,
		&C_GetMechanismInfo,
		&C_InitToken,
		&C_InitPIN,
		&C_SetPIN,
		&C_OpenSession,
		&C_CloseSession,
		&C_CloseAllSessions,
		&C_GetSessionInfo,
		&C_GetOperationState,
		&C_SetOperationState,
		&C_Login,
		&C_Logout,

		/* Object Management functions */
		&C_CreateObject,
		&C_CopyObject,
		&C_DestroyObject,
		&C_GetObjectSize,
		&C_GetAttributeValue,
		&C_SetAttributeValue,
		&C_FindObjectsInit,
		&C_FindObjects,
		&C_FindObjectsFinal,

		/* Encryption Functions */
		&C_EncryptInit,
		&C_Encrypt,
		&C_EncryptUpdate,
		&C_EncryptFinal,

		/* Decryption Functions */
		&C_DecryptInit,
		&C_Decrypt,
		&C_DecryptUpdate,
		&C_DecryptFinal,

		/* Signing and MACing */
		&C_DigestInit,
		&C_Digest,
		&C_DigestUpdate,
		&C_DigestKey,
		&C_DigestFinal,
		&C_SignInit,
		&C_Sign,
		&C_SignUpdate,
		&C_SignFinal,
		&C_SignRecoverInit,
		&C_SignRecover,
		&C_VerifyInit,
		&C_Verify,
		&C_VerifyUpdate,
		&C_VerifyFinal,
		&C_VerifyRecoverInit,
		&C_VerifyRecover,

		/* Dual crypto functions */
		&C_DigestEncryptUpdate,
		&C_DecryptDigestUpdate,
		&C_SignEncryptUpdate,
		&C_DecryptVerifyUpdate,

		/* Key Management functions */
		&C_GenerateKey,
		&C_GenerateKeyPair,
		&C_WrapKey,
		&C_UnwrapKey,
		&C_DeriveKey,
		&C_SeedRandom,
		&C_GenerateRandom,

		/* Management */
		&C_GetFunctionStatus,
		&C_CancelFunction,
};

CK_DEFINE_FUNCTION(CK_RV, C_Initialize)(
		CK_VOID_PTR pInitArgs){
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if (res != CKR_CRYPTOKI_NOT_INITIALIZED) {
		return CKR_CRYPTOKI_ALREADY_INITIALIZED;
	}

	/* If not already initialized, demand entropy */
	CK_BYTE_PTR entropy[32];
	printf("Please provide entropy to initialize the DRBG\n> ");

	fgets(entropy, 32);
	InitArgs args;
	args.entropy = &entropy;

	res = call_hypervisor(CMD_INITIALIZE, (uint32_t) &args, 0, 0);
	if (res == CKR_OK) {
		printf("SUCCESS: Token initialized\n");
		return res;
	}
	else
	{
		printf("Initialize failed. Abort.\n");
		return CKR_CANCEL;
	}
}

CK_DEFINE_FUNCTION(CK_RV, C_Finalize)(
		CK_VOID_PTR pReserved) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	res = call_hypervisor(CMD_FINALIZE, 0, 0, 0);
	if (res != RV_SUCCESS)
	{
		printf("Finalize failed. Abort.\n");
		return CKR_FUNCTION_FAILED;
	}
	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetInfo)(
		CK_INFO_PTR pInfo){
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (pInfo == NULL)
		return CKR_ARGUMENTS_BAD;
	pInfo->cryptokiVersion.major = 0x02;
	pInfo->cryptokiVersion.minor = 0x40;
	memset(pInfo->manufacturerID, ' ', sizeof(pInfo->manufacturerID));
	pInfo->flags = 0;
	pInfo->libraryVersion.major = PKCS11_CK_INFO_LIBRARY_VERSION_MAJOR;
	pInfo->libraryVersion.minor = PKCS11_CK_INFO_LIBRARY_VERSION_MINOR;

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetFunctionList)(
		CK_FUNCTION_LIST_PTR_PTR ppFunctionList) {
	if (ppFunctionList == NULL)
		return CKR_ARGUMENTS_BAD;

	*ppFunctionList = &function_list;
	return CKR_OK;
}

/* Slot and token Management:
 * Not very interesting, since we don't support multiple slots and tokens
 */

CK_DEFINE_FUNCTION(CK_RV, C_GetSlotList)(
		CK_BBOOL tokenPresent,
		CK_SLOT_ID_PTR pSlotList,
		CK_ULONG_PTR pulCount) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	IGNORE(tokenPresent);
	if (pulCount == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pSlotList == NULL)
	{
		*pulCount = 1;
	}
	else
	{
		if (*pulCount == 0)
			return CKR_BUFFER_TOO_SMALL;
		pSlotList[0] = PKCS11_CK_SLOT_ID;
		*pulCount = 1;
	}
	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetSlotInfo)(
		CK_SLOT_ID slotID,
		CK_SLOT_INFO_PTR pInfo) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (pInfo == NULL)
		return CKR_ARGUMENTS_BAD;

	memset(pInfo->slotDescription, ' ', sizeof(pInfo->slotDescription));
	memcpy(pInfo->slotDescription, PKCS11_CK_SLOT_INFO_DESCRIPTION, strlen(PKCS11_CK_SLOT_INFO_DESCRIPTION));
	memset(pInfo->manufacturerID, ' ', sizeof(pInfo->manufacturerID));
	memcpy(pInfo->manufacturerID, PKCS11_CK_SLOT_INFO_MANUFACTURER_ID, strlen(PKCS11_CK_SLOT_INFO_MANUFACTURER_ID));
	pInfo->flags = CKF_TOKEN_PRESENT;
	pInfo->hardwareVersion.major = 0x00;
	pInfo->hardwareVersion.minor = 0x01;
	pInfo->firmwareVersion.major = 0x00;
	pInfo->firmwareVersion.minor = 0x01;

	return CKR_OK;
}



CK_DEFINE_FUNCTION(CK_RV, C_GetTokenInfo)(
		CK_SLOT_ID slotID,
		CK_TOKEN_INFO_PTR  pInfo) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (pInfo == NULL)
		return CKR_ARGUMENTS_BAD;

	memset(pInfo->label, ' ', sizeof(pInfo->label));
	memcpy(pInfo->label, PKCS11_CK_TOKEN_INFO_LABEL, strlen(PKCS11_CK_TOKEN_INFO_LABEL));
	memset(pInfo->manufacturerID, ' ', sizeof(pInfo->manufacturerID));
	memcpy(pInfo->manufacturerID, PKCS11_CK_TOKEN_INFO_MANUFACTURER_ID, strlen(PKCS11_CK_TOKEN_INFO_MANUFACTURER_ID));
	memset(pInfo->model, ' ', sizeof(pInfo->model));
	memcpy(pInfo->model, PKCS11_CK_TOKEN_INFO_MODEL, strlen(PKCS11_CK_TOKEN_INFO_MODEL));
	memset(pInfo->serialNumber, ' ', sizeof(pInfo->serialNumber));
	memcpy(pInfo->serialNumber, PKCS11_CK_TOKEN_INFO_SERIAL_NUMBER, strlen(PKCS11_CK_TOKEN_INFO_SERIAL_NUMBER));


	// TODO: add missing flags!
	pInfo->flags = CKF_RNG | CKF_LOGIN_REQUIRED | CKF_USER_PIN_INITIALIZED | CKF_TOKEN_INITIALIZED;
	// TODO: we could give the application this information, but doesnt matter actually
	pInfo->ulMaxSessionCount = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulSessionCount = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulMaxRwSessionCount = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulRwSessionCount = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulTotalPublicMemory = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulFreePublicMemory = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulFreePrivateMemory = CK_UNAVAILABLE_INFORMATION;
	pInfo->ulTotalPrivateMemory = CK_UNAVAILABLE_INFORMATION;

	pInfo->ulMaxPinLen = PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN;
	pInfo->ulMinPinLen = PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN;
	pInfo->hardwareVersion.major = 0x00;
	pInfo->hardwareVersion.minor = 0x01;
	pInfo->firmwareVersion.major = 0x00;
	pInfo->firmwareVersion.minor = 0x01;
	memset(pInfo->utcTime, ' ', sizeof(pInfo->utcTime));

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetMechanismList)(
		CK_SLOT_ID slotID,
		CK_MECHANISM_TYPE_PTR pMechanismList,
		CK_ULONG_PTR pulCount) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_ALREADY_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (pulCount == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pMechanismList == NULL)
	{
		*pulCount = 1;
	}
	else
	{
		// TODO: Additional mechanism?
		if (1 > *pulCount)
			return CKR_BUFFER_TOO_SMALL;
		pMechanismList[0] = CKM_AES_CTR;
		*pulCount = 1;
	}

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetMechanismInfo)(
		CK_SLOT_ID slotID,
		CK_MECHANISM_TYPE type,
		CK_MECHANISM_INFO_PTR pInfo) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (pInfo == NULL)
		return CKR_ARGUMENTS_BAD;
	switch(type)
	{
		case CKM_AES_CTR:
			pInfo->ulMaxKeySize = 128;
			pInfo->ulMinKeySize = 128;
			pInfo->flags = CKF_ENCRYPT | CKF_DECRYPT | CKF_WRAP | CKF_UNWRAP;
			break;
		default:
			return CKR_MECHANISM_INVALID;
	}

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_InitToken)(
		CK_SLOT_ID slotID,
		CK_UTF8CHAR_PTR pPin,
		CK_ULONG ulPinLen,
		CK_UTF8CHAR_PTR pLabel) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if (res != CKR_OK)
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (pPin == NULL)
		return CKR_ARGUMENTS_BAD;
	if ((ulPinLen < PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN) || (ulPinLen > PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN))
		return CKR_PIN_LEN_RANGE;
	if (pLabel == NULL)
		return CKR_ARGUMENTS_BAD;

	if (token_initialized == CK_FALSE) {
		memcpy(soPin, pPin, ulPinLen);
	} else {
		res = memcmp(soPin, pPin, ulPinLen);
		if (res == 0) {
			memcpy(soPin, pPin, ulPinLen);
		} else {
			return CKR_PIN_INVALID;
		}
	}
	token_initialized = CK_TRUE;


	if (session_open == CK_TRUE)
		return CKR_SESSION_EXISTS;



	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_InitPIN)(
		CK_SESSION_HANDLE hSession,
		CK_UTF8CHAR_PTR pPin,
		CK_ULONG ulPinLen) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (pPin == NULL)
		return CKR_ARGUMENTS_BAD;
	if ((ulPinLen < PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN) || (ulPinLen > PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN))
		return CKR_PIN_LEN_RANGE;
	if(session_state != CKS_RW_SO_FUNCTIONS) {
		//printf("Session state: %x\n", session_state);
		return CKR_SESSION_READ_ONLY;
	}
	memcpy(usrPin, pPin, 4);
	return CKR_OK;
}

/* not really interesting since we accept any PIN anyway */
CK_DEFINE_FUNCTION(CK_RV, C_SetPIN)(
		CK_SESSION_HANDLE hSession,
		CK_UTF8CHAR_PTR pOldPin,
		CK_ULONG ulOldLen,
		CK_UTF8CHAR_PTR pNewPin,
		CK_ULONG ulNewLen) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;

	if ((pOldPin == NULL) || (pNewPin == NULL))
		return CKR_ARGUMENTS_BAD;
	if ((ulOldLen < PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN) || (ulOldLen > PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN))
		return CKR_PIN_LEN_RANGE;
	if ((ulNewLen < PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN) || (ulNewLen > PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN))
		return CKR_PIN_LEN_RANGE;
	if ((session_state == CKS_RO_PUBLIC_SESSION) || (session_state == CKS_RO_USER_FUNCTIONS))
		return CKR_SESSION_READ_ONLY;

	res = memcmp(usrPin, pOldPin, ulOldLen);
	if (res != 0)
		return CKR_PIN_INVALID;
	memcpy(usrPin, pNewPin, ulNewLen);


	return CKR_OK;
}


/* Session management functions:
 *
 * Not too interesting, allow basically everything
 */
CK_DEFINE_FUNCTION(CK_RV, C_OpenSession)(
		CK_SLOT_ID slotID,
		CK_FLAGS flags,
		CK_VOID_PTR pApplication,
		CK_NOTIFY Notify,
		CK_SESSION_HANDLE_PTR phSession) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	// We only allow exactly one Session
	if (session_open == CK_TRUE)
		return CKR_SESSION_COUNT;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	if (!(flags & CKF_SERIAL_SESSION))
		return CKR_SESSION_PARALLEL_NOT_SUPPORTED;

	if (phSession == NULL)
		return CKR_ARGUMENTS_BAD;

	session_open = CK_TRUE;

	if (flags & CKF_RW_SESSION) {
		session_state = CKS_RW_PUBLIC_SESSION;
	} else {
		session_state = CKS_RO_PUBLIC_SESSION;
	}

	*phSession = PKCS11_CK_SESSION_ID;


	return CKR_OK;
}

/* since we don't have different sessions, the next functions are somehow meaningless
 * we can just pretend to support this
 */

CK_DEFINE_FUNCTION(CK_RV, C_CloseSession)(
		CK_SESSION_HANDLE hSession) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_TRUE)
		return CKR_SESSION_HANDLE_INVALID;
	res = call_hypervisor(CMD_DESTROY_EVERYTHING, 0, 0, 0);
	if (res != RV_SUCCESS)
		return CKR_GENERAL_ERROR;
	session_open = CK_FALSE;
	session_state = CKS_RO_PUBLIC_SESSION;

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_CloseAllSessions)(
		CK_SLOT_ID slotID){
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (slotID != PKCS11_CK_SLOT_ID)
		return CKR_SLOT_ID_INVALID;
	res = call_hypervisor(CMD_DESTROY_EVERYTHING, 0, 0, 0);
	if (res != RV_SUCCESS)
		return CKR_GENERAL_ERROR;
	session_open = CK_FALSE;
	session_state = CKS_RO_PUBLIC_SESSION;

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GetSessionInfo)(
		CK_SESSION_HANDLE hSession,
		CK_SESSION_INFO_PTR pInfo) {
	uint32_t res;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (pInfo == NULL)
		return CKR_ARGUMENTS_BAD;
	pInfo->state = session_state;
	pInfo->slotID = PKCS11_CK_SLOT_ID;
	pInfo->ulDeviceError = 0;

	if ((session_state != CKS_RO_USER_FUNCTIONS) || (session_state != CKS_RO_PUBLIC_SESSION)) {
		pInfo->flags = CKF_SERIAL_SESSION | CKF_RW_SESSION;
	} else {
		pInfo->flags = CKF_SERIAL_SESSION;
	}

	return CKR_OK;
}

/* We don't support exporting the state of cryptographic
 * functions, that's not how it works
 */
CK_DEFINE_FUNCTION(CK_RV, C_GetOperationState)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pOperationState,
		CK_ULONG_PTR pulOperationStateLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

/* It's potentially evil to be able to restore the State from other
 * Sessions / Tokens!
 */
CK_DEFINE_FUNCTION(CK_RV, C_SetOperationState)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pOperationState,
		CK_ULONG ulOperationStateLen,
		CK_OBJECT_HANDLE hEncryptionKey,
		CK_OBJECT_HANDLE hAuthenticationKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

/* We basically accept any PIN that has the correct format.
 * PINs generally don't add security, since any attacker
 * compromising the host application will be able
 * to sniff the PIN anyhow.
 */
CK_DEFINE_FUNCTION(CK_RV, C_Login)(
		CK_SESSION_HANDLE hSession,
		CK_USER_TYPE userType,
		CK_UTF8CHAR_PTR pPin,
		CK_ULONG ulPinLen) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;

	if (pPin == NULL)
		return CKR_ARGUMENTS_BAD;

	if (ulPinLen < PKCS11_CK_TOKEN_INFO_MIN_PIN_LEN)
		return CKR_PIN_LEN_RANGE;
	if (ulPinLen > PKCS11_CK_TOKEN_INFO_MAX_PIN_LEN)
		return CKR_PIN_LEN_RANGE;

	if ((userType != CKU_SO) && (userType != CKU_USER))
		return CKR_USER_TYPE_INVALID;

	switch(session_state) {
	case CKS_RO_PUBLIC_SESSION:
		if (userType == CKU_SO) {
			return CKR_SESSION_READ_ONLY_EXISTS;
		} else {
			res = memcmp(usrPin, pPin, ulPinLen);
			if (res != 0)
				return CKR_PIN_INCORRECT;
			session_state = CKS_RO_USER_FUNCTIONS;
			break;
		}
	case CKS_RO_USER_FUNCTIONS:
	case CKS_RW_USER_FUNCTIONS:
		if (userType == CKU_SO) {
			return CKR_USER_ANOTHER_ALREADY_LOGGED_IN;
		} else {
			return CKR_USER_ALREADY_LOGGED_IN;
		}
	case CKS_RW_PUBLIC_SESSION:
		if (userType == CKU_SO) {
			res = memcmp(soPin, pPin, ulPinLen);
			if (res != 0)
				return CKR_PIN_INCORRECT;
			session_state = CKS_RW_SO_FUNCTIONS;
			break;
		} else {
			res = memcmp(usrPin, pPin, ulPinLen);
			if (res != 0)
				return CKR_PIN_INCORRECT;
			session_state = CKS_RW_USER_FUNCTIONS;
			break;
		}
	case CKS_RW_SO_FUNCTIONS:
		if (userType == CKU_SO) {
			return CKR_USER_ALREADY_LOGGED_IN;
		} else {
			return CKR_USER_ANOTHER_ALREADY_LOGGED_IN;
		}
	}

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_Logout)(
		CK_SESSION_HANDLE hSession) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;


	switch(session_state) {

	case CKS_RO_USER_FUNCTIONS:
		session_state = CKS_RO_PUBLIC_SESSION;
		break;
	case CKS_RW_SO_FUNCTIONS:
	case CKS_RW_USER_FUNCTIONS:
		session_state = CKS_RW_PUBLIC_SESSION;
		break;
	default:
		return CKR_USER_NOT_LOGGED_IN;

	}
	return CKR_OK;
}

/* Object management functions */


// potentially forbidden by policy
CK_DEFINE_FUNCTION(CK_RV, C_CreateObject)(
		CK_SESSION_HANDLE hSession,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulCount,
		CK_OBJECT_HANDLE_PTR phObject) {
	return CKR_FUNCTION_NOT_SUPPORTED;

}

// potentially forbidden by policy
CK_DEFINE_FUNCTION(CK_RV, C_CopyObject)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hObject,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulCount,
		CK_OBJECT_HANDLE_PTR phNewObject) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

/* Symbolic Models don't consider destruction of Object
 * But could considered useful at some point
 */
CK_DEFINE_FUNCTION(CK_RV, C_DestroyObject)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hObject) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

/* We only support Key Object, so size is always size AES_BLOCKLEN */
CK_DEFINE_FUNCTION(CK_RV, C_GetObjectSize)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hObject,
		CK_ULONG_PTR pulSize) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (pulSize == NULL)
		return CKR_ARGUMENTS_BAD;
	*pulSize = 16;
	return CKR_OK;
}

/*
 *	 Welp, this is complicated
 */
CK_DEFINE_FUNCTION(CK_RV, C_GetAttributeValue)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hObject,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulCount) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

// This is strictly forbidden by our policy
CK_DEFINE_FUNCTION(CK_RV, C_SetAttributeValue)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hObject,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulCount) {
	uint32_t res;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	return CKR_ACTION_PROHIBITED;
}

/*
 * Not really useful, but could be implemented later on
 */
CK_DEFINE_FUNCTION(CK_RV, C_FindObjectsInit)(
		CK_SESSION_HANDLE hSession,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulCount) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


CK_DEFINE_FUNCTION(CK_RV, C_FindObjects)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE_PTR phObject,
		CK_ULONG ulMaxObjectCount,
		CK_ULONG_PTR pulObjectCount) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_FindObjectsFinal)(CK_SESSION_HANDLE hSession) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


CK_DEFINE_FUNCTION(CK_RV, C_EncryptInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	uint32_t res;
	CryptInitArgs args;
	CK_AES_CTR_PARAMS_PTR pCtrParams;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (pMechanism == NULL)
		return CKR_ARGUMENTS_BAD;
	if(hKey <= 0)
		return CKR_KEY_HANDLE_INVALID;
#ifdef PKCS_DEBUG
	printf("Lib pParameter  : %x\n", pMechanism->pParameter);
#endif
	if (pMechanism->pParameter == NULL) {
		return CKR_MECHANISM_PARAM_INVALID;
	}
	/* We only support CKM_AES_CTR */
	if (pMechanism->mechanism != CKM_AES_CTR)
		return CKR_MECHANISM_INVALID;
	if (pMechanism->pParameter == NULL) {
		return CKR_MECHANISM_PARAM_INVALID;
	}
	pCtrParams = (CK_AES_CTR_PARAMS_PTR) pMechanism->pParameter;
	if ((pCtrParams->ulCounterBits <= 0) || (pCtrParams->ulCounterBits > 128)) { // TODO: really 128???
#ifdef PKCS_DEBUG
		printf("CounterBits: %x\n", pCtrParams->ulCounterBits);
#endif
		return CKR_MECHANISM_PARAM_INVALID;

	}


	args.hKey = hKey;
	memcpy(args.cb, pCtrParams->cb, 16);
#ifdef PKCS_DEBUG
	printf("Library IV: \n");
	print_hex(pCtrParams->cb, 16);
	printf("Counter Bits %d\n", pCtrParams->ulCounterBits);
#endif
	res = call_hypervisor(CMD_ENCRYPT_INIT, (void*) &args, 0, 0);
	return res;
}


CK_DEFINE_FUNCTION(CK_RV, C_Encrypt)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pData,
		CK_ULONG ulDataLen,
		CK_BYTE_PTR pEncryptedData,
		CK_ULONG_PTR pulEncryptedDataLen) {
	uint32_t res;
	EncryptArgs args;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (res != RV_SUCCESS)
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (pData == NULL)
		return CKR_ARGUMENTS_BAD;
	if (ulDataLen <= 0)
		return CKR_ARGUMENTS_BAD;
	if (pEncryptedData  == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pulEncryptedDataLen == NULL)
		return CKR_ARGUMENTS_BAD;


	args.pData = pData;
	args.ulDataLen = ulDataLen;
	args.pEncryptedData = pEncryptedData;
	args.pulEncryptedDataLen = pulEncryptedDataLen;
#ifdef PKCS_DEBUG
	printf("Dump EncryptArgs Library: \n");
	printf("pData: %x\n", args.pData);
	printf("ulDataLen: %x\n", &args.ulDataLen);
	printf("pEncryptedData: %x\n", args.pEncryptedData);
	printf("pulEncryptedDataLen: %x\n", args.pulEncryptedDataLen);
	printf("Args: %x\n", &args);
	printf("Dump done\n");
#endif
	res = call_hypervisor(CMD_ENCRYPT, &args, 0, 0);
	if (res != RV_SUCCESS)
		return res;

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_EncryptUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG_PTR pulEncryptedPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_EncryptFinal)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pLastEncryptedPart,
		CK_ULONG_PTR pulLastEncryptedPartLen){
	return CKR_FUNCTION_NOT_SUPPORTED;
}



CK_DEFINE_FUNCTION(CK_RV, C_DecryptInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	uint32_t res;
	CryptInitArgs  args;
	CK_AES_CTR_PARAMS_PTR pCtrParams;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (pMechanism == NULL)
		return CKR_ARGUMENTS_BAD;
	if (hKey <= 0)
		return CKR_KEY_HANDLE_INVALID;

	/* We only support AES_CTR */
	if (pMechanism->mechanism != CKM_AES_CTR)
		return CKR_MECHANISM_INVALID;
	if (pMechanism->pParameter == NULL)
		return CKR_MECHANISM_PARAM_INVALID;
	if (pMechanism->ulParameterLen <= 0)
		return CKR_MECHANISM_INVALID;
	pCtrParams = (CK_AES_CTR_PARAMS_PTR) pMechanism->pParameter;
	if ((pCtrParams->ulCounterBits <= 0) || (pCtrParams->ulCounterBits > 128)) { // TODO: really 128???
		//printf("CounterBits: %x\n", pCtrParams->ulCounterBits);
		return CKR_MECHANISM_PARAM_INVALID;

	}



	args.hKey = hKey;
	memcpy(args.cb, pCtrParams->cb, 16);

	res = call_hypervisor(CMD_DECRYPT_INIT, (void*) &args, 0, 0);

	if (res != RV_SUCCESS)
		return CKR_FUNCTION_FAILED;

	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_Decrypt)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pEncryptedData,
		CK_ULONG ulEncryptedDataLen,
		CK_BYTE_PTR pData,
		CK_ULONG_PTR pulDataLen) {
	uint32_t res;
	DecryptArgs args;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	if (pEncryptedData == NULL)
		return CKR_ARGUMENTS_BAD;
	if (ulEncryptedDataLen <= 0)
		return CKR_ARGUMENTS_BAD;
	if (pData == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pulDataLen == NULL)
		return CKR_ARGUMENTS_BAD;



	args.pData = pData;
	args.pulDataLen = pulDataLen;
	args.pEncryptedData = pEncryptedData;
	args.ulEncryptedDataLen = ulEncryptedDataLen;

	res = call_hypervisor(CMD_DECRYPT, &args, 0, 0);

	if (res != RV_SUCCESS)
		return CKR_FUNCTION_FAILED;
	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_DecryptUpdate) (
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG ulEncryptedPartLen,
		CK_BYTE_PTR pPart,
		CK_ULONG_PTR pulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_DecryptFinal) (
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pLastPart,
		CK_ULONG_PTR pulLastPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


/* Message digesting not supported at all */
CK_DEFINE_FUNCTION(CK_RV , C_DigestInit) (
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_Digest) (
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pData,
		CK_ULONG ulDataLen,
		CK_BYTE_PTR pDigest,
		CK_ULONG_PTR pulDigestLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_DigestUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


CK_DEFINE_FUNCTION(CK_RV, C_DigestKey)(
		CK_SESSION_HANDLE hSession,
		CK_OBJECT_HANDLE hKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_DigestFinal)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pDigest,
		CK_ULONG_PTR pulDigestLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


/* Signing and MACing also not supported... */

CK_DEFINE_FUNCTION(CK_RV, C_SignInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_Sign)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pData,
		CK_ULONG ulDataLen,
		CK_BYTE_PTR pSignature,
		CK_ULONG_PTR pulSignatureLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_SignUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_SignFinal)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pSignature,
		CK_ULONG_PTR pulSignatureLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_SignRecoverInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_SignRecover)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pData,
		CK_ULONG ulDataLen,
		CK_BYTE_PTR pSignature,
		CK_ULONG_PTR pulSignatureLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_VerifyInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_Verify)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pData,
		CK_ULONG ulDataLen,
		CK_BYTE_PTR pSignature,
		CK_ULONG ulSignatureLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_VerifyUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_VerifyFinal)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pSignature,
		CK_ULONG ulSignatureLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_VerifyRecoverInit)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_VerifyRecover)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pSignature,
		CK_ULONG ulSignatureLen,
		CK_BYTE_PTR pData,
		CK_ULONG_PTR pulDataLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


/* Dual-function cryptographic functions also not supported */
CK_DEFINE_FUNCTION(CK_RV, C_DigestEncryptUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG_PTR pulEncryptedPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_DecryptDigestUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG ulEncryptedPartLen,
		CK_BYTE_PTR pPart,
		CK_ULONG_PTR pulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


CK_DEFINE_FUNCTION(CK_RV, C_SignEncryptUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pPart,
		CK_ULONG ulPartLen,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG_PTR pulEncryptedPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_DecryptVerifyUpdate)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pEncryptedPart,
		CK_ULONG ulEncryptedPartLen,
		CK_BYTE_PTR pPart,
		CK_ULONG_PTR pulPartLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}


/* Key Management functions */
CK_DEFINE_FUNCTION(CK_RV, C_GenerateKey)(CK_SESSION_HANDLE hSession, CK_MECHANISM_PTR pMechanism, CK_ATTRIBUTE_PTR pTemplate, CK_ULONG ulCount, CK_OBJECT_HANDLE_PTR phKey) {
	uint32_t res, handle, template;
	GenerateKeyArgs args;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;

	if (pMechanism == NULL) {
		printf("pMechanism null\n");
		return CKR_ARGUMENTS_BAD;
	}
	if (pTemplate == NULL) {
		printf("pTemplate null\n");
		return CKR_ARGUMENTS_BAD;
	}
	if (phKey == NULL) {
		printf("phKey null\n");
		return CKR_ARGUMENTS_BAD;
	}

	template = parse_template(pTemplate, ulCount, 4);
	if (template == PKCS11_INVALID_TEMPLATE) {
		printf("Template failure %d\n", template);
		return CKR_ATTRIBUTE_VALUE_INVALID;
	}

	/* Only SO can create trusted keys */
	if (template == PKCS11_TRUSTED_TEMPLATE) {
		if (session_state != CKS_RW_SO_FUNCTIONS) {
			return CKR_ATTRIBUTE_VALUE_INVALID;
		}
	}


	args.handle_ptr = phKey;
#ifdef PKCS_DEBUG
	printf("PHKey Addr: %x\n", phKey);
	printf("Hande_ptr addr: %x\n", args.handle_ptr);
#endif
	args.template = template;
	res = call_hypervisor(CMD_GENERATE_KEY, (void*) &args, template, 0);
	if(res  != CKR_OK) {
		return res;
	}
	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_GenerateKeyPair)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_ATTRIBUTE_PTR pPublicKeyTemplate,
		CK_ULONG ulPublicKeyAttributeCount,
		CK_ATTRIBUTE_PTR pPrivateKeyTemplate,
		CK_ULONG ulPrivateKeyAttributeCount,
		CK_OBJECT_HANDLE_PTR phPublicKey,
		CK_OBJECT_HANDLE_PTR phPrivateKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_WrapKey)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hWrappingKey,
		CK_OBJECT_HANDLE hKey,
		CK_BYTE_PTR pWrappedKey,
		CK_ULONG_PTR pulWrappedKeyLen) {

	uint32_t res;
	WrapKeyArgs args;
	CK_AES_CTR_PARAMS_PTR pCtrParams;

	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (pMechanism == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pMechanism->mechanism != CKM_AES_CTR)
		return CKR_MECHANISM_INVALID;
	if ((pMechanism->pParameter == NULL)  || (pMechanism->ulParameterLen == 0)) {
		return CKR_MECHANISM_PARAM_INVALID;
	}

	pCtrParams = (CK_AES_CTR_PARAMS_PTR) pMechanism->pParameter;
	if ((pCtrParams->ulCounterBits <= 0) || (pCtrParams->ulCounterBits > 128)) { // TODO: really 128???
#ifdef PKCS_DEBUG
		printf("CounterBits   : %x\n", pCtrParams->ulCounterBits);
#endif
		return CKR_MECHANISM_PARAM_INVALID;
	}

	args.hKey = hKey;
	args.hWrappingKey = hWrappingKey;
	//printf("Lib wrapping handle: %x\n", hWrappingKey);
	args.pWrappedKey = pWrappedKey;
	args.pulWrappedKeyLen = pulWrappedKeyLen;
	memcpy(args.cb, pCtrParams->cb, 16);
	res = call_hypervisor(CMD_WRAP_KEY, (void*) &args, 0, 0);

	if (res == RV_SUCCESS) {
		*pulWrappedKeyLen = 16;
		return CKR_OK;
	}
	else {
		//printf("Lib wrap return : %x\n", res);
		return res;
	}
}


CK_DEFINE_FUNCTION(CK_RV, C_UnwrapKey)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hUnwrappingKey,
		CK_BYTE_PTR pWrappedKey,
		CK_ULONG ulWrappedKeyLen,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulAttributeCount,
		CK_OBJECT_HANDLE_PTR phKey) {

	uint32_t res, template;
	UnwrapKeyArgs args;
	CK_AES_CTR_PARAMS_PTR pCtrParams;

	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	if (pMechanism == NULL)
		return CKR_ARGUMENTS_BAD;
	if (pMechanism->mechanism != CKM_AES_CTR)
		return CKR_MECHANISM_INVALID;
	if ((pMechanism->pParameter == NULL) || (pMechanism->ulParameterLen == 0))
		return CKR_MECHANISM_PARAM_INVALID;
	if ((pWrappedKey == NULL) || (ulWrappedKeyLen != 16))
		return CKR_ARGUMENTS_BAD;
	if ((pTemplate == NULL) || (ulAttributeCount <= 0))
		return CKR_ARGUMENTS_BAD;
	if (phKey == NULL)
		return CKR_ARGUMENTS_BAD;
	template = parse_template(pTemplate, ulAttributeCount, 4);
	if (template == PKCS11_INVALID_TEMPLATE)
		return CKR_GENERAL_ERROR;

	pCtrParams = (CK_AES_CTR_PARAMS_PTR) pMechanism->pParameter;
	if ((pCtrParams->ulCounterBits <= 0) || (pCtrParams->ulCounterBits > 128)) {
#ifdef PKCS_DEBUG
		printf("CounterBits: %x\n", pCtrParams->ulCounterBits);
#endif
		return CKR_MECHANISM_PARAM_INVALID;
	}


	args.hUnwrappingKey = hUnwrappingKey;
	args.pWrappedKey = pWrappedKey;
	args.phKey = phKey;
	args.template = template;
	args.ulWrappedKeyLen = ulWrappedKeyLen;
	memcpy(args.cb, pCtrParams->cb, 16);

	res = call_hypervisor(CMD_UNWRAP_KEY, (void*) &args, 0, 0);
	if (res != RV_SUCCESS) {
		return res;
	}
	return CKR_OK;
}

CK_DEFINE_FUNCTION(CK_RV, C_DeriveKey)(
		CK_SESSION_HANDLE hSession,
		CK_MECHANISM_PTR pMechanism,
		CK_OBJECT_HANDLE hBaseKey,
		CK_ATTRIBUTE_PTR pTemplate,
		CK_ULONG ulAttributeCount,
		CK_OBJECT_HANDLE_PTR phKey) {
	return CKR_FUNCTION_NOT_SUPPORTED;
}

/* Random Number Generation functions: Not sure if we want to support them */
CK_DEFINE_FUNCTION(CK_RV, C_SeedRandom)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pSeed,
		CK_ULONG ulSeedLen){
	return CKR_RANDOM_SEED_NOT_SUPPORTED;
}

CK_DEFINE_FUNCTION(CK_RV, C_GenerateRandom)(
		CK_SESSION_HANDLE hSession,
		CK_BYTE_PTR pRandomData,
		CK_ULONG ulRandomLen) {
	return CKR_FUNCTION_NOT_SUPPORTED;

}

/* Parallel function management functions  */
CK_DEFINE_FUNCTION(CK_RV, C_GetFunctionStatus)(
		CK_SESSION_HANDLE hSession) {
	uint32_t res;

	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;
	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	return CKR_FUNCTION_NOT_PARALLEL;
}

CK_DEFINE_FUNCTION(CK_RV, C_CancelFunction)(
		CK_SESSION_HANDLE hSession) {
	uint32_t res;

	if (hSession != PKCS11_CK_SESSION_ID)
		return CKR_SESSION_HANDLE_INVALID;
	if (session_open == CK_FALSE)
		return CKR_SESSION_HANDLE_INVALID;

	res = call_hypervisor(CMD_IS_INITIALIZED, 0, 0, 0);
	if ((res != CKR_OK) || (token_initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	return CKR_FUNCTION_NOT_PARALLEL;
}
