#include "hyper.h"
#include "hw.h"
#include "guest_blob.h"

#include "pkcs11/pkcs11_token.h"



extern virtual_machine *curr_vm;



/* The handle that is called upon a PKCS11 Hypercall */
int pkcs11_handler(unsigned long cmd, void *params)
{

	// Only Accept Arguments within the Guest VM
	uint32_t guest_address_start = curr_vm->config->firmware->vstart;
	uint32_t guest_address_end   = guest_address_start + curr_vm->config->firmware->psize;


	switch(cmd) {

	case CMD_INITIALIZE:
	{
		InitArgs* initParams = (InitArgs*) params;
//		printf("%x\n", initParams);
		if( (uint32_t) initParams->entropy < guest_address_start
				|| (uint32_t) initParams->entropy > guest_address_end) {
			printf("hallo %x\n", (uint32_t) initParams->entropy);
			return RV_FAILURE;
		}
		return PKCS11_initialize(initParams);
	}

	case CMD_IS_INITIALIZED:
		return PKCS11_is_initialized();

	case CMD_GENERATE_KEY:
	{
		GenerateKeyArgs * generateKeyParams = (GenerateKeyArgs*) params;
		if ((uint32_t) generateKeyParams->handle_ptr < guest_address_start
				|| (uint32_t) generateKeyParams->handle_ptr > guest_address_end) {
			return RV_FAILURE;
		}
		return PKCS11_generate_key(generateKeyParams);
	}

	case CMD_WRAP_KEY:
	{
		WrapKeyArgs* wrapKeyParams = (WrapKeyArgs*) params;
		if ((uint32_t) wrapKeyParams->pWrappedKey < guest_address_start
				|| (uint32_t) wrapKeyParams->pWrappedKey > guest_address_end
				|| (uint32_t) wrapKeyParams->pulWrappedKeyLen < guest_address_start
				|| (uint32_t) wrapKeyParams->pulWrappedKeyLen > guest_address_end) {
			return RV_FAILURE;
		}
		return PKCS11_wrap_key(wrapKeyParams);
	}

	case CMD_UNWRAP_KEY:
	{
		UnwrapKeyArgs * unwrapKeyParams = (UnwrapKeyArgs*) params;
		if((uint32_t) unwrapKeyParams->pWrappedKey < guest_address_start
			|| (uint32_t) unwrapKeyParams->pWrappedKey > guest_address_end
			|| (uint32_t) unwrapKeyParams->phKey < guest_address_start
			|| (uint32_t) unwrapKeyParams->phKey > guest_address_end) {
			return RV_FAILURE;
		}

		return PKCS11_unwrap_key(unwrapKeyParams);
	}

	case CMD_ENCRYPT:
	{

		EncryptArgs* encryptParams = (EncryptArgs*) params;
/*
		printf("Dump EncryptArgs HV: \n");
		printf("pData: %x\n", encryptParams->pData);
		printf("ulDataLen: %x\n", &encryptParams->ulDataLen);
		printf("pEncryptedData: %x\n", encryptParams->pEncryptedData);
		printf("pulEncryptedDataLen: %x\n", encryptParams->pulEncryptedDataLen);
		printf("encryptParams: %x\n", encryptParams);

		printf("Dump done\n");
*/

		if ((uint32_t) encryptParams->pData < guest_address_start
			|| (uint32_t) encryptParams->pData > guest_address_end
			|| (uint32_t) encryptParams->pEncryptedData < guest_address_start
			|| (uint32_t) encryptParams->pEncryptedData > guest_address_end
			|| (uint32_t) encryptParams->pulEncryptedDataLen < guest_address_start
			|| (uint32_t) encryptParams->pulEncryptedDataLen > guest_address_end) {
			printf("Arguments horribly wrong!\n");
			printf("%x\n", encryptParams->pData);
			printf("Hypervisor Password: ");
			print_hex(encryptParams->pData, 16);
			printf("%x\n", encryptParams->pEncryptedData);
			return RV_FAILURE;
		}
		return PKCS11_encrypt(encryptParams);
	}

	case CMD_ENCRYPT_INIT:
	{

		CryptInitArgs * cryptInitParams = (CryptInitArgs*) params;
		if ((uint32_t) &(cryptInitParams->cb) < guest_address_start
				|| (uint32_t) &(cryptInitParams->cb) > guest_address_end) {
			return RV_FAILURE;
		}
		return PKCS11_encrypt_init(cryptInitParams);
	}
	case CMD_DECRYPT:
	{
		DecryptArgs* decryptParams = (DecryptArgs*) params;
		if ((uint32_t) decryptParams->pData < guest_address_start
			|| (uint32_t) decryptParams->pData > guest_address_end
			|| (uint32_t) decryptParams->pEncryptedData < guest_address_start
			|| (uint32_t) decryptParams->pEncryptedData > guest_address_end
			|| (uint32_t) decryptParams->pulDataLen < guest_address_start
			|| (uint32_t) decryptParams->pulDataLen > guest_address_end) {
			printf("Arguments horribly wrong!\n");
			return RV_FAILURE;
		}
		return PKCS11_decrypt(decryptParams);
	}
	case CMD_DECRYPT_INIT:
	{
		CryptInitArgs * cryptInitParams = (CryptInitArgs*) params;
		if ((uint32_t) &(cryptInitParams->cb) < guest_address_start
				|| (uint32_t) &(cryptInitParams->cb) > guest_address_end) {
			return RV_FAILURE;
		}
		return PKCS11_decrypt_init(cryptInitParams);

	}
	case CMD_DESTROY_EVERYTHING:
	{
		return PKCS11_delete_objects();
	}
	case CMD_FINALIZE: // Cannot really uninitialize the token!
		return PKCS11_delete_objects();
	default:
		printf("Handler: %x, %x\n", (uint32_t) cmd, (uint32_t) params);
		return RV_FAILURE;
	}
}
