/*
 * This implements the Token
 * Private Functions: Debug and internal token Management
 * Public  Functions: Functions used by the hypercall handler
 */

#include "pkcs11_token.h"

#include "aes.h"

/* include crypto primitives */
#include "ctr_drbg.h"
#include "types.h"
#include "uclib.h"

//#define PKCS_DEBUG

static pkcs11_ctx p11_ctx;



/* ---------- private functions --------- */


/*
 * compare IVs
 * returns 1 if the IV provided by the user is greater than the
 * IV used in previous executions
 */
int cmp_iv(unsigned char * user_iv, unsigned char * last_iv) {
	int fresh = -1;
	int i;
	for (i = 0; i < 16; i++) {
		if (user_iv[i] > last_iv[i]) {
			fresh = 1;
		}
	}

	return fresh;
}


/* Increment function used in several Cryptoraphic Functions */
void increment_iv(unsigned char * iv) {
	int i;
	for (i = AES_BLOCKLEN -1; i >= 0; i--) {
		if(iv[i] == 255) {
			if(i == 0) {
				while(1); // halt!
			}
			iv[i] = 0;
			continue;
		}
		else {
			iv[i] +=1;
			break;
		}
	}
}




/* Print char string as hex string */
void print_hex(unsigned char *bytes, int count) {
	int i;
	for (i = 0; i < count; i++) {
		if ((i % BLOCKLENGTH == 0) && (i != 0))
			printf("\n");
		printf("%2", bytes[i]);
	}
	printf("\n");
	return;
}

/* Object Management functions.
 * The object storage is realized as linked list of pkcs11_objects
 */

/*
 * Print the contents of the list
 */
void print_list(pkcs11_ctx *p11_ctx) {
	int i;

	for (i = 0 ; i < p11_ctx->key_count; i++) {
		printf("----------------\n");
		printf("Handle: %lu\n", p11_ctx->object_storage[i].handle);
		printf("Template: %lu\n", p11_ctx->object_storage[i].template);
		printf("Value:");
		print_hex(p11_ctx->object_storage[i + 1].key, 16);
		printf("\n");
	}
}


/* insert object if space available
 * handle will be (previous handle) + 1 or 1 if array is empty
 * returns handle of newly created object
 */
int insert_object(pkcs11_ctx *p11_ctx, unsigned char* key, CK_ULONG template) {

	int handle = 0;

	if (p11_ctx->key_count == MAX_HANDLE) {
		return -(CKR_DEVICE_MEMORY);
	}

	handle = ++p11_ctx->key_count;
	memcpy(p11_ctx->object_storage[handle].key, key, BLOCKLEN);
	p11_ctx->object_storage[handle].template = template;
	p11_ctx->object_storage[handle].handle = handle;


	return handle;

}


/* returns pointer to object with given handle, NULL if such object doesn't exist */
pkcs11_object *find_object(pkcs11_ctx *p11_ctx, CK_OBJECT_HANDLE handle) {
	if ((handle > MAX_HANDLE) || (handle == 0)) {
	#ifdef PKCS_DEBUG
		printf("invalid handle: %d\n", handle);
	#endif
		return NULL;
	}
	return &(p11_ctx->object_storage[handle]);
}

/* removes all objects from storage
 * This happens on closed Session */
void erase_oject_storage(pkcs11_ctx *p11_ctx) {
	int i;

	for (i = 0; i < MAX_HANDLE + 1; i++) {
		memset(p11_ctx->object_storage[i].key, '0', BLOCKLEN);
	}
	p11_ctx->key_count = 0;
	p11_ctx->current_key = 0;

}


/* --------- Debug functions --------- 	*/
/* Should be removed later on 			*/


/*
 * Dump State of the deterministic random byte generator
 */
void dump_drbg_state(ctr_drbg_ctx * ctx) {
	printf("## DUMP DRBG ##\n");
	printf("Key:\n");
	print_hex(ctx->key, 16);
	printf("Counter:\n");
	print_hex(ctx->counter, 16);
	printf("###############\n");
	return;
}








/* Debug functions for testing Crypto Implementations */
void add_key(pkcs11_ctx * p11_ctx, CK_BYTE_PTR ckey, CK_OBJECT_HANDLE hKey) {
	int handle;
	handle = insert_object(p11_ctx, ckey, hKey);
}

void set_iv(pkcs11_ctx * p11_ctx, CK_BYTE_PTR iv) {
	memcpy(p11_ctx->iv, iv, AES_BLOCKLEN);
}



/*
 *  This functions get called by the Handler
 */

/*
 *
 */
CK_RV PKCS11_initialize( InitArgs *args) {
#ifdef PKCS_DEBUG
	printf("Init: %x, %x\n", p11_ctx, args);
#endif
	ctr_drbg_selftest();
	AES_CTR_selftest();

	unsigned char entropy[SEEDLEN];
	CK_RV rv;
	int res;

	if (p11_ctx.initialized == CK_TRUE) {
		return CKR_CRYPTOKI_ALREADY_INITIALIZED;
	}

	/* Initialize the token */

	p11_ctx.current_key = CK_INVALID_HANDLE;
	p11_ctx.key_count = 0;

	memset(p11_ctx.iv, 0, BLOCKLEN);


	/* Instantiate CTR DRBG */
#ifdef PKCS_DEBUG
	print_hex(args->entropy, 32);
#endif
	res = ctr_drbg_instantiate(p11_ctx.ctr_ctx, args->entropy);
	if (res != CTR_DRBG_SUCCESS) {
		rv = CKR_DEVICE_ERROR;
		return rv;
	}

	/* No encryption / decryption so far */
	p11_ctx.state = CRYPT_UNINITIALIZED;
	p11_ctx.initialized = CK_TRUE;
#ifdef PKCS_DEBUG
	dump_drbg_state(p11_ctx.ctr_ctx);
#endif
	return CKR_OK;
}


CK_RV PKCS11_is_initialized() {
	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE)) {
#ifdef PKCS_DEBUG
		printf("Cryptoki not initialized\n");
#endif
		return CKR_CRYPTOKI_NOT_INITIALIZED;
	}
	else
		return CKR_OK;
}

/* Generate a fresh Key */
CK_RV PKCS11_generate_key(GenerateKeyArgs *args) {
#ifdef PKCS_DEBUG
	printf("Generate Key\n");
#endif
	CK_ULONG handle;
	CK_RV rv;

	CK_BYTE key[BLOCKLEN];
	int res;

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;


	if ((args->template != TRUSTED_TEMPLATE)
			&& (args->template != USAGE_TEMPLATE)
			&& (args->template != UNTRUSTED_TEMPLATE)) {
#ifdef PKCS_DEBUG
		printf("template: %d\n", args->template);
#endif
		return CKR_GENERAL_ERROR;
	}

	res = ctr_drbg_generate(p11_ctx.ctr_ctx, key, BLOCKLEN);
	if (res != CTR_DRBG_SUCCESS) {
		rv = CKR_DEVICE_ERROR;
		return rv;
	}

	handle = insert_object(&p11_ctx, key, args->template);
	if (handle <= 0) { // Some error occured
		return CKR_DEVICE_MEMORY;
	}
	*(args->handle_ptr) = handle;
#ifdef PKCS_DEBUG
	printf("Addr: %x, handle: %x\n", (uint32_t) args->handle_ptr, *args->handle_ptr);
#endif
	return CKR_OK;
}


/*
 * Wrap key.
 * This is possible under the following conditions:
 * 1. Both keys exist
 * 2. Wrapping key is trusted key
 * 3. Wrapped key is usage key
 * 4. IV is fresh
 */
CK_RV PKCS11_wrap_key( WrapKeyArgs *args) {

	pkcs11_object *poWrappingKey, *poKey;
	CK_BYTE_PTR wrapping_key;
	CK_BYTE_PTR key;
	CK_RV rv;

	unsigned char tmp[16];
	unsigned char Iv[16];

	int fresh_iv;


	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	/* Condition 1 */
	poWrappingKey = find_object(&p11_ctx, args->hWrappingKey);
	if (poWrappingKey == NULL) {
		rv = CKR_WRAPPING_KEY_HANDLE_INVALID;
#ifdef PKCS_DEBUG
		printf("Condition 1.1: %x\n", args->hWrappingKey);
#endif
		return rv;
	}
	poKey = find_object(&p11_ctx, args->hKey);
	if ((poWrappingKey == NULL) || (poKey == NULL)) {
#ifdef PKCS_DEBUG
		printf("Condition 1.2\n");
#endif
		rv = CKR_KEY_HANDLE_INVALID;
		return rv;
	}

	/* Condition 2 */
	if (poWrappingKey->template != TRUSTED_TEMPLATE) {
#ifdef PKCS_DEBUG
		printf("Condition 2\n");
#endif
		rv = CKR_WRAPPING_KEY_HANDLE_INVALID;
		return rv;
	}

	/* Condition 3 */
	if (poKey->template != USAGE_TEMPLATE) {
#ifdef PKCS_DEBUG
	printf("Condition 3\n");
#endif
		rv = CKR_KEY_NOT_WRAPPABLE;
		return rv;
	}

	/* Condition 4 */
	fresh_iv = cmp_iv(args->cb, p11_ctx.iv);
	if (fresh_iv == -1) {
#ifdef PKCS_DEBUG
		printf("IV not Fresh!\n");
		print_hex(args->cb, 16);
#endif
		return CKR_MECHANISM_PARAM_INVALID;
	}
	memcpy(p11_ctx.iv, args->cb, BLOCKLEN);


	wrapping_key = poWrappingKey->key;
	key = poKey->key;

	AES_CTR_buffer(wrapping_key, p11_ctx.iv, key, args->pWrappedKey, AES_BLOCKLEN);
	increment_iv(p11_ctx.iv);


	// memcpy(args->pWrappedKey, tmp, BLOCKLEN);
	*(args->pulWrappedKeyLen) = BLOCKLEN;
	return CKR_OK;
}

/* Unwrap key.
 * Allowed under the following conditions:
 * 1. Unwrapping Key exists and is Trusted Key
 * 2. Template of unwrapped key is usage template
 */
CK_RV PKCS11_unwrap_key(UnwrapKeyArgs *args){
	pkcs11_object * poUnwrappingKey;
	CK_BYTE_PTR unwrapped_key;
	CK_OBJECT_HANDLE ulUnwrappedKey;
	CK_RV rv;
	CK_OBJECT_HANDLE hUnwrappedKey;
	unsigned char tmp[BLOCKLEN];

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	/* Condition 1 */
	poUnwrappingKey = find_object(&p11_ctx, args->hUnwrappingKey);

	if (poUnwrappingKey == NULL) {
		rv = CKR_UNWRAPPING_KEY_HANDLE_INVALID;
		return rv;
	}
	if (poUnwrappingKey->template != TRUSTED_TEMPLATE) {
		rv = CKR_KEY_FUNCTION_NOT_PERMITTED;
		return rv;
	}

	/* Condition 2 */
	if (args->template != USAGE_TEMPLATE) {
		rv = CKR_TEMPLATE_INCONSISTENT; // Check Return Value for templates not atching wwt
		return rv;
	}


	/* Decrypt Key */
	AES_CTR_buffer(poUnwrappingKey->key, args->cb, args->pWrappedKey,  tmp, AES_BLOCKLEN);
	hUnwrappedKey = insert_object(&p11_ctx, tmp, args->template);
	if (hUnwrappedKey == RV_FAILURE) { // Hit Handle Limit
		return CKR_DEVICE_MEMORY;

	}
	*(args->phKey) = hUnwrappedKey;
	return CKR_OK;
}

/* Init Encrypt arbitrary data.
 * Allowed under the following conditions:
 * 1. Key exists and is not a trusted key
 * 2. IV is fresh
 */
CK_RV PKCS11_encrypt_init(CryptInitArgs *args) {
	CK_RV rv;
	pkcs11_object * poKey;
	int fresh_iv;

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	/* Condition 1 */
	poKey = find_object(&p11_ctx, args->hKey);
	if (poKey == NULL) {
		rv = CKR_KEY_HANDLE_INVALID;
		return rv;
	}

	if (poKey->template == TRUSTED_TEMPLATE) {
		rv = CKR_KEY_FUNCTION_NOT_PERMITTED;
		return rv;
	}

	/* Condition 2 */
	fresh_iv = cmp_iv(args->cb, p11_ctx.iv);
	if (fresh_iv == -1) {
#ifdef PKCS_DEBUG
		printf("IV not Fresh!\n");
		print_hex(args->cb, 16);
#endif
		return CKR_MECHANISM_PARAM_INVALID;
	}


	p11_ctx.state = CRYPT_ENCRYPT_INIT;
	memcpy(p11_ctx.iv, args->cb, 16);
	p11_ctx.current_key = poKey->handle;
	return CKR_OK;
}

/* Init Decrypt arbitrary Data.
 * Allowed under the following conditions:
 * 1. Key exists and is not trusted key
 */
CK_RV PKCS11_decrypt_init(CryptInitArgs *args) {
	CK_RV rv;
	pkcs11_object * poKey;

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	/* Condition 1*/
	poKey =  find_object(&p11_ctx, args->hKey);
	if (poKey == NULL) {
		rv = CKR_KEY_HANDLE_INVALID;
		return rv;
	}

	if (poKey->template == TRUSTED_TEMPLATE) {
		rv = CKR_KEY_FUNCTION_NOT_PERMITTED;
		return rv;
	}


	p11_ctx.state = CRYPT_DECRYPT_INIT;
	memcpy(p11_ctx.iv, args->cb, 16);
	p11_ctx.current_key = poKey->handle;
	return CKR_OK;
}

/*
 * Encrypt arbitrary Data.
 * This is allowed under the following conditions:
 * 1. Encryption has been initialized previously
 * 2. Key is either usage/untrusted
 */
CK_RV PKCS11_encrypt( EncryptArgs *args) {
	pkcs11_object * poKey;
	CK_RV rv;
	CK_BYTE buf[args->ulDataLen];
	int i, j;

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	// did call happen after EncryptInit?
	if (p11_ctx.state != CRYPT_ENCRYPT_INIT) {
		printf("Not initialized?\n");
		return CKR_OPERATION_NOT_INITIALIZED;
	}

	// does key exist?
	poKey =  find_object(&p11_ctx, p11_ctx.current_key);
	if (poKey == NULL) {
		rv = CKR_KEY_HANDLE_INVALID;
		return rv;
	}

	if (poKey->template == TRUSTED_TEMPLATE) {
		rv = CKR_KEY_FUNCTION_NOT_PERMITTED;
		return rv;
	}

	/* Encrypt data using CTR-Mode*/
	AES_CTR_buffer(poKey->key, p11_ctx.iv, args->pData, args->pEncryptedData, args->ulDataLen);
	*(args->pulEncryptedDataLen) = (args->ulDataLen);

	// set state to not initialized
	p11_ctx.state = CRYPT_UNINITIALIZED;
	return CKR_OK;
}

/* Decrypt Data */
CK_RV PKCS11_decrypt(DecryptArgs *args) {
	pkcs11_object * poKey;
	CK_RV rv;
	CK_BYTE iv[BLOCKLEN];

	if ((&p11_ctx == NULL) || (p11_ctx.initialized == CK_FALSE))
		return CKR_CRYPTOKI_NOT_INITIALIZED;

	// did call happen after EncryptInit?
	if (p11_ctx.state != CRYPT_DECRYPT_INIT) {
		return CKR_OPERATION_NOT_INITIALIZED;
	}

	poKey = find_object(&p11_ctx, p11_ctx.current_key);
	if (poKey == NULL) {
		printf("Key not found!\n");
		return CKR_KEY_HANDLE_INVALID;
	}

	if (poKey->template == TRUSTED_TEMPLATE) {
		rv = CKR_KEY_FUNCTION_NOT_PERMITTED;
		return rv;
	}

	AES_CTR_buffer(poKey->key, p11_ctx.iv, args->pEncryptedData, args->pData, args->ulEncryptedDataLen);
#ifdef PKCS_DEBUG
	print_hex(args->pData, 16);
#endif
	*(args->pulDataLen) = args->ulEncryptedDataLen;

	// set state to uninitialized
	p11_ctx.state = CRYPT_UNINITIALIZED;

	return CKR_OK;
}

CK_RV PKCS11_delete_objects() {
	erase_oject_storage(&p11_ctx);
	return CKR_OK;
}
