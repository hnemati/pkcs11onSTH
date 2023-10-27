#include "ctr_drbg.h"

#include "aes.h"
#include "types.h"
#include "uclib.h"


/*
 * Initiate CTR DRBG
 * ctx: Context holding State information
 * entropy: Entropy, provided by the Guest
 */
int ctr_drbg_instantiate(ctr_drbg_ctx *ctx, unsigned char *entropy) {

	int res;

	/* initialize key and counter buffers */
	memset(ctx->key, 0, KEYLEN);
	memset(ctx->counter, 0, BLOCKLEN);

	/* invoke drbg */
	res = ctr_drbg_update(ctx, entropy);
	if (res != CTR_DRBG_SUCCESS)
		return res;

	/* we don't support reseeding yet, so we only keep this for consistency with the standard */
	ctx->reseed_counter = 1;
	return CTR_DRBG_SUCCESS;
}

/*
 * Reset the Key and the Counter
 * Provided data: Additional Input, not necessarily required
 */
int ctr_drbg_update(ctr_drbg_ctx *ctx, unsigned char *provided_data) {

	unsigned char temp[SEEDLEN]; // holding random bytes at the end
	unsigned char *temp_ptr = temp;

	int i, temp_len;

	memset(temp, 0, SEEDLEN);

	// Encrypt Counter twice
	// The next key will be the result of the first encryption
	// The next Counter will be the result of the second encryption
	for (temp_len = 0; temp_len < SEEDLEN; temp_len += BLOCKLEN) {

		/* increase counter */
		for (i = BLOCKLEN; i > 0; i--) {
			if (++(ctx->counter[i-1]) != 0)
				break;
		}

		/* Encrypt Counter */
		memcpy(temp_ptr, ctx->counter, BLOCKLEN);
		AES_ECB_encrypt(ctx->key, temp_ptr);
		temp_ptr += BLOCKLEN;
	}

	for (i = 0; i < SEEDLEN; i++) {
		temp[i] = temp[i] ^ provided_data[i];
	}

	// update key and counter
	memcpy(ctx->key, temp, KEYLEN);
	memcpy(ctx->counter, temp + KEYLEN, BLOCKLEN);
	return CTR_DRBG_SUCCESS;
}

/*
 * Generate (Pseudo)Random Bitstring of size len
 */
int ctr_drbg_generate(ctr_drbg_ctx *ctx, unsigned char *dst, unsigned int len) {
	int res, i, temp_len;

	if (ctx->reseed_counter > 100000)
		return CTR_DRBG_FAILURE;

	// Additional Data is optional, but has to be set to zero if not used
	unsigned char additional_input[SEEDLEN];
	unsigned char temp[len]; // Buffer containing Randomness at the end
	unsigned char * temp_ptr = temp;

	memset(additional_input, 0, SEEDLEN);
	memset(temp, 0, len);

	for (temp_len = 0; temp_len < len; temp_len += BLOCKLEN) {
		/* increase counter */
		for (i = BLOCKLEN; i > 0; i--) {
			if (++ctx->counter[i-1] != 0)
				break;
		}

		/* Encrypt Counter */
		memcpy(temp_ptr, ctx->counter, BLOCKLEN);
		AES_ECB_encrypt(ctx->key, temp_ptr);

		temp_ptr += BLOCKLEN;
	}

	/* Copy to Destination Buffer */
	memcpy(dst, temp, len);

	/* Update DRBG Context */
	ctr_drbg_update(ctx, additional_input);
	++ctx->reseed_counter;

	return CTR_DRBG_SUCCESS;
}

int_ctr_drbg_uninstantiate(ctr_drbg_ctx * ctx) {
	memset(ctx->key, 0, KEYLEN);
	memset(ctx->counter, 0, BLOCKLEN);
	ctx->reseed_counter = 0;

	return CTR_DRBG_SUCCESS;
}


/* These Test Vectors are taken from
 * The NIST SP 800-90A Deterministic Random
 * Bit Generator Validation System (DRBGVS)
 * (CAVS 14.3)
 *
 * with the Scenario:
 *
 * [AES-128 no df]
 * [PredictionResistance = False]
 * [EntropyInputLen = 256]
 * [NonceLen = 0]
 * [PersonalizationStringLen = 0]
 * [AdditionalInputLen = 0]
 * [ReturnedBitsLen = 512]
 *
 */
static const unsigned char entropy_input_count0[32] = {
		0x08, 0x4b, 0x35, 0x2f, 0x38, 0xab, 0x28, 0xd9,
		0xc1, 0xc7, 0xff, 0x16, 0x55, 0x8e, 0x0a, 0x12,
		0x37, 0x7d, 0x82, 0x0c, 0xd6, 0xec, 0xa3, 0xa3,
		0x52, 0xa6, 0xfe, 0xc3, 0x81, 0xf3, 0x58, 0x44
};


static const unsigned char key_count0[16] = {
		0x50, 0xa9, 0xc9, 0xe1, 0xc2, 0xd5, 0x18, 0xb8,
		0xf7, 0xb8, 0xe2, 0x41, 0xf1, 0x69, 0x4f, 0x48
};


static const unsigned char v_count0[16] = {
		0x34, 0xf5, 0x58, 0xc2, 0xb6, 0x5a, 0x00, 0x31,
		0xa1, 0x8e, 0x3c, 0x7a, 0xf0, 0x41, 0xa6, 0x3c
};

static const unsigned char generate_first_call_key_count0[16] = {
		0x7e, 0xf5, 0x88, 0x8b, 0x05, 0x9b, 0x97, 0xee,
		0xcd, 0x6e, 0x2c, 0xd5, 0x4a, 0xcb, 0x3b, 0x26
};


static const unsigned char generate_first_call_v_count0[16] = {
		0xe4, 0xf5, 0x63, 0x46, 0xb9, 0xd3, 0x29, 0x10,
		0x84, 0x88, 0xc7, 0xcf, 0xeb, 0x49, 0x29, 0x99
};

static const unsigned char generate_second_call_key_count0[16] = {
		0x2f, 0x99, 0x36, 0x2f, 0x52, 0x32, 0x9c, 0x11,
		0xa4, 0x82, 0x37, 0x53, 0xc0, 0x78, 0xba, 0x0a
};

static const unsigned char generate_second_call_v_count0[16] = {
		0x1d, 0x3e, 0xb8, 0x97, 0x81, 0xd7, 0x70, 0x02,
		0x2e, 0x0f, 0x7f, 0xce, 0xf9, 0x81, 0x32, 0x10
};


static const unsigned char returned_bits_count0[512] = {
		0xcb, 0xdf, 0xff, 0x95, 0xde, 0x29, 0x06, 0xf3,
		0x42, 0x3e, 0xb4, 0x42, 0x2b, 0xd3, 0xb0, 0xe6,
		0xed, 0x55, 0xa7, 0x84, 0x3a, 0xb6, 0xeb, 0xed,
		0xf5, 0x2a, 0xca, 0xf2, 0x8e, 0x7a, 0x5a, 0xe0,
		0x61, 0xae, 0xdb, 0x49, 0xe7, 0x47, 0x67, 0x83,
		0xf5, 0xcf, 0x29, 0x54, 0x16, 0x8c, 0x8e, 0xbc,
		0x3c, 0x9a, 0xb0, 0xb1, 0xa1, 0xcb, 0x87, 0x90,
		0x76, 0xb4, 0x76, 0x97, 0xb3, 0x6f, 0x95, 0x40
};


int ctr_drbg_selftest() {

	printf("CTR DRBG Selftest...\n");
	int cmp;
	ctr_drbg_ctx ctx;

	/* Instantiate */
	ctr_drbg_instantiate(&ctx, entropy_input_count0);
	cmp = memcmp( ctx.key, key_count0, 16);
	if (cmp != 0) {
		// printf("Key after instantiate Wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}

	cmp = memcmp(ctx.counter, v_count0, 16);
	if (cmp != 0){
		// printf("Value after Instantiate Wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}


	unsigned char dst[64];

	/* First Generate call, without print */
	ctr_drbg_generate(&ctx, dst, 64);

	cmp = memcmp(ctx.key, generate_first_call_key_count0, 16);
	if (cmp != 0) {
		// printf("Key after Generate Wrong Count 0!\n");
		printf("... failed!\n");
	}

	cmp = memcmp(ctx.counter, generate_first_call_v_count0, 16);
	if (cmp != 0) {
		// printf("Value after Generate Wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}


	/* Second Generate call, with print */
	ctr_drbg_generate(&ctx, dst, 64);

	cmp = memcmp(ctx.key, generate_second_call_key_count0, 16);
	if (cmp != 0) {
		// printf("Key after Generate Wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}

	cmp = memcmp(ctx.counter, generate_second_call_v_count0, 16);
	if (cmp != 0) {
		// printf("Value after Generate Wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}

	cmp = memcmp(dst, returned_bits_count0, 64);
	if (cmp != 0) {
		// printf("Returned bits wrong Count 0!\n");
		printf("... failed!\n");
		return -1;
	}

	printf("passed!\n");
	return 0;
}
