/*
 * CTR DRBG as specified in
 * NIST SP 800-90A Rev. 1
 *
 * Author: Matthias Stockmayer
 */

#ifndef CTR_DRBG_H_
#define CTR_DRBG_H_


#define SEEDLEN 	32
#define BLOCKLEN 	16
#define KEYLEN 		16

#define CTR_DRBG_SUCCESS 0
#define CTR_DRBG_FAILURE 1

#ifndef NULL
#define NULL ((void*) 0)
#endif

/* CTR_DRBG Datastructure */

typedef struct {
	unsigned char  	key[KEYLEN]; /* What the standard denotes Key */
	unsigned char   counter[BLOCKLEN]; /* What the standard denotes V */
	int 			reseed_counter;
} ctr_drbg_ctx;


/* Function Prototypes */

int ctr_drbg_instantiate(ctr_drbg_ctx *ctx, unsigned char *entropy);

int ctr_drbg_update(ctr_drbg_ctx *ctx, unsigned char *provided_data);

int ctr_dbrg_reseed(ctr_drbg_ctx *ctx, unsigned char *seed);

int ctr_drbg_generate(ctr_drbg_ctx *ctx, unsigned char *dst, unsigned int len);

int ctr_drbg_selftest();

#endif /* CTR_DRBG_H_ */
