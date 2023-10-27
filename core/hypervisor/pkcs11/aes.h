/*
 * aes.h
 *
 * AES Implementation based on tiny-AES-c
 * https://github.com/kokke/tiny-AES-c
 */

#ifndef _AES_H_
#define _AES_H_

#include "types.h"

typedef unsigned long uintptr_t;

#define AES_BLOCKLEN 16 // 128 Bit Block Length
#define AES_KEYLEN 16
#define AES_keyExpSize 176


void AES_ECB_encrypt(uint8_t* key, const uint8_t* buf);
void AES_ECB_decrypt(uint8_t* key, const uint8_t* buf);
void AES_CTR_xcrypt_buffer(uint8_t* key, uint8_t* iv, uint8_t* buf, uint32_t length);


#endif /* _AES_H_ */
