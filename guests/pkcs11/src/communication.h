/*
 * communication.h
 *
 * Hypercall Wrapper for convenience
 *
 *  Created on: 14.11.2017
 *      Author: Matthias Stockmayer
 */

#ifndef _COMMUNICATION_H_
#define _COMMUNICATION_H_

#include <uclib.h>

uint32_t l1[4096] __attribute__ ((aligned (16 * 1024)));
uint32_t l2[1024] __attribute__ ((aligned (4 * 1024)));


extern uint32_t syscall_pkcs11(uint32_t r0, uint32_t r1, uint32_t r2);

#define ISSUE_HYPERCALL(type, p0, p1, p2) \
	syscall_pkcs11(type | (p2 << 4), p0, p1);

#define ISSUE_HYPERCALL_(type, p0, p1, p2, p3) \
		syscall_pkcs11((type | (p2 & 0xFFFFFFFF0)), p0, ((p1 << 20) | p3));



uint32_t call_hypervisor(int,  uint32_t, uint32_t, uint32_t);



#endif

