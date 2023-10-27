#include "../../pkcs11/src/communication.h"

#include <lib.h>
#include <types.h>
#include <uclib.h>

#define ISSUE_HYPERCALL(type, p0, p1, p2) \
		syscall_pkcs11(type, p0, p1);


uint32_t call_hypervisor(int command, uint32_t  arg0, uint32_t arg1, uint32_t arg2)
{
	//printf("Hypercall: %x, %x\n", command, arg0);
	uint32_t res;

	res = ISSUE_HYPERCALL(command, (uint32_t) arg0, arg1, arg2);
	if (res == -1)
	{
		printf("Error while communicating with the hypervisor\n");
	}
	return res;
}
