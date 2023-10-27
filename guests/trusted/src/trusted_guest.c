/*
 * trusted_guest.c
 *
 * Author: Matthias Stockmayer
 */
#include "trusted_guest.h"
#include <lib.h>


void guest_handler(int cmd, void* args) {
	printf("Hello World\n");
}



void handler_rpc(unsigned callNum, void *params)
{
	return;
}


void _main() {
	printf("main");
	guest_handler(0, 0);
}
