/*
 * Implementing Heap operations
 * Actually not used anymore
 *
 * Author: Matthias Stockmayer
 */

/* Heap Operations */

#include <memlib.h>
#include <lib.h>

extern addr_t __guest_heap_start__, __guest_heap_end__;
extern addr_t __guest_message_box_start__, __guest_message_box_end__;

static heap_ctxt_t heap;

/* Zero and free */
void free_zero(void *addr, size_t size) {
	memset(addr, 0, size);
	free(addr);
}

/* normal free */
void free(void *addr) {
	heap_free(&heap, addr);
}

void *malloc(uint32_t size) {
	return heap_alloc(&heap, size);
}

void init_heap() {
	addr_t start = (addr_t) &__guest_heap_start__;
	addr_t end 	 = (addr_t) &__guest_heap_end__;
	heap_init(&heap, end - start - 1, (void *)start);
}

void init_message_box() {
	addr_t start = (addr_t) &__guest_message_box_start__;
	addr_t end = (addr_t) &__guest_message_box_end__;
	printf("Message Box start: %x\n", start);
	printf("Message Box end: %x\n", end);
}
