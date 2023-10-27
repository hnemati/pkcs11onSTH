/*
 * trusted_guest.h

 *      Author: Matthias Stockmayer
 */

#ifndef GUESTS_TRUSTED_SRC_TRUSTED_GUEST_H_
#define GUESTS_TRUSTED_SRC_TRUSTED_GUEST_H_


void guest_handler(int cmd, void* args) __attribute__((section("tguest")));


#endif /* GUESTS_TRUSTED_SRC_TRUSTED_GUEST_H_ */
