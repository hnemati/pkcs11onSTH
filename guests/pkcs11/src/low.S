

	.global syscall_pkcs11
	.code 32
	.balign 4


syscall_pkcs11:
	svc # 667
	bx lr
