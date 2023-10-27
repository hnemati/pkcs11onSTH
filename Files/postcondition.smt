; this unreadable snippet checks wether buffer = AES(Key, Iv) \xor data
; first build the address pointing to the data buffer. This is on the stack at address FP - 32. Since mem_array is 32 -> 8, we have to manuall construct this shit
; this is the address on the stack containg the src pointer
(let fp_minus_32 (bvadd FP_108 (_ bv4294967264)) 

; select each byte of the address
(let data_ptr_0 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv0 32)))) 
(let data_ptr_1 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv1 32))))
(let data_ptr_2 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv2 32))))
(let data_ptr_3 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv3 32))))

; put the address bytes together
(let data_ptr 
	(bvor
	(bvor 
	(bvor 
		(data_ptr_0) 
		(bvshl data_ptr_1 (_  bv8 32)))
		(bvshl data_ptr_2 (_ bv16 32)))
		(bvshl data_ptr_3 (_ bv24 32)))

; check wether the xor is correct. 
(let ctr_correct 
((= (select mem_array_113 (bvadd FP_108 (_ bv4294967276 32))) 
		(bvxor ((_ extract 7 0) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv0 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967277 32))) 
		(bvxor ((_ extract 15 8) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv1 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967278 32))) 
		(bvxor ((_ extract 23 16) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv2 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967279 32))) 
		(bvxor ((_ extract 31 24) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv3 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967280 32))) 
		(bvxor ((_ extract 39 32) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv4 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967281 32))) 
		(bvxor ((_ extract 47 40) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv5 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967282 32))) 
		(bvxor ((_ extract 55 48) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv6 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967283 32))) 
		(bvxor ((_ extract 63 56) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv7 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967284 32))) 
		(bvxor ((_ extract 71 64) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv8 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967285 32))) 
		(bvxor ((_ extract 79 72) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv9 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967286 32))) 
		(bvxor ((_ extract 87 80) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv10 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967287 32))) 
		(bvxor ((_ extract 95 88) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv11 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967288 32))) 
		(bvxor ((_ extract 103 96) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv12 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967289 32))) 
		(bvxor ((_ extract 111 104) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv13 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967290 32))) 
		(bvxor ((_ extract 119 112) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv14 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967291 32))) 
		(bvxor ((_ extract 127 120) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv15 32))))))
)))))))
