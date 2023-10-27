(set-logic QF_AUFBV)
(set-info :smt-lib-version 2.0)
(set-option :produce-assignments true)

; free variables:
(declare-fun R0_57 () (_ BitVec 32))
(declare-fun R1_58 () (_ BitVec 32))
(declare-fun R2_59 () (_ BitVec 32))
(declare-fun R3_60 () (_ BitVec 32))
(declare-fun CSPR_106 () (_ BitVec 32))
(declare-fun FP_FIQ_107 () (_ BitVec 32))
(declare-fun FP_108 () (_ BitVec 32))
(declare-fun mem_array_113 () (Array (_ BitVec 32)
(_ BitVec 8)))
; end free variables.

; The uninterpreted Block Cipher
(declare-fun ciphertext () (_ BitVec 128))
(declare-fun AES ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 128)) 

; Encryption of Iv under Key
;(assert (= (AES R0_57 R1_58) ciphertext))
; is at memory FP-20 FP - 4 
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967276 32))) ((_ extract 7    0) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967277 32))) ((_ extract 15   8) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967278 32))) ((_ extract 23  16) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967279 32))) ((_ extract 31  24) ciphertext )))

;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967280 32))) ((_ extract 39  32) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967281 32))) ((_ extract 47  40) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967282 32))) ((_ extract 55  48) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967283 32))) ((_ extract 63  56) ciphertext )))

;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967284 32))) ((_ extract 71  64) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967285 32))) ((_ extract 79  72) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967286 32))) ((_ extract 87  80) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967287 32))) ((_ extract 95  88) ciphertext )))

;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967288 32))) ((_ extract 103  96) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967289 32))) ((_ extract 111 104) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967290 32))) ((_ extract 119 112) ciphertext )))
;(assert (= (select mem_array_113 (bvadd FP_108 (_ bv4294967291 32))) ((_ extract 127 120) ciphertext )))



(assert 


 (let ((aes_memory_block (and
 						(= (AES (bvadd FP_108 (_ bv4294967272 32)) (bvadd FP_108 (_ bv4294967268 32))) ciphertext)
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967276 32))) ((_ extract 7    0) ciphertext ))
						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967277 32))) ((_ extract 15   8) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967278 32))) ((_ extract 23  16) ciphertext ))
            (= (select mem_array_113 (bvadd FP_108 (_ bv4294967279 32))) ((_ extract 31  24) ciphertext ))

						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967280 32))) ((_ extract 39  32) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967281 32))) ((_ extract 47  40) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967282 32))) ((_ extract 55  48) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967283 32))) ((_ extract 63  56) ciphertext ))

						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967284 32))) ((_ extract 71  64) ciphertext ))
						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967285 32))) ((_ extract 79  72) ciphertext ))
						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967286 32))) ((_ extract 87  80) ciphertext ))
						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967287 32))) ((_ extract 95  88) ciphertext ))

						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967288 32))) ((_ extract 103  96) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967289 32))) ((_ extract 111 104) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967290 32))) ((_ extract 119 112) ciphertext ))
 						(= (select mem_array_113 (bvadd FP_108 (_ bv4294967291 32))) ((_ extract 127 120) ciphertext )))))

 (let (($arguments_different_179_0 (and (not (= R0_57 R1_58))
                                   (not (= R0_57 R2_59))
                                   (not (= R0_57 R3_60))
                                   (not (= R1_58 R2_59))
                                   (not (= R1_58 R3_60))
                                   (not (= R2_59 R3_60)))))
 (let (($temp_181_1 (bvule (_ bv4026531840 32) R0_57)))
 (let (($arguments_address_valid_194_2 (and (bvule R0_57 (_ bv3489660928 32))
                                       $temp_181_1
                                       (bvule R1_58 (_ bv3489660928 32))
                                       $temp_181_1
                                       (bvule R2_59 (_ bv3494903808 32))
                                       $temp_181_1
                                       (bvule R3_60 (_ bv3494903808 32))
                                       $temp_181_1)))
 (let (($precondition_195_3 (and $arguments_different_179_0
                            $arguments_address_valid_194_2 aes_memory_block)))
 (let ((?temp_205_4 
                    
                    (ite (= ((_ extract 4 0)   CSPR_106) (_ bv17 5))
                    FP_FIQ_107 FP_108)))
 (let ((?temp_206_5 (bvadd ?temp_205_4 (_ bv4294967264 32))))
 (let ((?temp_218_6 (bvadd ?temp_206_5 (_ bv1 32))))
 (let ((?temp_231_7 (bvadd ?temp_206_5 (_ bv2 32))))
 (let ((?temp_244_8 (bvadd ?temp_206_5 (_ bv3 32))))
 (let ((?tmp_R3_248_9 (bvor
                      (bvor
                      (bvor
                      ((_ zero_extend 24) (select mem_array_113 ?temp_206_5))
                      (bvshl
                      ((_ zero_extend 24) (select mem_array_113 ?temp_218_6))
                      (_ bv8 32)))
                      (bvshl
                      ((_ zero_extend 24) (select mem_array_113 ?temp_231_7))
                      (_ bv16 32)))
                      (bvshl
                      ((_ zero_extend 24) (select mem_array_113 ?temp_244_8))
                      (_ bv24 32)))))
 (let ((?tmp_R2_255_10 
                       ((_ zero_extend 24)
                       (select mem_array_113   ?tmp_R3_248_9))))
 (let ((?tmp_R3_268_11 
                       ((_ zero_extend 24)
                       (select mem_array_113
                       (bvadd ?temp_205_4 (_ bv4294967276 32))))))
 (let ((?tmp_R3_275_12 (bvxor   ?tmp_R3_268_11   ?tmp_R2_255_10)))
 (let ((?tmp_R2_281_13 ((_ zero_extend 24) ((_ extract 7 0)   ?tmp_R3_275_12)
                       )))
 (let ((?temp_292_14 (bvadd ?temp_205_4 (_ bv4294967260 32))))
 (let ((?temp_304_15 (bvadd ?temp_292_14 (_ bv1 32))))
 (let ((?temp_317_16 (bvadd ?temp_292_14 (_ bv2 32))))
 (let ((?temp_330_17 (bvadd ?temp_292_14 (_ bv3 32))))
 (let ((?tmp_R3_334_18 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select mem_array_113 ?temp_292_14))
                       (bvshl
                       ((_ zero_extend 24)
                       (select mem_array_113 ?temp_304_15)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select mem_array_113 ?temp_317_16)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select mem_array_113 ?temp_330_17)) (_ bv24 32)))))
 (let ((?mem_array_342_19 (store mem_array_113   ?tmp_R3_334_18
                          ((_ extract 7 0)   ?tmp_R2_281_13))))
 (let ((?tmp_R3_394_20 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_292_14))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_304_15)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_317_16)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_330_17)) (_ bv24 32)))))
 (let ((?tmp_R3_399_21 (bvadd   ?tmp_R3_394_20 (_ bv1 32))))
 (let ((?tmp_R2_452_22 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_206_5))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_218_6)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_231_7)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_457_23 (bvadd   ?tmp_R2_452_22 (_ bv1 32))))
 (let ((?tmp_R1_464_24 
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19   ?tmp_R2_457_23))))
 (let ((?tmp_R2_477_25 
                       ((_ zero_extend 24)
                       (select ?mem_array_342_19
                       (bvadd ?temp_205_4 (_ bv4294967277 32))))))
 (let ((?tmp_R2_484_26 (bvxor   ?tmp_R2_477_25   ?tmp_R1_464_24)))
 (let ((?tmp_R2_490_27 ((_ zero_extend 24) ((_ extract 7 0)   ?tmp_R2_484_26)
                       )))
 (let ((?mem_array_498_28 (store ?mem_array_342_19   ?tmp_R3_399_21
                          ((_ extract 7 0)   ?tmp_R2_490_27))))
 (let ((?tmp_R3_550_29 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_292_14))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_304_15)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_317_16)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_330_17)) (_ bv24 32)))))
 (let ((?tmp_R3_555_30 (bvadd   ?tmp_R3_550_29 (_ bv2 32))))
 (let ((?tmp_R2_608_31 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_206_5))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_218_6)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_231_7)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_613_32 (bvadd   ?tmp_R2_608_31 (_ bv2 32))))
 (let ((?tmp_R1_620_33 
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28   ?tmp_R2_613_32))))
 (let ((?tmp_R2_633_34 
                       ((_ zero_extend 24)
                       (select ?mem_array_498_28
                       (bvadd ?temp_205_4 (_ bv4294967278 32))))))
 (let ((?tmp_R2_640_35 (bvxor   ?tmp_R2_633_34   ?tmp_R1_620_33)))
 (let ((?tmp_R2_646_36 ((_ zero_extend 24) ((_ extract 7 0)   ?tmp_R2_640_35)
                       )))
 (let ((?mem_array_654_37 (store ?mem_array_498_28   ?tmp_R3_555_30
                          ((_ extract 7 0)   ?tmp_R2_646_36))))
 (let ((?tmp_R3_706_38 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_292_14))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_304_15)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_317_16)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_330_17)) (_ bv24 32)))))
 (let ((?tmp_R3_711_39 (bvadd   ?tmp_R3_706_38 (_ bv3 32))))
 (let ((?tmp_R2_764_40 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_206_5))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_218_6)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_231_7)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_769_41 (bvadd   ?tmp_R2_764_40 (_ bv3 32))))
 (let ((?tmp_R1_776_42 
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37   ?tmp_R2_769_41))))
 (let ((?tmp_R2_789_43 
                       ((_ zero_extend 24)
                       (select ?mem_array_654_37
                       (bvadd ?temp_205_4 (_ bv4294967279 32))))))
 (let ((?tmp_R2_796_44 (bvxor   ?tmp_R2_789_43   ?tmp_R1_776_42)))
 (let ((?tmp_R2_802_45 ((_ zero_extend 24) ((_ extract 7 0)   ?tmp_R2_796_44)
                       )))
 (let ((?mem_array_810_46 (store ?mem_array_654_37   ?tmp_R3_711_39
                          ((_ extract 7 0)   ?tmp_R2_802_45))))
 (let ((?tmp_R3_862_47 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_292_14))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_304_15)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_317_16)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_330_17)) (_ bv24 32)))))
 (let ((?tmp_R3_867_48 (bvadd   ?tmp_R3_862_47 (_ bv4 32))))
 (let ((?tmp_R2_920_49 (bvor
                       (bvor
                       (bvor
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_206_5))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_218_6)) (_ bv8 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_231_7)) (_ bv16 32)))
                       (bvshl
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_925_50 (bvadd   ?tmp_R2_920_49 (_ bv4 32))))
 (let ((?tmp_R1_932_51 
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46   ?tmp_R2_925_50))))
 (let ((?tmp_R2_945_52 
                       ((_ zero_extend 24)
                       (select ?mem_array_810_46
                       (bvadd ?temp_205_4 (_ bv4294967280 32))))))
 (let ((?tmp_R2_952_53 (bvxor   ?tmp_R2_945_52   ?tmp_R1_932_51)))
 (let ((?tmp_R2_958_54 ((_ zero_extend 24) ((_ extract 7 0)   ?tmp_R2_952_53)
                       )))
 (let ((?mem_array_966_55 (store ?mem_array_810_46   ?tmp_R3_867_48
                          ((_ extract 7 0)   ?tmp_R2_958_54))))
 (let ((?tmp_R3_1018_56 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_292_14))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_304_15)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_317_16)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_330_17)) (_ bv24 32)))))
 (let ((?tmp_R3_1023_57 (bvadd   ?tmp_R3_1018_56 (_ bv5 32))))
 (let ((?tmp_R2_1076_58 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_206_5))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_218_6)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_231_7)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_1081_59 (bvadd   ?tmp_R2_1076_58 (_ bv5 32))))
 (let ((?tmp_R1_1088_60 
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55   ?tmp_R2_1081_59))))
 (let ((?tmp_R2_1101_61 
                        ((_ zero_extend 24)
                        (select ?mem_array_966_55
                        (bvadd ?temp_205_4 (_ bv4294967281 32))))))
 (let ((?tmp_R2_1108_62 (bvxor   ?tmp_R2_1101_61   ?tmp_R1_1088_60)))
 (let ((?tmp_R2_1114_63 ((_ zero_extend 24)
                        ((_ extract 7 0)   ?tmp_R2_1108_62))))
 (let ((?mem_array_1122_64 (store ?mem_array_966_55   ?tmp_R3_1023_57
                           ((_ extract 7 0)   ?tmp_R2_1114_63))))
 (let ((?tmp_R3_1174_65 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_292_14))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_304_15)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_317_16))
                        (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_330_17))
                        (_ bv24 32)))))
 (let ((?tmp_R3_1179_66 (bvadd   ?tmp_R3_1174_65 (_ bv6 32))))
 (let ((?tmp_R2_1232_67 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_206_5))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_218_6)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_231_7)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_1237_68 (bvadd   ?tmp_R2_1232_67 (_ bv6 32))))
 (let ((?tmp_R1_1244_69 
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64   ?tmp_R2_1237_68))))
 (let ((?tmp_R2_1257_70 
                        ((_ zero_extend 24)
                        (select ?mem_array_1122_64
                        (bvadd ?temp_205_4 (_ bv4294967282 32))))))
 (let ((?tmp_R2_1264_71 (bvxor   ?tmp_R2_1257_70   ?tmp_R1_1244_69)))
 (let ((?tmp_R2_1270_72 ((_ zero_extend 24)
                        ((_ extract 7 0)   ?tmp_R2_1264_71))))
 (let ((?mem_array_1278_73 (store ?mem_array_1122_64   ?tmp_R3_1179_66
                           ((_ extract 7 0)   ?tmp_R2_1270_72))))
 (let ((?tmp_R3_1330_74 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_292_14))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_304_15)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_317_16))
                        (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_330_17))
                        (_ bv24 32)))))
 (let ((?tmp_R3_1335_75 (bvadd   ?tmp_R3_1330_74 (_ bv7 32))))
 (let ((?tmp_R2_1388_76 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_206_5))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_218_6)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_231_7)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_1393_77 (bvadd   ?tmp_R2_1388_76 (_ bv7 32))))
 (let ((?tmp_R1_1400_78 
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73   ?tmp_R2_1393_77))))
 (let ((?tmp_R2_1413_79 
                        ((_ zero_extend 24)
                        (select ?mem_array_1278_73
                        (bvadd ?temp_205_4 (_ bv4294967283 32))))))
 (let ((?tmp_R2_1420_80 (bvxor   ?tmp_R2_1413_79   ?tmp_R1_1400_78)))
 (let ((?tmp_R2_1426_81 ((_ zero_extend 24)
                        ((_ extract 7 0)   ?tmp_R2_1420_80))))
 (let ((?mem_array_1434_82 (store ?mem_array_1278_73   ?tmp_R3_1335_75
                           ((_ extract 7 0)   ?tmp_R2_1426_81))))
 (let ((?tmp_R3_1486_83 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_292_14))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_304_15)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_317_16))
                        (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_330_17))
                        (_ bv24 32)))))
 (let ((?tmp_R3_1491_84 (bvadd   ?tmp_R3_1486_83 (_ bv8 32))))
 (let ((?tmp_R2_1544_85 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_206_5))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_218_6)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_231_7)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_1549_86 (bvadd   ?tmp_R2_1544_85 (_ bv8 32))))
 (let ((?tmp_R1_1556_87 
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82   ?tmp_R2_1549_86))))
 (let ((?tmp_R2_1569_88 
                        ((_ zero_extend 24)
                        (select ?mem_array_1434_82
                        (bvadd ?temp_205_4 (_ bv4294967284 32))))))
 (let ((?tmp_R2_1576_89 (bvxor   ?tmp_R2_1569_88   ?tmp_R1_1556_87)))
 (let ((?tmp_R2_1582_90 ((_ zero_extend 24)
                        ((_ extract 7 0)   ?tmp_R2_1576_89))))
 (let ((?mem_array_1590_91 (store ?mem_array_1434_82   ?tmp_R3_1491_84
                           ((_ extract 7 0)   ?tmp_R2_1582_90))))
 (let ((?tmp_R3_1642_92 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_292_14))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_304_15)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_317_16))
                        (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_330_17))
                        (_ bv24 32)))))
 (let ((?tmp_R3_1647_93 (bvadd   ?tmp_R3_1642_92 (_ bv9 32))))
 (let ((?tmp_R2_1700_94 (bvor
                        (bvor
                        (bvor
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_206_5))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_218_6)) (_ bv8 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_231_7)) (_ bv16 32)))
                        (bvshl
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91 ?temp_244_8)) (_ bv24 32)))))
 (let ((?tmp_R2_1705_95 (bvadd   ?tmp_R2_1700_94 (_ bv9 32))))
 (let ((?tmp_R1_1712_96 
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91   ?tmp_R2_1705_95))))
 (let ((?tmp_R2_1725_97 
                        ((_ zero_extend 24)
                        (select ?mem_array_1590_91
                        (bvadd ?temp_205_4 (_ bv4294967285 32))))))
 (let ((?tmp_R2_1732_98 (bvxor   ?tmp_R2_1725_97   ?tmp_R1_1712_96)))
 (let ((?tmp_R2_1738_99 ((_ zero_extend 24)
                        ((_ extract 7 0)   ?tmp_R2_1732_98))))
 (let ((?mem_array_1746_100 (store ?mem_array_1590_91   ?tmp_R3_1647_93
                            ((_ extract 7 0)   ?tmp_R2_1738_99))))
 (let ((?tmp_R3_1798_101 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_1803_102 (bvadd   ?tmp_R3_1798_101 (_ bv10 32))))
 (let ((?tmp_R2_1856_103 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_1861_104 (bvadd   ?tmp_R2_1856_103 (_ bv10 32))))
 (let ((?tmp_R1_1868_105 
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100   ?tmp_R2_1861_104))))
 (let ((?tmp_R2_1881_106 
                         ((_ zero_extend 24)
                         (select ?mem_array_1746_100
                         (bvadd ?temp_205_4 (_ bv4294967286 32))))))
 (let ((?tmp_R2_1888_107 (bvxor   ?tmp_R2_1881_106   ?tmp_R1_1868_105)))
 (let ((?tmp_R2_1894_108 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_1888_107))))
 (let ((?mem_array_1902_109 (store ?mem_array_1746_100   ?tmp_R3_1803_102
                            ((_ extract 7 0)   ?tmp_R2_1894_108))))
 (let ((?tmp_R3_1954_110 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_1959_111 (bvadd   ?tmp_R3_1954_110 (_ bv11 32))))
 (let ((?tmp_R2_2012_112 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_2017_113 (bvadd   ?tmp_R2_2012_112 (_ bv11 32))))
 (let ((?tmp_R1_2024_114 
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109   ?tmp_R2_2017_113))))
 (let ((?tmp_R2_2037_115 
                         ((_ zero_extend 24)
                         (select ?mem_array_1902_109
                         (bvadd ?temp_205_4 (_ bv4294967287 32))))))
 (let ((?tmp_R2_2044_116 (bvxor   ?tmp_R2_2037_115   ?tmp_R1_2024_114)))
 (let ((?tmp_R2_2050_117 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_2044_116))))
 (let ((?mem_array_2058_118 (store ?mem_array_1902_109   ?tmp_R3_1959_111
                            ((_ extract 7 0)   ?tmp_R2_2050_117))))
 (let ((?tmp_R3_2110_119 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_2115_120 (bvadd   ?tmp_R3_2110_119 (_ bv12 32))))
 (let ((?tmp_R2_2168_121 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_2173_122 (bvadd   ?tmp_R2_2168_121 (_ bv12 32))))
 (let ((?tmp_R1_2180_123 
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118   ?tmp_R2_2173_122))))
 (let ((?tmp_R2_2193_124 
                         ((_ zero_extend 24)
                         (select ?mem_array_2058_118
                         (bvadd ?temp_205_4 (_ bv4294967288 32))))))
 (let ((?tmp_R2_2200_125 (bvxor   ?tmp_R2_2193_124   ?tmp_R1_2180_123)))
 (let ((?tmp_R2_2206_126 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_2200_125))))
 (let ((?mem_array_2214_127 (store ?mem_array_2058_118   ?tmp_R3_2115_120
                            ((_ extract 7 0)   ?tmp_R2_2206_126))))
 (let ((?tmp_R3_2266_128 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_2271_129 (bvadd   ?tmp_R3_2266_128 (_ bv13 32))))
 (let ((?tmp_R2_2324_130 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_2329_131 (bvadd   ?tmp_R2_2324_130 (_ bv13 32))))
 (let ((?tmp_R1_2336_132 
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127   ?tmp_R2_2329_131))))
 (let ((?tmp_R2_2349_133 
                         ((_ zero_extend 24)
                         (select ?mem_array_2214_127
                         (bvadd ?temp_205_4 (_ bv4294967289 32))))))
 (let ((?tmp_R2_2356_134 (bvxor   ?tmp_R2_2349_133   ?tmp_R1_2336_132)))
 (let ((?tmp_R2_2362_135 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_2356_134))))
 (let ((?mem_array_2370_136 (store ?mem_array_2214_127   ?tmp_R3_2271_129
                            ((_ extract 7 0)   ?tmp_R2_2362_135))))
 (let ((?tmp_R3_2422_137 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_2427_138 (bvadd   ?tmp_R3_2422_137 (_ bv14 32))))
 (let ((?tmp_R2_2480_139 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_2485_140 (bvadd   ?tmp_R2_2480_139 (_ bv14 32))))
 (let ((?tmp_R1_2492_141 
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136   ?tmp_R2_2485_140))))
 (let ((?tmp_R2_2505_142 
                         ((_ zero_extend 24)
                         (select ?mem_array_2370_136
                         (bvadd ?temp_205_4 (_ bv4294967290 32))))))
 (let ((?tmp_R2_2512_143 (bvxor   ?tmp_R2_2505_142   ?tmp_R1_2492_141)))
 (let ((?tmp_R2_2518_144 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_2512_143))))
 (let ((?mem_array_2526_145 (store ?mem_array_2370_136   ?tmp_R3_2427_138
                            ((_ extract 7 0)   ?tmp_R2_2518_144))))
 (let ((?tmp_R3_2578_146 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_292_14))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_304_15))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_317_16))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_330_17))
                         (_ bv24 32)))))
 (let ((?tmp_R3_2583_147 (bvadd   ?tmp_R3_2578_146 (_ bv15 32))))
 (let ((?tmp_R2_2636_148 (bvor
                         (bvor
                         (bvor
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_206_5))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_218_6))
                         (_ bv8 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_231_7))
                         (_ bv16 32)))
                         (bvshl
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145 ?temp_244_8))
                         (_ bv24 32)))))
 (let ((?tmp_R2_2641_149 (bvadd   ?tmp_R2_2636_148 (_ bv15 32))))
 (let ((?tmp_R1_2648_150 
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145   ?tmp_R2_2641_149))))
 (let ((?tmp_R2_2661_151 
                         ((_ zero_extend 24)
                         (select ?mem_array_2526_145
                         (bvadd ?temp_205_4 (_ bv4294967291 32))))))
 (let ((?tmp_R2_2668_152 (bvxor   ?tmp_R2_2661_151   ?tmp_R1_2648_150)))
 (let ((?tmp_R2_2674_153 ((_ zero_extend 24)
                         ((_ extract 7 0)   ?tmp_R2_2668_152))))
 (let ((?mem_array_2682_154 (store ?mem_array_2526_145   ?tmp_R3_2583_147
                            ((_ extract 7 0)   ?tmp_R2_2674_153))))
 (let ((?temp_2740_155 (bvadd R0_57 (_ bv1 32))))
 (let ((?temp_2745_156 (bvadd R0_57 (_ bv2 32))))
 (let ((?temp_2750_157 (bvadd R0_57 (_ bv3 32))))
 (let ((?temp_2779_158 (bvadd R1_58 (_ bv1 32))))
 (let ((?temp_2784_159 (bvadd R1_58 (_ bv2 32))))
 (let ((?temp_2789_160 (bvadd R1_58 (_ bv3 32))))

; this unreadable snippet checks wether buffer = AES(Key, Iv) \xor data
; first build the address pointing to the data buffer. This is on the stack at address FP - 32. Since mem_array is 32 -> 8, we have to manually construct this shit
; this is the address on the stack containing the src pointer
(let ((fp_minus_32 (bvadd FP_108 (_ bv4294967264 32)) ))

; select each byte of the address
(let ((data_ptr_0 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv0 32))))))
(let ((data_ptr_1 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv1 32))))))
(let ((data_ptr_2 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv2 32))))))
(let ((data_ptr_3 ((_ zero_extend 24) (select mem_array_113 (bvadd fp_minus_32 (_ bv3 32))))))

; put the address bytes together
(let ((data_ptr 
	(bvor 
  (bvor
    (bvor data_ptr_0 (bvshl data_ptr_1 (_  bv8 32)))
		  (bvshl data_ptr_2 (_ bv16 32)))
		  (bvshl data_ptr_3 (_ bv24 32)))))

; check wether the xor is correct. 
(let (($ctr_correct
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967276 32))) 
		(bvxor ((_ extract 7 0) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv0 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967277 32))) 
		(bvxor ((_ extract 15 8) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv1 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967278 32))) 
		(bvxor ((_ extract 23 16) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv2 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967279 32))) 
		(bvxor ((_ extract 31 24) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv3 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967280 32))) 
		(bvxor ((_ extract 39 32) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv4 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967281 32))) 
		(bvxor ((_ extract 47 40) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv5 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967282 32))) 
		(bvxor ((_ extract 55 48) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv6 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967283 32))) 
		(bvxor ((_ extract 63 56) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv7 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967284 32))) 
		(bvxor ((_ extract 71 64) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv8 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967285 32))) 
		(bvxor ((_ extract 79 72) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv9 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967286 32))) 
		(bvxor ((_ extract 87 80) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv10 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967287 32))) 
		(bvxor ((_ extract 95 88) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv11 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967288 32))) 
		(bvxor ((_ extract 103 96) ciphertext)  (select mem_array_113 (bvadd data_ptr  (_ bv12 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967289 32))) 
		(bvxor ((_ extract 111 104) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv13 32)))))
(and (= (select mem_array_113 (bvadd FP_108 (_ bv4294967290 32))) 
		(bvxor ((_ extract 119 112) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv14 32)))))
(= (select mem_array_113 (bvadd FP_108 (_ bv4294967291 32))) 
		(bvxor ((_ extract 127 120) ciphertext)  (select mem_array_113 (bvadd data_ptr (_ bv15 32))))))))))))))))))))))

 (let (($key_iv_not_changed_2814_161 (and
                                     (=
                                     (bvor
                                     (bvor
                                     (bvor
                                     ((_ zero_extend 24)
                                     (select mem_array_113 R0_57))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2740_155))
                                     (_ bv8 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2745_156))
                                     (_ bv16 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2750_157))
                                     (_ bv24 32)))
                                     (bvor
                                     (bvor
                                     (bvor
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154 R0_57))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2740_155)) (_ bv8 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2745_156)) (_ bv16 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2750_157)) (_ bv24 32))))
                                     (=
                                     (bvor
                                     (bvor
                                     (bvor
                                     ((_ zero_extend 24)
                                     (select mem_array_113 R1_58))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2779_158))
                                     (_ bv8 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2784_159))
                                     (_ bv16 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select mem_array_113 ?temp_2789_160))
                                     (_ bv24 32)))
                                     (bvor
                                     (bvor
                                     (bvor
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154 R1_58))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2779_158)) (_ bv8 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2784_159)) (_ bv16 32)))
                                     (bvshl
                                     ((_ zero_extend 24)
                                     (select ?mem_array_2682_154
                                     ?temp_2789_160)) (_ bv24 32)))))))
 (let (($goal_2817_162 (not (=> $precondition_195_3 (and $ctr_correct $key_iv_not_changed_2814_161)))))
 $goal_2817_162))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 ))))))))))))))))))))))))))))))))))

(check-sat)
(exit)
