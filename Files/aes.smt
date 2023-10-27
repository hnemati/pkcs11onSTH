; One step in AES CTR requires 3 Arguments:
; Iv: Pointer to the Iv Block
; Key: Pointer to the Key Block
; Data: Pointer to the Data Block that gets xored with AES(Key, Iv)

; Globally: mem Array (_ BitVec 32) -> (_ BitVec 32)


(declare-const key  (_ BitVec 128)) 
(declare-const iv   (_ BitVec 128))
(declare-const data (_ BitVec 128))

(declare-const keyPtr (_ BitVec 32))
(declare-const ivPtr (_ BitVec 32))
(declare-const dataPtr (_ BitVec 32))



(declare-const mem (Array (_ BitVec 32) (_ BitVec 128))) ; memory mapps

(assert (= (select mem keyPtr) key))
(assert (= (select mem ivPtr) iv))
; (assert (= (select mem dataPtr) data))


(declare-fun AES ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128)) ; c = AES(k, iv) 

(assert (= (select mem dataPtr) (AES key iv)))




(check-sat)
(get-model)
