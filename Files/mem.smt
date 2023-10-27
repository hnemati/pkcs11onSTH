(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-option :produce-assignments true)

; free variables:
; end free variables.

(assert true)
(check-sat)
(exit)
