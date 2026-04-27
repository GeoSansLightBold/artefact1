(require "../save-results.scm")
(require "ccsa/function")
(require "ccsa/builtin-functions")
(require "ccsa/cryptography")
(require "ccsa/protocol")
(require "ccsa/solver")
(require "ccsa/sort")
(require "ccsa/formula")
(require "ccsa/signature")
(require-builtin ccsa/ll/pbl as pbl.)
(require-builtin ccsa/ll/configuration as config.)
(require-builtin ccsa/ll as b.)
(require-builtin ccsa/ll/report as report.)
(require-builtin ccsa/ll/rewrite as rw.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))
(define ptcls (list p1 p2))

(define ddh (declare-cryptography pbl))
(define-function g pbl (ddh) Bitstring)
(define-function mexp pbl (ddh) (Bitstring Bitstring) -> Bitstring)
(initialize-as-ddh ddh g mexp)

(define-function a1 pbl Nonce)
(define-function b1 pbl Nonce)
(define-function c11 pbl Nonce)

(register-fresh-nonce ddh '() c11)

(define empty-cond (lambda _ mtrue))

(define SDIS1 (declare-same-step pbl "SDIS1" ptcls '()
    empty-cond
    (lambda (p in . _) (mexp g b1))
    empty-assignements))

(define SDIS2 (declare-step pbl "SDIS2" '()
    (step p1 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp (mexp g a1) b1))
      empty-assignements)
    (step p2 (lambda (in . _) (eq in (mexp g a1)))
      (lambda (in . _) (mexp g c11))
      empty-assignements)))

(add-constrain pbl () (lt SDIS1 SDIS2))

(publish pbl () (mexp g a1))
(publish pbl () (mexp g b1))

(run-and-save pbl p1 p2 "ssh-forward-part2-secret" "150ms")
