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
(require-builtin ccsa/ll/builtin-functions as builtin.)

(define pbl (mk-problem 'x))

(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

(define prf (declare-cryptography pbl))

(define-function H pbl (prf) (Bitstring Bitstring) -> Bitstring)
(define-function key pbl (Index) -> Nonce)
(define-function n pbl (Index Index) -> Nonce)
(define-function seed pbl (Index) -> Nonce)

(define kT (declare-memory-cell pbl "kT" (list Index) (lambda (_ i) (seed i))))

(define tag
  (declare-step pbl "tag" (list Index Index)
    (step p1
      (lambda _ mtrue)
      (lambda (in i _ cells . _) (H (cells kT i) (key i)))
      (lambda (in i _ cells . _) (list (store-cell ((_) kT i) := (H (cells kT i) (key i))))))
    (step p2
      (lambda _ mtrue)
      (lambda (in i j cells . _) (n i j))
      (lambda (in i _ cells . _) (list (store-cell ((_) kT i) := (H (cells kT i) (key i))))))))

(initialize-as-prf prf H)

;; proven in squirrel
(pbl.add-smt-axiom pbl
  (forall ((t1 Time) (i Index) (i2 Index) (j Index))
    (=> (and (happens (tag i j)) (lt t1 (tag i j)))
      (not (eq (macro_memory_cell (kT i) (tag i j) p1) (macro_memory_cell (kT i2) t1 p1))))))

(bind ((i Index) (j Index))
  (register-fresh-nonce prf (list i j) (n i j)))

(run-and-save pbl p1 p2 "toy-state-equiv" "150ms")
