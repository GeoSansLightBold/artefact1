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

;; Simple memory cell test
;; Declare a memory cell with no parameters (single value)
(define s (declare-memory-cell pbl "s" '() (lambda (p) empty)))

;; Tag process that reads and updates the memory cell
(define tag
  (declare-step pbl "tag" '()
    (step p1 (lambda _ mtrue) (lambda _ mempty) (lambda (in cells) (list (store-cell s := mempty))))
    (step p2 (lambda _ mtrue) (lambda _ mempty) empty-assignements)))

;; Configuration - use short timeout
(define default-timeout (b.string->duration "150ms"))
(config.set_smt_timeout pbl (b.mult->duration scale-timeout default-timeout))

;; Run the indistinguishability check
(if (run pbl p1 p2)
  (displayln "success")
  (error "failed memory-cell-simple"))

(displayln (report.print-report (pbl.get-report pbl)))
(save-results "memory-cell-simple" pbl)
