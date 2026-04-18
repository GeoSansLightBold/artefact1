(provide
  Function? Formula? Sort? Signature? Variable?)


(require-builtin ccsa/ll/variable as var->)
(require-builtin ccsa/ll/formula as f->)
(require-builtin ccsa/ll/function as fun->)
(require-builtin ccsa/ll/sort as sort->)
(require-builtin ccsa/ll/signature as sig->)

(define Variable? var->Variable?)
(define Function? fun->Function?)
(define Formula? f->Formula?)
(define Sort? sort->Sort?)
(define Signature? sig->Signature?)