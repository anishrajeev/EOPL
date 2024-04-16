#lang eopl
#|
SCANNER AND GRAMMAR DEFINITIONS FOR SLLGEN
-------------------------------------------------
|#

(define scanner-3-1
  '((white-sp
     (whitespace) skip)
    (comment
     ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "?"))) symbol)
    (number
     (digit (arbno digit)) number)))

(define grammar-3-1
  '((program
     (expression)
     a-program)
    (expression
     (number)
     lit-exp)
    (expression
     (identifier)
     var-exp)
    (expression
     (primitive "(" (separated-list expression ",") ")")
     primapp-exp)
    (expression
     ("emptylist")
     emptylist-exp)
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    (expression
     ("cond" (arbno expression expression) "end")
     cond-exp)
    (expression
     ("let" (arbno identifier "=" expression) "in" expression)
     let-exp)
    (expression
     ("unpack" (arbno identifier) "=" expression "in" expression)
     unpack-exp) 
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     app-exp)
    (expression
     ("lexvaryoucan'tmatchthis" number)
     lexvar-exp)
    (primitive ("+")
               add-prim)
    (primitive ("-")
               subtract-prim)
    (primitive ("*")
               mult-prim)
    (primitive ("add1")
               incr-prim)
    (primitive ("sub1")
               decr-prim)
    (primitive ("print")
               print-prim)
    (primitive ("minus")
               minus-prim)
    (primitive ("cons")
               cons-prim)
    (primitive ("car")
               car-prim)
    (primitive ("cdr")
               cdr-prim)
    (primitive ("list")
               list-prim)
    (primitive ("setcar")
               setcar-prim)
    (primitive ("equal?")
               equal-prim)
    (primitive ("zero?")
               zero-prim)
    (primitive ("greater?")
               greater-prim)
    (primitive ("null?")
               null-prim)
    (primitive ("eq?")
               eq-prim)))

(define-datatype procval procval?
  (closure
   (argnum number?)
   (body expression?)
   (env (lambda (x) #t))))

(define apply-proc
  (lambda (proc args)
    (cases procval proc
      (closure (argnum body env)
                 (if (eqv? argnum (length args))
                     (eval-expression body (extend-nameless-env args env))
                     (eopl:error 'apply-proc "Wrong number of arguments fed to procedure%"))))))

(define scan&parse
  (sllgen:make-string-parser
   scanner-3-1
   grammar-3-1))

(define true-value?
  (lambda (x)
    (not (zero? x))))

(sllgen:make-define-datatypes scanner-3-1 grammar-3-1)

(define run
  (lambda (x)
    (let ((ast (scan&parse x)))
      (if (validate-ast ast)
          (eval-program (lexicald ast))
          (eopl:error 'run "Wrong amount of arguments in 1 or more statements%")))))
#|
HERE IS THE SIMPLE INTERPRETER PROVIDED
----------------------------------------
|#

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body empty-nameless-env)))))

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) 0)
      (primapp-exp (prim rands)
                   (let ((args (eval-rands rands env)))
                     (apply-primitive prim args env)))
      (emptylist-exp () (quote ()))
      (if-exp (cond true false)
              (if (true-value? (eval-expression cond env))
                  (eval-expression true env)
                  (eval-expression false env)))
      (cond-exp (test-exps condseq-exps)
                (if (null? test-exps)
                    0
                    (if (true-value? (eval-expression (car test-exps) env))
                        (eval-expression (car condseq-exps) env)
                        (eval-expression (cond-exp (cdr test-exps) (cdr condseq-exps)) env))))
      (let-exp (ids rands body)
               (let ((args (eval-rands rands env)))
                 (eval-expression body (extend-nameless-env args env))))
      (unpack-exp (ids list body)
                  (let ((args (eval-expression list env)))
                    (if (eqv? (length args) (length ids))
                        (eval-expression body (extend-nameless-env args env))
                        (eopl:error 'eval-expression "Wrong number of arguments given to unpack%"))))
      (proc-exp (ids body)
                (closure (length ids) body env))
      (app-exp (rator rands)
               (let ((pclosure (eval-expression rator env))
                     (args (eval-rands rands env)))
                 (if (procval? pclosure)
                     (apply-proc pclosure args)
                     (eopl:error 'eval-expression "Tried to apply paramters to the non procedure ~s%" rator))))
      (lexvar-exp (d) (if (eqv? -1 d)
                          (eopl:error 'eval-expression "Couldn't find variable%")
                          (apply-nameless-env env d))))))

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

(define apply-primitive
  (lambda (prim args env)
    (cases primitive prim
      (add-prim () (+ (car args) (cadr args)))
      (subtract-prim () (- (car args) (cadr args)))
      (mult-prim () (* (car args) (cadr args)))
      (incr-prim () (+ (car args) 1))
      (decr-prim () (- (car args) 1))
      (print-prim () (let ()
                       (display (car args))
                       1))
      (minus-prim () (* -1 (car args)))
      (cons-prim () (cons (car args) (cadr args)))
      (car-prim () (car (car args)))
      (cdr-prim () (cdr (car args)))
      (list-prim () args)
      (setcar-prim () (cons (cadr args) (cdar args)))
      (equal-prim () (if (= (car args) (cadr args)) 1 0))
      (zero-prim () (if (zero? (car args)) 1 0))
      (greater-prim () (if (> (car args) (cadr args)) 1 0))
      (null-prim () (if (null? (car args)) 1 0))
      (eq-prim () (if (= (car args) (cadr args)) 1 0)))))

(define empty-env
  (lambda ()
    (lambda (sym)
      (eopl:error 'apply-value "~s has no binding%" sym))))

(define extend-env
  (lambda (syms vals env)
    (letrec
        ((list-index
          (lambda (list sym)
            (cond
              ((null? list) #f)
              ((eqv? (car list) sym) 0)
              (else
               (let ((rest (list-index (cdr list) sym)))
                 (if (number? rest) (+ 1 rest) #f)))))))
      (lambda (sym)
        (let ((index (list-index syms sym)))
          (if (number? index) (list-ref vals index) (apply-env env sym)))))))

(define index
  (lambda (lst val i)
    (cond
      ((null? lst) -1)
      ((eq? (car lst) val) i)
      (else (index (cdr lst) val (+ i 1))))))

(define apply-env
  (lambda (env sym)
    (env sym)))

(define init-env
  (lambda ()
    (empty-env)))

(define empty-nameless-env '())

(define extend-nameless-env
  (lambda (vals env)
    (append vals env)))

(define apply-nameless-env
  (lambda (env d)
    (list-ref env d)))

#|
END OF DEFINITIONS
-------------------------------------------------
|#
(define list-of
  (lambda (predicate)
    (lambda (lst)
      (cond
        ((null? lst) #t)
        ((predicate (car lst)) ((list-of predicate) (cdr lst)))
        (else #f)))))

;3.1
#|(define program-to-list
  (lambda (exp)
    (cases program exp
        (a-program (exp)
                   (expression-to-list exp)))))
(define expression-to-list
  (lambda (exp)
    (cases expression exp
      (lit-exp (n) (list 'lit-exp n))
      (var-exp (s) (list 'var-exp s))
      (primapp-exp (p r) (list 'primapp-exp p (map (lambda (rand) expression-to-list rand) r))))))

;3.3
(define parse-program
  (lambda (data)
    (letrec
        ((parse
          (lambda (data)
            (cond
              ((number? data) (lit-exp data))
              ((symbol? data) (var-exp data))
              ((eqv? (car data) '+) (primapp-exp (add-prim) (map parse (cdr data))))
              ((eqv? (car data) '-) (primapp-exp (subtract-prim) (map parse (cdr data))))
              ((eqv? (car data) '*) (primapp-exp (mult-prim) (map parse (cdr data))))
              ((eqv? (car data) 'add1) (primapp-exp (incr-prim) (map parse (cdr data))))
              ((eqv? (car data) 'sub1) (primapp-exp (decr-prim) (map parse (cdr data))))))))
      (a-program (parse data)))))|#

;3.9
(define validate-ast
  (lambda (ast)
    (cases program ast
      (a-program (exp)
                 (cases expression exp
                   (lit-exp (n) #t)
                   (var-exp (n) #t)
                   (primapp-exp (p r)
                                (cases primitive p
                                  (add-prim () (= (length r) 2))
                                  (subtract-prim () (= (length r) 2))
                                  (mult-prim () (= (length r) 2))
                                  (incr-prim () (= (length r) 1))
                                  (decr-prim () (= (length r) 1))
                                  (print-prim () (= (length r) 1))
                                  (minus-prim () (= (length r) 1))
                                  (cons-prim () (= (length r) 2))
                                  (car-prim () (= (length r) 1))
                                  (cdr-prim () (= (length r) 1))
                                  (list-prim () #t)
                                  (setcar-prim () (= (length r) 2))
                                  (equal-prim () (= (length r) 2))
                                  (zero-prim () (= (length r) 1))
                                  (greater-prim () (= (length r) 2))
                                  (null-prim () (= (length r) 1))
                                  (eq-prim () (= (length r) 2))))
                   (emptylist-exp () #t)
                   (if-exp (a b c) #t)
                   (cond-exp (a b) #t)
                   (let-exp (a b c) #t)
                   (unpack-exp (a b c) #t)
                   (proc-exp (ids body) #t)
                   (app-exp (rator rands) #t)
                   (lexvar-exp (d) #t))))))

;factorial function
;(run "let fact = proc (n, f) if zero? (n) then 1 else * (n, (f - (n, 1) f)) in (fact 5 fact)")

;even odd function
;(run "let even = proc (n, o, e) if zero? (n) then 1 else (o -(n, 1) o e) odd = proc (n, o, e) if zero? (n) then 0 else (e -(n, 1) o e) in (even 13 odd even)")

(define lexicald
  (lambda (prog)
    (cases program prog
      (a-program (exp) (a-program (lexicald-exp exp '()))))))

(define lexicald-exp
  (lambda (exp env)
    (cases expression exp
      (lit-exp (n) (lit-exp n))
      (var-exp (v) (lexvar-exp (index env v 0)))
      (primapp-exp (p r) (primapp-exp p (map (lambda (x) (lexicald-exp x env)) r)))
      (emptylist-exp () emptylist-exp)
      (if-exp (a b c) (if-exp (lexicald-exp a env) (lexicald-exp b env) (lexicald-exp c env)))
      (cond-exp (a b) (cond-exp (lexicald-exp a env) (lexicald-exp b env)))
      (let-exp (ids rands body)
               (let ((eenv (append ids env)))
                 (let-exp ids
                          (map (lambda (x) (lexicald-exp x env)) rands)
                          (lexicald-exp body eenv))))
      (unpack-exp (ids vals body)
                  (unpack-exp ids
                              (map (lambda (val) (lexicald-exp val env)) vals)
                              (lexicald-exp body (append ids env))))
      (proc-exp (ids body) (proc-exp ids (lexicald-exp body (append ids env))))
      (app-exp (appl args) (app-exp (lexicald-exp appl env) (map (lambda (x) (lexicald-exp x env)) args)))
      (lexvar-exp (d) (lexvar-exp (d))))))