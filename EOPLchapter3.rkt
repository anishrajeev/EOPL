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
               null-prim)))

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
          (eval-program ast)
          (eopl:error 'run "Wrong amount of arguments in 1 or more statements%")))))
#|
HERE IS THE SIMPLE INTERPRETER PROVIDED
----------------------------------------
|#

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (primapp-exp (prim rands)
                   (let ((args (eval-rands rands env)))
                     (apply-primitive prim args env)))
      (emptylist-exp () (quote ()))
      (if-exp (cond true false)
              (if (true-value? (eval-expression cond env))
                  (eval-expression true env)
                  (eval-expression false env))))))

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
      (equal-prim () (if (eqv? (car args) (cadr args)) 1 0))
      (zero-prim () (if (zero? (car args)) 1 0))
      (greater-prim () (if (> (car args) (cadr args)) 1 0))
      (null-prim () (if (null? (car args)) 1 0)))))

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
              (else (+ 1 (list-index (cdr list) sym)))))))
      (lambda (sym)
        (let ((index (list-index syms sym)))
          (if (number? index) (list-ref vals index) (apply-env env sym)))))))

(define apply-env
  (lambda (env sym)
    (env sym)))

(define init-env
  (lambda ()
    (extend-env
     '(i v x)
     '(1 5 10)
     (empty-env))))

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
                                  (null-prim () (= (length r) 1))))
                   (emptylist-exp () #t)
                   (if-exp (a b c) #t))))))

