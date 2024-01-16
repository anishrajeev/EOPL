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
    (primitive ("+")
               add-prim)
    (primitive ("-")
               subtract-prim)
    (primitive ("*")
               mult-prim)
    (primitive ("add1")
               incr-prim)
    (primitive ("sub1")
               decr-prim)))

(define scan&parse
  (sllgen:make-string-parser
   scanner-3-1
   grammar-3-1))

(sllgen:make-define-datatypes scanner-3-1 grammar-3-1)

#|
END OF DEFINITIONS
-------------------------------------------------
|#

;3.1
(define list-of
  (lambda (pred)
    (lambda (list)
      (or (null? list)
          (and (pred (car list))
               ((list-of pred) (cdr list)))))))

#|(define-datatype program program?
  (a-program
   (exp expression?)))

(define-datatype expression expression?
  (lit-exp
   (datum number?))
  (var-exp
   (id symbol?))
  (primapp-exp
   (prim primitive?)
   (rands (list-of expression?))))

(define-datatype primitive primitive?
  (add-prim)
  (subtract-prim)
  (mult-prim)
  (incr-prim)
  (decr-prim))|#

(define foldr
  (lambda (list map accum base)
    (if (null? list)
        base
        (accum (map (car list)) (foldr (cdr list) map accum base)))))

(define program-to-list
  (lambda (ast)
    (cond
      ((program? ast)
       (cases program ast
         (a-program (exp) (cons 'a-program (cons (program-to-list exp) (quote ()))))))
      ((expression? ast)
       (cases expression ast
         (lit-exp (datum) (list 'lit-exp datum))
         (var-exp (id) (list 'var-exp id))
         (primapp-exp (prim rands)
                      (cons 'primapp-exp
                      (cons (program-to-list prim)
                            (cons (foldr rands program-to-list cons (quote ()))
                                  (quote ())))))))
      ((primitive? ast)
       (cases primitive ast
         (add-prim () '(add-prim))
         (subtract-prim () '(subtract-prim))
         (mult-prim () '(mult-prim))
         (incr-prim () '(incr-prim))
         (decr-prim () '(decr-prim))))
      (else (eopl:error 'program-to-list "Parsing error; ast has undefined datatypes%")))))

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
                     (apply-primitive prim args))))))

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

(define apply-primitive
  (lambda (prim args)
    (cases primitive prim
      (add-prim () (+ (car args) (cadr args)))
      (subtract-prim () (- (car args) (cadr args)))
      (mult-prim () (* (car args) (cadr args)))
      (incr-prim () (+ (car args) 1))
      (decr-prim () (- (car args) 1)))))

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
END OF DEFINITION
--------------------------------------------------------------------------------
|#

;3.2 No this shouldn't as we don't ever reassign anything and there
;is no possible ambiguity of semantics(i.e. there is no ambiguity between
;what to do first, we first evaluate sub exp then the main... currently
;it is evaluated by a dfs kinda approach that goes deeper first

;3.3
(define parse-program
  (lambda (data)
    (letrec
        ((parse
          (lambda (data)
            (cond
              ((number? data) (lit-exp data))
              ((symbol? data) (var-exp data))
              ((eqv? (car data) '+) (primapp-exp (add-prim) (foldr (cdr data) parse cons (quote ()))))
              ((eqv? (car data) '-) (primapp-exp (subtract-prim) (foldr (cdr data) parse cons (quote ()))))
              ((eqv? (car data) '*) (primapp-exp (mult-prim) (foldr (cdr data) parse cons (quote ()))))
              ((eqv? (car data) 'add1) (primapp-exp (incr-prim) (foldr (cdr data) parse cons (quote ()))))
              ((eqv? (car data) 'sub1) (primapp-exp (decr-prim) (foldr (cdr data) parse cons (quote ())))))))
         (user
          (lambda ()
            (a-program (parse data)))))
      (user))))

;3.7
