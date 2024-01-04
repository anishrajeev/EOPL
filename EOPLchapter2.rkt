#lang eopl

;2.1 (Base 16)
#|As the base gets lower it gets slower as more recursive calls
when the base is high there is less recursive calls for pred and succ
|#

(define N 16)

(define zero '())

(define iszero? null?)

(define succ
  (lambda (n)
    (cond
      ((iszero? n) '(1))
      ((eqv? (car n) (- N 1)) (cons 0 (succ (cdr n))))
      (else (cons (+ 1 (car n)) (cdr n))))))

(define pred
  (lambda (n)
    (cond
      ((iszero? n) (eopl:error 'pred "Zero doesn't have a predecessor%"))
      ((eqv? (car n) 0) (cons (- N 1) (pred (cdr n))))
      (else (cons (- (car n) 1) (cdr n))))))

;2.3
(define vector-of
  (lambda (pred)
    (lambda (vector)
      (letrec ((A
                (lambda (v i)
                  (or (eqv? i (vector-length v))
                      (and (pred (vector-ref v i))
                           (A v (+ i 1)))))))
        (A vector 0)))))

;2.4
(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

(define bintree-to-list
  (lambda (tree)
    (cases bintree tree
      (leaf-node (val) (cons 'leaf-node (cons val (quote ()))))
      (interior-node (k l r)
                     (cons 'interior-node
                           (cons k
                                 (cons (bintree-to-list l)
                                       (cons (bintree-to-list r) (quote ())))))))))

;2.5
(define max-interior
  (lambda (tree)
    (letrec
        ((max
          (lambda (tree)
            (cases bintree tree
              (leaf-node (datum)
                         (cons 'null
                               (cons datum (quote ()))))
              (interior-node (k l r)
                             (let*
                                 ((left (max l))
                                  (right (max r))
                                  (lv (cadr left))
                                  (rv (cadr right)))
                               (cond
                                 ((and (eqv? 'null (car left))
                                       (eqv? 'null (car right)))
                                  (cons k (cons (+ lv rv) (quote ()))))
                                 ((eqv? 'null (car left))
                                  (if (> rv (+ rv lv))
                                      right
                                      (cons k (cons (+ rv lv) (quote ())))))
                                 ((eqv? 'null (car right))
                                  (if (> lv (+ rv lv))
                                      left
                                      (cons k (cons (+ rv lv) (quote ())))))
                                 (else
                                  (cond
                                    ((and (>= lv 0) (>= rv 0))
                                     (cons k (cons (+ lv rv) (quote ()))))
                                    ((and (> 0 lv) (> 0 rv))
                                     (if (> lv rv) left right))
                                    ((> 0 lv) right)
                                    (else left))))))))))
      (car (max tree)))))

;2.7
(define list-of
  (lambda (pred)
    (lambda (list)
      (or (null? list)
          (and (pred (car list))
               ((list-of pred) (cdr list)))))))

(define-datatype expression expression?
  (lit-exp
   (datum number?))
  (var-exp
   (id symbol?))
  (if-exp
   (test-exp expression?)
   (true-exp expression?)
   (false-exp expression?))
  (lambda-exp
   (ids (list-of symbol?))
   (body expression?))
  (app-exp
   (rator expression?)
   (rands (list-of expression?)))
  (lex-info
   (id symbol?)
   (depth number?)
   (position number?))
  (free-info
   (id symbol?)))

(define parse
  (lambda (datum)
    (letrec
        ((looper
          (lambda (explist decs)
            (cond
              ((null? explist) (quote ()))
              (else (cons (parser (car explist) decs)
                    (looper (cdr explist) decs))))))
         (member?
          (lambda (var list pos)
            (cond
              ((null? list) #f)
              ((eqv? var (car list)) pos)
              (else (member? var (cdr list) (+ 1 pos))))))
         (find
          (lambda (decs var depth)
            (cond
              ((null? decs) 'free)
              (else
               (let ((member (member? var (car decs) 0)))
                 (if (eqv? member #f)
                     (find (cdr decs) var (+ 1 depth))
                     (cons depth (cons member (quote ())))))))))
         (parser
          (lambda (datum decs)
            (cond
              ((number? datum) (lit-exp datum))
              ((symbol? datum)
               (let ((f (find decs datum 0)))
                 (if (eqv? f 'free)
                     (free-info datum)
                     (lex-info datum
                               (car f)
                               (cadr f)))))
              ((not (pair? datum))
               (eopl:error 'parse
                           "Invalid concrete syntax ~s%" datum))
              ((eqv? (car datum) 'if)
               (if-exp (parser (cadr datum) decs) (parser (caddr datum) decs) (parser (cadddr datum) decs)))
              ((eqv? (car datum) 'lambda)
               (lambda-exp (cadr datum) (parser (caddr datum) (cons (cadr datum) decs))))
              (else (app-exp (parser (car datum) decs)
                             (looper (cdr datum) decs)))))))
      (parser datum (quote ())))))

(define unparse
 (lambda (exp)
   (letrec
       ((A
         (lambda (rands)
           (if (null? rands)
               (quote ())
               (cons (B (car rands)) (A (cdr rands))))))
        (B
         (lambda (exp)
           (cases expression exp
             (lit-exp (datum) datum)
             (var-exp (id) id)
             (if-exp (test-exp true-exp false-exp)
                     (list 'if (B test-exp) (B true-exp) (B false-exp)))
             (lambda-exp (ids body)
                         (list 'lambda ids (B body)))
             (app-exp (rator rands)
                      (cons (B rator) (A rands)))
             (lex-info (id depth position)
                       (cons id (cons ': (cons depth (cons position (quote ()))))))
             (free-info (id)
                        (cons id (cons 'free (quote ()))))))))
     (B exp))))

(define lexical-address
  (lambda (datum)
    (unparse (parse datum))))

;2.8
(define free-vars
  (lambda (datum)
    (letrec
        ((parsed (parse datum))
         (member?
          (lambda (list var)
            (cond
              ((null? list) #f)
              ((eqv? (car list) var) #t)
              (else (member? (cdr list) var)))))
         (merge
          (lambda (s1 s2)
            (cond
              ((null? s1) s2)
              ((member? s2 (car s1)) (merge (cdr s1) s2))
              (else (cons (car s1) (merge (cdr s1) s2))))))
         (loop
          (lambda (list)
            (if (null? list)
                (quote ())
                (merge (answer (car list))
                       (loop (cdr list))))))
         (answer
          (lambda (exp)
            (cases expression exp
              (lit-exp (datum) (quote ()))
              (var-exp (id) (quote ()))
              (if-exp (test true false)
                      (merge (answer test)
                             (merge (answer true)
                                    (answer false))))
              (lambda-exp (ids body)
                          (answer body))
              (app-exp (rator rands)
                       (merge (answer rator) (loop rands)))
              (lex-info (id depth position)
                        (quote ()))
              (free-info (id)
                         (cons id (quote ())))))))
      (answer parsed))))

;2.9, use bunch of cond+if stats to validate data before passing to parser 2 lazy

;2.10
(define all-ids
  (lambda (exp)
    (cases expression exp
      (var-exp (datum) (cons datum (quote ())))
      (lambda-exp (id body) (cons id
                                  (all-ids body)))
      (app-exp (rator rand) (append (all-ids rator) (all-ids rand)))
      (else (quote ())))))

;2.11
;Pretty sure this works, can't rlly test cus of conflicting data-type defns(why can't we reassign them? lol)
(define-datatype extended-expression extended-expression?
  (var-exp2
   (id symbol?))
  (lambda-exp2
   (id symbol?)
   (body extended-expression?))
  (app-exp2
   (rator extended-expression?)
   (rand extended-expression?))
  (lit-exp2
   (datum number?))
  (primapp-exp
   (prim symbol?)
   (exp1 extended-expression?)
   (exp2 extended-expression?)))

(define lambda-calculus-subst
  (lambda (exp subst-exp subst-id)
    (letrec
        ((subst
          (lambda (exp)
            (cases extended-expression exp
              (var-exp2 (id)
                        (if (eqv? id subst-id)
                            subst-exp
                            exp))
              (lambda-exp2 (id body)
                          (cond
                            ((eqv? id (subst-id)) exp)
                            ((eqv? id (subst-exp)) (let ((newid (fresh-id body id)))
                                                     (lambda-exp2 (var-exp2 newid)
                                                                 (subst (lambda-calculus-subst body newid id)))))
                            (else (lambda-exp id (subst body)))))
              (app-exp2 (rator rand)
                       (app-exp2 (subst rator) (subst rand)))
              (lit-exp2 (datum)
                       exp)
              (primapp-exp (prim rand1 rand2)
                           (primapp-exp prim (subst rand1) (subst rand2)))))))
      (subst exp))))

;2.12
(define alpha-convert
  (lambda (exp)
    (cases extended-expression exp
      (lambda-exp2 (id body)
                   (let ((newid (fresh-id body id)))
                     (lambda-exp2 newid (lambda-calculus-subst body id newid))))
      (else 'error))))