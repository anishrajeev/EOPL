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

(define fresh-id
  (lambda (exp s)
    (let ((syms (all-ids exp)))
      (letrec
          ((loop (lambda (n)
                   (let ((sym (string->symbol
                               (string-append s
                                              (number->string n)))))
                     (if (memv sym syms) (loop (+ n 1)) sym)))))
        (loop 0)))))

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

(define beta-convert
  (lambda (exp)
    (cases extended-expression exp
      (app-exp2 (rator rand)
                (cases extended-expression rand
                  (lambda-exp2 (id body)
                               (lambda-calculus-subst rator body id))
                  (else 'N/A)))
      (else 'N/A))))

(define eta-convert
  (lambda (exp)
    (letrec
        ((free?
          (lambda (exp var)
            (cases extended-expression exp
              (var-exp2 (id) (eqv? id var))
              (lambda-exp2 (id body)
                           (and (not (eqv? id var))
                                (free? body var)))
              (app-exp2 (rator rand)
                        (or (free? rator)
                            (free? rand)))
              (lit-exp2 (num) #f)
              (primapp-exp (prim rand1 rand2) (or (free? rand1 var)
                                                  (free? rand2 var))))))
         (answer
          (lambda (exp)
            (cases extended-expression exp
              (lambda-exp2 (id body)
                           (cases extended-expression body
                             (app-exp2 (rator rand)
                                       (if (eqv? rand id)
                                           (if (free? rator id) exp rator)
                                           exp))
                             (else 'N/A)))
              (else 'N/A)))))
      (answer exp))))

;2.13
;Way 2 lazy for this ngl, its super repetitive...

;2.14
#|
empty stack = ()
push element e onto stack s is just (cons e s)
pop element from stack is just car and returns cdr
top returns car s and keeps stack as s
empty-stack? is simply null?
stacks are equal to lists
(1 2 3 4) is an example of a stack with 1 ontop and 4 on bottom
|#

;2.15
(define empty-stack (lambda () (quote ())))

(define push
  (lambda (stack elem)
    (lambda ()
      (cons elem (stack)))))

(define pop
  (lambda (stack)
    (lambda ()
      (cdr (stack)))))

(define top
  (lambda (stack)
    (car (stack))))

(define empty-stack?
  (lambda (stack)
    (null? (stack))))

;2.16
(define list-find-last-position
  (lambda (list pred)
    (cond
      ((null? list) #f)
      (else
       (let ((future (list-find-last-position (cdr list) pred)))
         (cond
           ((number? future) (+ 1 future))
           ((pred (car list)) 0)
           (else #f)))))))

;2.17
;Is this the best way to go arnd this? I have to think, may update l8r
;but for now this works fine
(define empty-env
  (lambda ()
    (lambda (function sym)
      (function sym
                (lambda (sym) (eopl:error 'apply-value "~s has no binding%" sym))
                (lambda (sym) #f)))))

(define extend-env
  (lambda (syms vals env)
    (lambda (function sym)
      (function
       sym
       (lambda (sym)
         (let ((pos (list-find-last-position syms (lambda (s) (eqv? s sym)))))
           (if (number? pos)
               (list-ref vals pos)
               (apply-value env sym))))
       (lambda (sym)
         (if (memv sym syms)
             #t
             (apply-association env sym)))))))

(define apply-value
  (lambda (env sym)
    ((env (lambda (x y z) y) sym) sym)))

(define apply-association
  (lambda (env sym)
    ((env (lambda (x y z) z) sym) sym)))

(define has-association?
  (lambda (env sym)
    (apply-association env sym)))

;2.18
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

(define scheme-value? (lambda (v) #t))

(define environment-to-list
  (lambda (env)
    (cases environment env
      (empty-env-record () '(empty-env-record))
      (extended-env-record (syms vals env)
                           (cons 'extended-env-record (cons syms (cons vals (cons (environment-to-list env) (quote ())))))))))

;2.19
(define-datatype stack stack?
  (ast-empty-stack)
  (ast-full-stack
   (element (lambda (v) #t))
   (rest stack?)))

(define ast-push
  (lambda (stk elem)
    (ast-full-stack elem stk)))

(define ast-pop
  (lambda (stk)
    (cases stack stk
      (ast-empty-stack () (eopl:error 'ast-pop "Can't pop on an empty stack%"))
      (ast-full-stack (elem rest) rest))))

(define ast-top
  (lambda (stk)
    (cases stack stk
      (ast-empty-stack () (eopl:error 'ast-pop "There's no top on an empty stack%"))
      (ast-full-stack (elem rest) elem))))

(define ast-empty-stack?
  (lambda (stk)
    (cases stack stk
      (ast-empty-stack () #t)
      (ast-full-stack (elem rest) #f))))

;2.20
(define has-association-ast?
  (lambda (sym env)
    (cases environment env
      (empty-env-record () #f)
      (extended-env-record (syms vals env)
                           (or (memv sym syms)
                               (has-association-ast? sym env))))))

;2.21: The empty environment, its represented as (() ())

;2.22 NGL this confusese me... 2-element rib as if we didn't already do that earlier in the book?

;2.23
(define empty-env-rib '(() ()))

(define extend-env-rib
  (lambda (syms vals env)
    (cons
     (append syms (car env))
     (append vals (cdr env)))))

(define apply-env-rib
  (lambda (sym env)
    (let ((index (list-find-last-position (car env) (lambda (x) (eqv? x sym)))))
      (if (eqv? index #f)
          (eopl:error 'apply-env-rib "~s isn't associated with a value in this environment%" sym)
          (list-ref (cadr env) index)))))
;2.24
(define constant?
  (lambda (v) (or (string? v)
                  (or (number? v)
                      (or (boolean? v)
                          (null? v))))))

(define-datatype term term?
  (var-term
   (id symbol?))
  (constant-term
   (datum constant?))
  (app-term
   (terms (list-of term?))))

(define empty-subst-p
  (lambda ()
    (lambda (v) (var-term v))))

(define extend-subst-p
  (lambda (i t s)
    (lambda (v)
      (if (eqv? i v) t (apply-subst-p s v)))))

(define apply-subst-p
  (lambda (s v)
    (s v)))

(define-datatype subst-ast subst-ast?
  (empty-subst-ast)
  (extended-subst-ast
   (v (lambda (v) #t))
   (t term?)
   (subst subst-ast?)))

(define extend-subst-ast
  (lambda (i t s)
    (extended-subst-ast i t s)))

(define apply-subst-ast
  (lambda (s i)
    (cases subst-ast s
      (empty-subst-ast () i)
      (extended-subst-ast (v t subst)
                          (if (eqv? i v) t (apply-subst-ast subst i))))))

(define subst-in-terms-ast
  (lambda (t s)
    (letrec
        ((looper
          (lambda (list)
            (if (null? list) (quote ()) (cons (ans (car list)) (looper (cdr list))))))
         (ans
          (lambda (t s)
            (cases term t
              (var-term (id) (apply-subst-ast s id))
              (constant-term (c) c)
              (app-term (terms) (looper terms))))))
      (ans t s))))

(define subst-in-terms-p
  (lambda (t s)
    (letrec
        ((looper
          (lambda (list)
            (if (null? list) (quote ()) (cons (ans (car list)) (looper (cdr list))))))
         (ans
          (lambda (t s)
            (cases term t
              (var-term (id) (apply-subst-p s id))
              (constant-term (c) c)
              (app-term (terms) (looper terms))))))
      (ans t s))))

;2.25
(define unit-subst
  (lambda (i t)
    (lambda (v)
      (if (eqv? i v) t (var-term t)))))

(define compose-substs
  (lambda (s1 s2)
    (lambda (v)
      (apply-subst-p s2 (apply-subst-p s1 v)))))

;Without occurs check t = a and u = (1 2 a)
;The subst would be a |-> (1 2 a) but
;subst t = (1 2 a) but subst u has no value

;2.26
(define-datatype reference reference?
  (a-ref
   (position integer?)
   (vec vector?)))

(define cell
  (lambda (arg)
    (let ((ref (a-ref 0 (vector arg))))
      (letrec
          ((cell?
            (lambda ()
              (reference? ref)))
           (contents
            (lambda ()
              (cases reference ref
                (a-ref (p v) (vector-ref v p)))))
           (setcell
            (lambda (val)
              (cases reference ref
                (a-ref (p v) (vector-set! v p val))))))
        (vector cell? contents setcell)))))

(define cell-get-cell? (lambda (c) (vector-ref c 0)))
(define cell-get-contents (lambda (c) (vector-ref c 1)))
(define cell-get-setcell (lambda (c) (vector-ref c 2)))