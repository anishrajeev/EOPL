#lang eopl

;1.6  and 1.7
(define nth-elt
  (lambda (lst n)
    (if (list? lst)
        (letrec ((A (lambda (lstp np)
                       (if (null? lstp)
                           (eopl:error 'nth-elt
                    "~s doesn't have ~s elements.~%" lst n)
                           (if (zero? np)
                               (car lstp)
                               (A (cdr lstp) (- np 1)))))))
           (A lst n))
        ((eopl:error 'nth-elt
                    "Provide a valid list please.~%")))))

;1.11
#|(define subst
  (lambda (new old slist)
    (if (null? slist)
        (quote ())
        (let ((se (car slist)))
          (if (symbol? se)
              (if (eqv? old se)
                  (cons new (subst new old (cdr slist)))
                  (cons se (subst new old (cdr slist))))
              (cons (subst new old (car slist)) (subst new old (cdr slist))))))))|#

;1.12
(define subst
  (lambda (new old slist)
    (map (lambda (se)
           (if (symbol? se)
              (if (eqv? old se)
                  new
                  se)
              (subst new old se))) slist)))

;1.13
#|
<top-level> ::= <s-list>
<s-list> ::= ({<symbol-expression>}*)
<symbol-expression> ::= <symbol> | <s-list>
|#
(define notate-depth
  (lambda (slist)
    (notate-depth-in-s-list slist 0)))

(define notate-depth-in-s-list
  (lambda (slist d)
    (map (lambda (se)
           (if (symbol? se)
               (list se d)
               (notate-depth-in-s-list se (+ d 1))))
         slist)))

;1.15
(define duple
  (lambda (n x)
    (if (zero? n)
        (quote ())
        (cons x (duple (- n 1) x)))))

(define invert
  (lambda (lst)
    (if (null? lst)
        (quote ())
        (let ((tlist (car lst)))
          (cons (cons (cadr tlist) (car tlist)) (invert (cdr lst)))))))

(define filter-in
  (lambda (pred lst)
    (if (null? lst)
        (quote ())
        (if (pred (car lst))
            (cons (car lst) (filter-in pred (cdr lst)))
            (filter-in pred (cdr lst))))))

(define every?
  (lambda (pred lst)
    (if (null? lst)
        #t
        (and
         (pred (car lst))
         (every? pred (cdr lst))))))

(define exists?
  (lambda (pred lst)
    (if (null? lst)
        #f
        (or
         (pred (car lst))
         (exists? pred (cdr lst))))))

(define vector-index
  (lambda (pred v)
    (letrec ((helper
              (lambda (n)
                (if (zero? n)
                    #f
                    (if (pred (vector-ref v (- n 1)))
                        (- n 1)
                        (helper (- n 1)))))))
      (helper (vector-length v)))))

(define list-set
  (lambda (lst n x)
    (if (zero? n)
        (cons x (cdr lst))
        (cons (car lst) (list-set (cdr lst) (- n 1) x)))))

(define product
  (lambda (los1 los2)
    (letrec
        ((A (lambda (se l1 l2 ans)
              (if (null? l2)
                  (B (cdr l1) los2 ans)
                  (A se l1 (cdr l2) (cons (list se (car l2)) ans)))))
         (B (lambda (l1 l2 ans)
              (if (null? l1)
                  ans
                  (A (car l1) l1 l2 ans)))))
      (B los1 los2 (quote ())))))

(define down
  (lambda (lst)
    (if (null? lst)
        (quote ())
        (cons (list (car lst)) (down (cdr lst))))))

(define vector-append-list
  (lambda (v lst)
    (letrec ((first (lambda (n ans)
                      (if (zero? n)
                          (second (vector-length v) ans lst)
                          (let ()
                            (vector-set! ans (- n 1)
                                              (vector-ref v (- n 1)))
                            (first (- n 1) ans)))))
             (second (lambda (n ans l)
                       (if (null? l)
                           ans
                           (let ()
                             (vector-set! ans n (car l))
                             (second (+ n 1) ans (cdr l)))))))
      (first (vector-length v) (make-vector (+ (length lst) (vector-length v)) 0)))))

;1.16
(define up
  (lambda (lst)
    (letrec ((A (lambda (lst ans)
                  (if (null? lst)
                      ans
                      (if (symbol? (car lst))
                          (A (cdr lst) (cons (car lst) ans))
                          (A (cdr lst) (append (car lst) ans)))))))
      (A (reverse lst) (quote ())))))

(define swapper
  (lambda (s1 s2 slist)
    (letrec ((A (lambda (slist)
                  (if (null? slist)
                      (quote ())
                      (if (symbol? (car slist))
                          (if (eqv? s1 (car slist))
                              (cons s2 (A (cdr slist)))
                              (if (eqv? s2 (car slist))
                                  (cons s1 (A (cdr slist)))
                                  (cons (car slist) (A (cdr slist)))))
                          (cons (A (car slist)) (A (cdr slist))))))))
      (A slist))))

(define count-occurrences
  (lambda (s slist)
    (letrec ((A (lambda (slist)
                  (if (null? slist)
                      0
                      (if (symbol? (car slist))
                          (if (eqv? s (car slist))
                              (+ 1 (A (cdr slist)))
                              (A (cdr slist)))
                          (+ (A (cdr slist)) (A (car slist))))))))
      (A slist))))

(define flatten
  (lambda (slist)
    (if (null? slist)
        (quote ())
        (if (symbol? (car slist))
            (cons (car slist) (flatten (cdr slist)))
            (append (flatten (car slist)) (flatten (cdr slist)))))))

(define merge
  (lambda (lon1 lon2)
    (cond
      ((null? lon1) lon2)
      ((null? lon2) lon1)
      ((< (car lon1) (car lon2)) (cons (car lon1) (merge (cdr lon1) lon2)))
      (else (cons (car lon2) (merge lon1 (cdr lon2)))))))

;1.17
(define path
  (lambda (n bst)
    (letrec ((A (lambda (bst)
                  (cond
                    ((eqv? n (car bst)) (quote ()))
                    ((< n (car bst)) (cons (quote left) (A (cadr bst))))
                    (else (cons (quote right) (A (caddr bst))))))))
      (A bst))))

(define sort
  (lambda (lon)
    (letrec
        ((min (lambda (lst)
                (if (null? (cdr lst))
                    (car lst)
                    (let ((mincdr (min (cdr lst))))
                      (if (< (car lst) mincdr)
                          (car lst)
                          mincdr)))))
      (rember (lambda (lst m)
                (cond
                  ((null? lst) (quote ()))
                  ((eqv? m (car lst)) (cdr lst))
                  (else (cons (car lst) (rember (cdr lst) m))))))
      (answer (lambda (lst)
                (if (null? lst)
                    (quote ())
                    (let ((m (min lst)))
                      (cons m (answer (rember lst m))))))))
      (answer lon))))

(define sort-predicate
  (lambda (predicate lon)
    (letrec
        ((min (lambda (lst)
                (if (null? (cdr lst))
                    (car lst)
                    (let ((mincdr (min (cdr lst))))
                      (if (predicate (car lst) mincdr)
                          (car lst)
                          mincdr)))))
      (rember (lambda (lst m)
                (cond
                  ((null? lst) (quote ()))
                  ((eqv? m (car lst)) (cdr lst))
                  (else (cons (car lst) (rember (cdr lst) m))))))
      (answer (lambda (lst)
                (if (null? lst)
                    (quote ())
                    (let ((m (min lst)))
                      (cons m (answer (rember lst m))))))))
      (answer lon))))

;1.18
;part 1
(define compose
  (lambda (p1 p2)
    (lambda (x)
      (p1 (p2 x)))))

;part 2
(define car&cdr
  (lambda (s slist errvalue)
    (letrec
        ((A (lambda (slist)
                  (cond
                    ((null? slist) errvalue)
                    ((symbol? (car slist))
                     (if (eqv? s (car slist))
                         (quote car)
                         (cons (quote compose) (cons (car&cdr s (cdr slist) errvalue) (cons (quote cdr) (quote ()))))))
                    (else
                     (if (member? (car slist))
                         (cons (quote compose) (cons (car&cdr s (car slist) errvalue) (cons (quote car) (quote ()))))
                         (cons (quote compose) (cons (car&cdr s (cdr slist) errvalue) (cons (quote cdr) (quote ())))))))))
         (member? (lambda (slist)
                    (cond
                      ((null? slist) #f)
                      ((symbol? (car slist))
                       (or (eqv? s (car slist)) (member? (cdr slist))))
                      (else (or (member? (car slist)) (member? (cdr slist))))))))
      (if (not (member? slist))
          errvalue
          (A slist)))))

;part3
(define car&cdr2
  (lambda (s slist errvalue)
    (letrec
        ((A (lambda (slist)
              (cond
                ((null? slist) errvalue)
                ((symbol? (car slist))
                 (if (eqv? s (car slist))
                     (quote car)
                     (append (quote (lambda (x))) (cons (cons (car&cdr2 s (cdr slist) errvalue) (quote ((cdr x)))) (quote ())))))
                (else
                 (if (member? (car slist))
                       (append (quote (lambda (x))) (cons (cons (car&cdr2 s (car slist) errvalue) (quote ((car x)))) (quote ())))
                       (append (quote (lambda (x))) (cons (cons (car&cdr2 s (cdr slist) errvalue) (quote ((cdr x)))) (quote ()))))))))
         (member? (lambda (slist)
                    (cond
                      ((null? slist) #f)
                      ((symbol? (car slist))
                       (or (eqv? s (car slist)) (member? (cdr slist))))
                      (else (or (member? (car slist)) (member? (cdr slist))))))))
      (if (not (member? slist))
          errvalue
          (A slist)))))

;1.19
(define free-vars
  (lambda (exp)
    (letrec
        ((member? (lambda (s set)
                    (cond
                      ((null? set) #f)
                      ((eqv? s (car set)) #t)
                      (else (member? s (cdr set))))))
         (union (lambda (s1 s2)
                  (cond
                    ((null? s1) s2)
                    ((member? (car s1) s2)
                     (union (cdr s1) s2))
                    (else (cons (car s1)
                                (union (cdr s1) s2))))))
         (answer (lambda (exp bound free)
                   (cond
                     ((symbol? exp) (if (member? exp bound)
                                        free
                                        (if (member? exp free) free (cons exp free))))
                     ((eqv? 'lambda (car exp)) (answer (caddr exp) (cons (caadr exp) bound) free))
                     (else (union (answer (car exp) bound free) (answer (cadr exp) bound free)))))))
      (answer exp (quote ()) (quote ())))))

(define bound-vars
  (lambda (exp)
    (letrec
        ((member? (lambda (s set)
                     (cond
                       ((null? set) #f)
                       ((eqv? s (car set)) #t)
                       (else (member? s (cdr set))))))
          (union (lambda (s1 s2)
                   (cond
                     ((null? s1) s2)
                     ((member? (car s1) s2)
                      (union (cdr s1) s2))
                     (else (cons (car s1)
                                 (union (cdr s1) s2))))))
          (answer (lambda (exp bound)
                    (cond
                      ((symbol? exp) bound)
                     ((eqv? 'lambda (car exp))
                      (if (member? (caadr exp) bound)
                          (answer (caddr exp) bound)
                          (answer (caddr exp) (cons (caadr exp) bound))))
                     (else (union (answer (car exp) bound) (answer (cadr exp) bound)))))))
      (answer exp (quote ())))))

;1.20
#|
((lambda (x) y) (lambda (z) w))
This exp's value doesn't depend on w, which is free
|#

;1.21
#|
((lambda (x) y) (lambda (y) y))
y shows up both bound and free
|#

;1.22
(define occurs-free?
  (lambda (var exp)
    (letrec
        ((member?
           (lambda (slist s)
             (cond
               ((null? slist) #f)
               ((eqv? s (car slist)) #t)
               (else (member? (cdr slist) s)))))
         (looper (lambda (var exps)
                   (cond
                     ((null? exps) #f)
                     (else (or (free? var (car exps)) (looper var (cdr exps)))))))
         (free? (lambda (var exp)
                  (cond
                    ((symbol? exp) (eqv? var exp))
                    ((eqv? (car exp) 'lambda) 
                     (and (not (member? (cadr exp) var))
                          (occurs-free? var (caddr exp))))
                    (else (looper var exp))))))
      (free? var exp))))

(define occurs-bound?
  (lambda (var exp)
    (letrec
        ((member?
           (lambda (slist s)
             (cond
               ((null? slist) #f)
               ((eqv? s (car slist)) #t)
               (else (member? (cdr slist) s)))))
         (looper (lambda (var exps)
                   (cond
                     ((null? exps) #f)
                     (else (or (bound? var (car exps)) (looper var (cdr exps)))))))
         (bound? (lambda (var exp)
                   (cond
                     ((symbol? exp) #f)
                     ((eqv? (car exp) 'lambda)
                      (or (member? (cadr exp) var) (bound? var (caddr exp))))
                     (else (looper var exp))))))
      (bound? var exp))))

;1.31
(define lexical-address
  (lambda (exp)
    (letrec
        ((finder (lambda (scopes var num)
                   (cond
                     ((null? scopes) 'free)
                     (else
                      (let ((m (member? (car scopes) var 0)))
                        (if (eqv? m #f)
                            (finder (cdr scopes) var (+ 1 num))
                            (cons num (cons m (quote ())))))))))
         (member? (lambda (slist var num)
                    (cond
                      ((null? slist) #f)
                      ((eqv? (car slist) var) num)
                      (else (member? (cdr slist) var (+ 1 num))))))
         (looper (lambda (explist scopes)
                   (cond
                     ((null? explist) (quote ()))
                     (else (cons (answer (car explist) scopes) (looper (cdr explist) scopes))))))
         (answer (lambda (exp scopes)
                   (cond
                     ((symbol? exp)
                      (let ((found (finder scopes exp 0)))
                        (if (eqv? found 'free)
                            (cons exp (cons 'free (quote ())))
                            (cons exp (cons ': (cons (car found) (cons (cadr found) (quote ()))))))))
                     ((eqv? (car exp) 'lambda) (cons 'lambda (cons (cadr exp)
                                                                   (cons (answer (caddr exp) (cons (cadr exp) scopes))
                                                                         (quote ())))))
                     ((eqv? (car exp) 'if) (cons 'if (cons (answer (cadr exp) scopes)
                                                      (cons (answer (caddr exp) scopes)
                                                            (cons (answer (cadddr exp) scopes)
                                                                  (quote ()))))))
                     ((looper exp scopes))))))
      (answer exp (quote ())))))

;1.32
(define un-lexical-address
  (lambda (exp)
    (letrec
        ((getter (lambda (scopes depth pos)
                   (cond
                     ((null? scopes) #f)
                     ((zero? depth) (get (car scopes) pos))
                     (else (getter (cdr scopes) (- depth 1) pos)))))
         (get (lambda (varlist pos)
                (cond
                  ((null? varlist) #f)
                  ((zero? pos) (car varlist))
                  (else (get (cdr varlist) (- pos 1))))))
         (upwards (lambda (scopes depth var)
                    (cond
                      ((null? scopes) #f)
                      ((zero? depth) #t)
                      ((member? (car scopes) var) #f)
                      (else (upwards (cdr scopes) (- depth 1) var)))))
         (member?
           (lambda (slist s)
             (cond
               ((null? slist) #f)
               ((eqv? s (car slist)) #t)
               (else (member? (cdr slist) s)))))
         (looper (lambda (explist scopes)
                   (cond
                     ((null? explist) (quote ()))
                     (else (cons (answer (car explist) scopes) (looper (cdr explist) scopes))))))
         (valid? (lambda (exp scopes)
                   (cond
                     ((null? exp) #t)
                     ((eqv? (car exp) ':)
                      (let ((got (getter scopes (cadr exp) (caddr exp))))
                        (if (eqv? got #f)
                            #f
                            (upwards scopes (cadr exp) got))))
                     ((eqv? (car exp) 'lambda) (valid? (caddr exp) (cons (cadr exp) scopes)))
                     ((eqv? (car exp) 'if) (and
                                            (valid? (cadr exp) scopes)
                                            (and
                                             (valid? (caddr exp) scopes)
                                             (valid? (cadddr exp) scopes))))
                     ((symbol? (car exp)) #t)
                     (else (and (valid? (car exp) scopes) (valid? (cdr exp) scopes))))))
         (answer (lambda (exp scopes)
                   (cond
                     ((eqv? (car exp) ':) (getter scopes (cadr exp) (caddr exp)))
                     ((and (symbol? (car exp)) (eqv? (cadr exp) 'free)) (car exp))
                     ((eqv? (car exp) 'lambda) (cons 'lambda (cons (cadr exp) (cons (answer (caddr exp) (cons (cadr exp) scopes)) (quote ())))))
                     ((eqv? (car exp) 'if) (cons 'if (cons (answer (cadr exp) scopes)
                                                      (cons (answer (caddr exp) scopes)
                                                            (cons (answer (cadddr exp) scopes)
                                                                  (quote ()))))))
                     (else (looper exp scopes))))))
      (if (valid? exp (quote ())) (answer exp (quote ())) #f))))