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

(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

;2.4
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
                             (let
                                 ((left (max l))
                                  (right (max r)))
                               (let
                                   ((lv (cadr left))
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
                                    (else left)))))))))))
      (car (max tree)))))
