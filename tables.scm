(load "mk/mk.scm")

;; version that uses implicit subsetness, rather than following the semantics in the paper

(define evalo
  (lambda (exp val)
    (eval-expo exp '() val)))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((numbero exp) (== exp val))
      ((symbolo exp) (lookupo exp env val))
      ((fresh (rator rand table a)
         (== `(,rator ,rand) exp)
         (eval-expo rand env a)
         (table-lookupo a table val)
         (eval-expo rator env table)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (table-all x body env val))))))

;; should be a constraint that depends on eval-expo
(define table-all
  (lambda (x body env table)
    (conde
      ((== '() table))
      ((fresh (key value rest)
         ;; table extension, and enforcing setness, needs to be lazy
         (== `((,key . ,value) . ,rest) table)

         ;; keep setness -- make lazy
         ;; also need to ignore order to make it set-like
;         (not-in-tableo key rest)

         ;; intent of this entire relation/constraint
         ;; every pair <key,value> in table satisfies this:
         (eval-expo body `((,x . ,key) . ,env) value)
         
         (table-all x body env rest))))))

(define not-in-tableo
  (lambda (x env)
    (conde
      ((== '() env))
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-tableo x rest))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest)))
      ((== '() env)))))

(define proper-listo
  (lambda (exp env val)
    (conde
      ((== '() exp)
       (== '() val))
      ((fresh (a d t-a t-d)
         (== `(,a . ,d) exp)
         (== `(,t-a . ,t-d) val)
         (eval-expo a env t-a)
         (proper-listo d env t-d))))))

(define table-lookupo
  (lambda (x env t)
    (fresh (rest y v)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (table-lookupo x rest t))))))

(define lookupo
  (lambda (x env t)
    (fresh (rest y v)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

#!eof

(run 1 (q) (evalo 'x q))
=>
()

(run* (q) (evalo '1 q))
=>
((1))

(run 1 (q) (evalo '((lambda (x) 2) 1) q))
=>
2

(run* (q) (evalo '((lambda (x) 2) 1) q))
=>
2

(run* (q) (evalo '((lambda (x) x) 1) q))
 => 1

(run 1 (q) (evalo '(lambda (x) x) q))
=>
(), ((1 . 1)), ((0 . 0) (1 . 1)), (() . ())

((lambda (x) (x x)) (lambda (x) (x x)))  diverge
