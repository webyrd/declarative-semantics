(load "pmatch.scm")
(load "mk/mk.scm")
(load "mk/test-check.scm")

;; version with support for enough forms for append

(define evalo
  (lambda (exp val)
    (eval-expo exp '() val)))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((numbero exp) (== exp val))
      ((== `(quote ,val) exp)
       (not-in-envo 'quote env))
      ((fresh (aexp dexp aval dval)
          (== `(cons ,aexp ,dexp) exp)
          (== val `(,aval . ,dval))
          (not-in-envo 'cons env)
          (eval-expo aexp env aval)
          (eval-expo dexp env dval)))
      ((fresh (pexp pval dval)
          (== `(car ,pexp) exp)
          (== pval `(,val . ,dval))
          (not-in-envo 'car env)
          (eval-expo pexp env pval)))
      ((fresh (pexp pval aval)
          (== `(cdr ,pexp) exp)
          (== pval `(,aval . ,val))
          (not-in-envo 'cdr env)
          (eval-expo pexp env pval)))
      ((fresh (lexp lval)
          (== `(null? ,lexp) exp)
          (not-in-envo 'null? env)
          (eval-expo lexp env lval)
          (conde
            ((== val #t) (== lval '()))
            ((== val #f) (fresh (a d) (== lval `(,a . ,d)))))))
      ((fresh (e1 e2 e3 bval)
          (== `(if ,e1 ,e2 ,e3) exp)
          (not-in-envo 'if env)
          (eval-expo e1 env bval)
          (conde
            ((== bval #t) (eval-expo e2 env val))
            ((== bval #f) (eval-expo e3 env val)))))
      ((symbolo exp)
       (fresh (lv)
         (lookupo exp env lv)
         (subseto val lv)))
      ((fresh (rator rand table-val rand-v table a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(table . ,table))
         (table-lookupo a table table-val)
         (eval-expo rand env rand-v)
         (subseto a rand-v)
         (subseto val table-val)))
      ((fresh (x body table-list)
         (== `(lambda (,x) ,body) exp)
         (== `(table . ,table-list) val)
         (symbolo x)
         (not-in-envo 'lambda env)
         (table-all x body env table-list))))))

(define subseto
  (lambda (s1 s2)
    (conde
      ((numbero s1) (numbero s2) (== s1 s2))
      ((fresh (l1 l2)
          (== s1 `(table . ,l1))
          (== s2 `(table . ,l2))
          (list-subseto l1 l2)))
      ((== s1 s2) (listo s1)))))

(define list-subseto
  (lambda (s1 s2)
    (conde
      ((== '() s1))
      ((fresh (h1 h2 t1 t2)
         (== `(,h1 . ,t1) s1)
         (== `(,h2 . ,t2) s2)
         (conde
           ((== h1 h2)
            (list-subseto t1 t2))
           ((=/= h1 h2)
            (list-subseto s1 t2))))))))

(define listo
  (lambda (l)
    (conde
      ((== l '()))
      ((fresh (a d)
          (== l `(,a . ,d))
          (listo d))))))

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

(define rec
  '(lambda (!)
     (lambda (x)
       ((! !) x))))

(define append-defn
 '(lambda (!)
    (lambda (l1)
      (lambda (l2)
        (if (null? l1) l2
          (cons (car l1) (((! !) (cdr l1)) l2)))))))

(define append-proc `(,rec ,append-defn))

(define a-list '(quote (1 2)))
(define another-list '(quote (3 4 5)))

(define append-call `((,append-proc ,a-list) ,another-list))

(define append-kont
  '(lambda (k)
     (lambda (l1)
       (lambda (l2)
         (if (null? l1) l2
           (cons (car l1) ((k (cdr l1)) l2)))))))

(define kons
  '(lambda (x)
     (lambda (y)
       (cons x y))))

(define kons-1 `(,kons 1))

;;; tests

(test 'subseto-1
  (run* (q) (list-subseto '(1 2) '(1 2 3)))
  '((_.0)))

(test 'subseto-2
  (run* (q) (list-subseto '(1 2) '(0 1 2 3)))
  '((_.0)))

(test 'subseto-3
  (run* (q) (list-subseto '(1 2) '(0 () 1 2 3)))
  '((_.0)))

(test 'subseto-4
  (run* (q) (list-subseto '(() 1 2) '(0 () 1 2 3)))
  '((_.0)))

(test 'subseto-5
  (run* (q) (list-subseto '(() 1 2) '(() 0 1 2 3)))
  '((_.0)))

(test 'subseto-6
  (run* (q) (list-subseto '(1 () 2) '(() 0 1 2 3)))
  '())

(test 'subseto-7
  (run* (q) (list-subseto '(1 () 2) '(() 0 1 2 3)))
  '())

(test 'subseto-8
  (run* (q) (list-subseto '() q))
  '((()) ((_.0 . _.1))))

(test 'subset-9
  (run* (q) (list-subseto q '()))
  '((())))

(test 'evalo-1
  (run 1 (q) (evalo 'x q))
  '())

(test 'evalo-2
  (run* (q) (evalo '1 q))
  '((1)))

(test 'evalo-3
  (run 1 (q) (evalo '((lambda (x) 2) 1) q))
  '((2)))

(test 'evalo-4
  (run 10 (q) (evalo '((lambda (x) 2) 1) q))
  ;; tabling or lazy constraints may allow this to be one answer
  '((2) (2) (2) (2) (2) (2) (2) (2) (2) (2)))

(test 'evalo-5
  (run 10 (q) (evalo '((lambda (x) x) 1) q))
  '((1) (1) (1) (1) (1) (1) (1) (1) (1) (1)))

(test 'evalo-6
  (run 10 (q) (evalo '(lambda (x) x) q))
  '((())
    (((_.0 . _.0)) (num _.0))
    (((())))
    (((_.0 . _.0) (_.1 . _.1)) (num _.0 _.1))
    ((((_.0 . _.1))))
    (((_.0 . _.0) (())) (num _.0))
    ((((_.0 . _.1) _.0 . _.1)) (num _.1))
    (((()) (_.0 . _.0)) (num _.0))
    (((_.0 . _.0) (_.1 . _.1) (_.2 . _.2)) (num _.0 _.1 _.2))
    (((_.0 . _.0) ((_.1 . _.2))) (num _.0))))


(define print-answers
  (lambda (answers)
    (for-each
      (lambda (value/side-condition)
        (pmatch value/side-condition
                [((table . ,table) . ,side-condition)
                 (printf "=====================\n")
                 (for-each
                   (lambda (pr)
                     (printf "~s -> ~s\n"
                             (car pr)
                             (cdr pr)))
                   table)
                 (unless (null? side-condition)
                   (printf "---------------------\n")
                   (printf "~s\n" side-condition))
                 (printf "=====================\n")
                 (newline)]))
      answers)))

(print-answers (run 100 (q) (evalo '(lambda (x) x) q)))

;; examples from the bottom of page 5

(test 'page-5-1
  (let ((t0 '(table . ((1 . 2))))
        (t1 '(table . ((0 . 1) (1 . 2)))))
    (run 1 (q)
      (evalo '(lambda (x) x) `(table . ((,t0 . ,t0) (,t1 . ,t1))))))
  '((_.0)))

(test 'page-5-2
  (let ((t0 '(table . ((1 . 2))))
        (t1 '(table . ((0 . 1) (1 . 2)))))
    (run 1 (q)
      (evalo '(lambda (x) x) `(table . ((,t0 . ,t1))))))
  '())

(test 'page-5-3
  (let ((t0 '(table . ((1 . 2))))
        (t1 '(table . ((0 . 1) (1 . 2)))))
    (run 1 (q)
      (evalo '(lambda (x) x) `(table . ((,t1 . ,t0))))))
  '((_.0)))


;; example from top of page 6

(test 'page-6-1
  (let ((t3 '(table . (((table . ()) . 1)))))
    (run 1 (q)
      (evalo '(lambda (f) (f f)) `(table . ((,t3 . 1))))))
  '((_.0)))


;; example from the bottom of page 7

(test 'page-7-1
  (run 1 (q)
    (evalo '(lambda (y) (lambda (x) x)) `(table . ((1 . (table . ())) (1 . (table . ((0 . 0)))) (1 . (table . ((8 . 8) (5 . 5))))))))
  '((_.0)))
