(load "pmatch.scm")
(load "mk/mk.scm")
(load "mk/test-check.scm")

;; version that uses explicit subsetness

(define evalo
  (lambda (exp val)
    (eval-expo exp '() val)))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((numbero exp) (== exp val))
      ((symbolo exp)
       (fresh (lv)
         (lookupo exp env lv)
         (subseto val lv)))
      ((fresh (rator rand table-val rand-v table a)
         (== `(,rator ,rand) exp)
         (eval-expo rand env rand-v)
         (table-lookupo a table table-val)
         (eval-expo rator env table)
         (subseto a rand-v)
         (subseto val table-val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (table-all x body env val))))))

(define subseto
  (lambda (s1 s2)
    (conde
      ((numbero s1) (numbero s2) (== s1 s2))
      ((== '() s1)
       (conde
         ((== '() s2))
         ((fresh (h t)
            (== `(,h . ,t) s2)))))
      ((fresh (h1 h2 t1 t2)
         (== `(,h1 . ,t1) s1)
         (== `(,h2 . ,t2) s2)
         (conde
           ((== h1 h2)
            (subseto t1 t2))
           ((=/= h1 h2)
            (subseto s1 t2))))))))

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


;;; tests

(test 'subseto-1
  (run* (q) (subseto '(1 2) '(1 2 3)))
  '((_.0)))

(test 'subseto-2
  (run* (q) (subseto '(1 2) '(0 1 2 3)))
  '((_.0)))

(test 'subseto-3
  (run* (q) (subseto '(1 2) '(0 () 1 2 3)))
  '((_.0)))

(test 'subseto-4
  (run* (q) (subseto '(() 1 2) '(0 () 1 2 3)))
  '((_.0)))

(test 'subseto-5
  (run* (q) (subseto '(() 1 2) '(() 0 1 2 3)))
  '((_.0)))

(test 'subseto-6
  (run* (q) (subseto '(1 () 2) '(() 0 1 2 3)))
  '())

(test 'subseto-7
  (run* (q) (subseto '(1 () 2) '(() 0 1 2 3)))
  '())

(test 'subseto-8
  (run* (q) (subseto '() q))
  '((()) ((_.0 . _.1))))

(test 'subset-9
  (run* (q) (subseto q '()))
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


(let ((answers (run 100 (q) (evalo '(lambda (x) x) q))))
    (for-each
      (lambda (value/side-condition)
        (pmatch value/side-condition
          [(,table . ,side-condition)
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
      answers))
