;;;
;;; Sanity-checks for builtins
;;;

;;; [ misc ]----------------------------------------
(defun tests--sum-n (n)
  (/ (* n (+ n 1)) 2))

;;; ---[ math ]----------------------------------------
(defun math/fibonacci (n)
  (let ((a 0) (b 1))
    (while (> n 0)
      (set* (a b) (b (+ a b)))
      (dec! n))
    a))

(defun math/factorial (n)
  (let ((x 1))
    (while (> n 0)
      (set* (x n) ((* x n) (- n 1))))
    x))

(test math
      (= (+) 0)
      (= (+ 10) 10)
      (= (+ 10 10) 20)
      (= (*) 1)
      (= (* 10) 10)
      (= (* 10 10) 100)
      (= (- 1) -1)
      (= (- 1 2) -1)
      (= (- 1 2 3) -4)
      (= (/ 2.0) 0.5)
      (= (/ 8 2) 4)
      (= (/ 8 2 2) 2)
      (eq? (map abs (range-list -10 0))
           (reverse (range-list 1 11)))
      (eq? (map math/fibonacci (range-list 1 21))
           '(1 1 2 3 5 8 13 21 34 55 89 144 233 377 610 987 1597 2584 4181 6765))
      (eq? (map math/factorial (range-list 0 13))
           '(1 1 2 6 24 120 720 5040 40320 362880 3628800 39916800 479001600)))

;;; ---[ loops ]---------------------------------------
(test loops
      (= (loop (break 'ok)) 'ok)
      (= (let ((x (dolist (y '(abc def ghi))
                    (break y))))
           x)
         'abc)
      (eq? (let ((xs nil))
             (loop
              (set xs (cons 'x xs))
              (when (= (len xs) 1)
                (set xs (cons 'y xs))
                (next))
              (set xs (cons 'z xs))
              (break xs)))
           '(z x y x)))

;;; ---[ quasi ]---------------------------------------
(test quasi-quoting
      (eq? (let ((x 1) (y 'abc) (z 'xyz))
             `(:x ,x :y ,y :z ,z))
           '(:x 1 :y abc :z xyz))
      (eq? `(x y z)
           '(x y z))
      (eq? (let ((x 1) (y 2) (z 3))
             `(,x (,y ,z) ,y ,z ((,x))))
           '(1 (2 3) 2 3 ((1)))))

;;; ---[ let ]-----------------------------------------
(test let-bindings
      (= (let ((x 1)) x)
         1)
      (= (let ((x (let ((y (let ((z 1336)) (+ z 1)))) y)))
           x)
         1337))

;;; ---[ lambda ]--------------------------------------
(test lambda-empty-call
      (= ((lambda (x) (+ x 10)) 10)
         20)
      ;(= ((lambda (x &? y) (+ x (or y 1))) 10)
      ;   11)
      ;(= ((lambda (x &? y) (+ x (or y 1))) 10 10)
      ;   20)
      (= ((lambda (x &rest r) (* x (sum r))) 1)
         0)
      (= ((lambda (x &rest r) (* x (sum r))) 12 1 2 3 4 5)
         (* 12 (tests--sum-n 5))))

(test lambda-capture-call
      (= ((let ((y 10))
            (lambda (x) (+ x y))) 10)
         20)
      (= ((let ((f (let ((y 1.3e3))
                     (lambda (x) (+ x y)))))
            (lambda (x) (f x))) 37)
         1337.0))

;;; ---[ static-variables ]----------------------------
(define var 0)
(defun tests--static-var ()
  (inc! var))

(test static-variables
      (eq? `(,(tests--static-var)
             ,(tests--static-var)
             ,(tests--static-var)
             ,(tests--static-var))
           '(1 2 3 4)))

;;; ---[ rest-args ]-----------------------------------
(defun tests--mul-sum (x &rest r)
  (* x (sum r)))

(test rest-args
      (= (tests--mul-sum 1) 0)
      (= (tests--mul-sum 4) 0)
      (= (tests--mul-sum 4 1 2 3) (* 4 (tests--sum-n 3)))
      (= (tests--mul-sum 6 1 2 3 4 5 6 7 8 9) (* 6 (tests--sum-n 9))))

;;; ---[ optional-args ]-------------------------------
(defun tests--opt (x &? y)
  (+ x (or y 2)))

(defun tests--opt-2 (x &? y &? z)
  (+ x (or y 2) (or z 2)))

(test optional-args
      (= (tests--opt 2) 4)
      (= (tests--opt 3) 5)
      (= (tests--opt 2 3) 5)
      (= (tests--opt 2 5) 7)
      (= (tests--opt-2 2) 6)
      (= (tests--opt-2 3) 7)
      (= (tests--opt-2 2 3) 7)
      (= (tests--opt-2 2 5) 9)
      (= (tests--opt-2 2 3 3) 8)
      (= (tests--opt-2 2 5 3) 10))

;;; ---[ rest-and-optional-args ]-----------------------
(defun tests--mul-opt-sum (&? x &rest r)
  (* (or x 1) (sum r)))

(test rest-and-optional-args
      (= (tests--mul-opt-sum) 0)
      (= (tests--mul-opt-sum 1) 0)
      (= (tests--mul-opt-sum 4 1 2 3) (* 4 (tests--sum-n 3)))
      (= (tests--mul-opt-sum 6 1 2 3 4 5 6 7 8 9) (* 6 (tests--sum-n 9))))

;;; ---[ eval ]-----------------------------------------
(test eval
      (= (eval nil) nil)
      (= (eval '(+ 2 2)) 4)
      (= (eval '(eval '(eval '(+ 1 1)))) 2))

;;; ---[ eval-when-compile ]-----------------------------
(define static-1 0)
(defun tests--inc-static-1 (n)
  (inc! static-1 n))

(define static-2 0)
(defun tests--inc-static-2 (n)
  (inc! static-2 n))
;(test eval-when-compile
;      (= (progn
;           (tests--inc-static-1 10)
;           (tests--inc-static-1 20))
;         30)
;      (= (progn
;           (tests--inc-static-2 10)
;           (eval-when :compile
;             (tests--inc-static-2 20)))
;         20))

;;; ---[ and/or ]----------------------------------------
(define static-3 0)
(defun tests--inc-static-3 (n)
  (inc! static-3 n))

(define static-4 0)
(defun tests--inc-static-4 (n)
  (inc! static-4 n))

(test and
      (= (and)
         true)
      (= (and false)
         false)
      (= (and true)
         true)
      (= (and true false)
         false)
      (= (progn
           (and true
                false
                (tests--inc-static-3 10))
           (tests--inc-static-3 10))
         10))

(test or
      (= (or)
         false)
      (= (or false)
         nil)
      (= (or true)
         true)
      (= (or false 'thing 10)
         'thing)
      (= (or true false)
         true)
      (= (progn
           (or false
               true
               (tests--inc-static-4 10))
           (tests--inc-static-4 10))
         10))

;;; ---[ vector ]----------------------------------------
(test vector
      (eq? (let ((v (vec 1 2 3)))
             `(,(pop v) ,(pop v) ,(pop v)))
           '(3 2 1))
      (eq? (let ((v (vec 1 2 3)))
             (push v 10)
             `(,(pop v) ,(pop v) ,(pop v)))
           '(10 3 2))
      (eq? (let ((v (vec 1 2 3)))
             (push v 10)
             (push v 12)
             `(,(get v 0) ,(get v 4) ,(get v 3)))
           '(1 12 10))
      (= (let ((v (vec)))
           (push v 1337))
         1337)
      (= (len (vec 1 2 3))
         3)
      (= (len (vec))
         0))

;;; ---[ inc/dec ]---------------------------------------
(test inc
      (= (let ((x 0))
           (inc! x))
         1)
      (= (let ((x 0))
           (inc! x)
           (inc! x))
         2)
      (= (let ((x 0))
           (inc! x)
           (inc! x)
           x)
         2))

(test dec
      (= (let ((x 1))
           (dec! x))
         0)
      (= (let ((x 1))
           (dec! x)
           (dec! x))
         -1)
      (= (let ((x 1))
           (dec! x)
           (dec! x)
           x)
         -1))

;;; ---[ self ]------------------------------------------
(load self)

(test self
      (eq? (do-factorial)
           '(1 2 6 24 120 720 5040 40320 362880 3628800))
      (eq? (do-factorial-d)
           '(1 2 6 24 120 720 5040 40320 362880 3628800))
      (eq? (evil '((((lambda (f)
                       (f f))
                     (lambda (f)
                       (lambda (g)
                         (lambda (xs)
                           (if xs
                               (cons (g (car xs))
                                     (((f f) g) (cdr xs))))))))
                    (lambda (x)
                      (* x 2)))
                   '(2 4 6 8 10 12)))
           '(4 8 12 16 20 24))
      (eq? (evil '((((lambda (x)
                       (lambda (y)
                         (lambda (z)
                           (+ (* x (* 2 y)) z))))
                     4) 5) 6))
           46))

;;; ---[ gensym ]----------------------------------------
(defun mapwise (f xs)
  (= (dolist (pair (zip xs (cdr xs)))
       (let ((x (car pair))
             (y (cadr pair)))
         (break `(,x ,y))))
     nil))

(test gensym)

;;; ---[ continuations ]---------------------------------
(test continuations
      (= (+ (call/cc (lambda (k) (throw (k 1)))) 1) 2))

;;; ---[ apply ]-----------------------------------------
(test apply
      (eq? (apply (lambda (&rest xs) xs) (vec 1 2 3))
           '(1 2 3))
      (eq? (apply (lambda (&rest xs) xs) '(1 2 3))
           '(1 2 3))
      (eq? (all? (lambda (li)
                   (eq? (apply (lambda (&rest xs)
                                 xs)
                               li)
                        li))
                 `(,(range-list 0 100)
                   ,(range-list 10 15)))
           true)
      (= (apply + (let ((v (vec))) (range (i (0 65535)) (push v i)) v))
         (let ((s 0))
           (range (i (0 65535)) (set s (+ s i)))
           s)))

;;; ---[ unused ]----------------------------------------
(defun black-box (x) x)
(define *test-global* 0)
(defun shenanigans (x)
  (set *test-global* (+ *test-global* x)))

(test dead-code
      (= (let ((x 0))
           (+ 1 2 3 4 5 (set x 5))
           (+ 1 2 3 (set x (+ x 5)) 4 5)
           (- 1 2 3 (set x (+ x 5)) 4 5)
           x)
         15)
      (= (progn
           (+ 1 (shenanigans 10))
           (< 1 (shenanigans 30))
           *test-global*)
         40))

;;; ---[ macros ]----------------------------------------
(defmacro make-lambda (x)
  `(lambda () ,x))

(test macros
      (= ((make-lambda 1)) 1)
      (= ((make-lambda (+ 1 2 3))) (+ 1 2 3))
      (= (eval-when-compile ((make-lambda 1))) 1)
      (= (read-compile "(apply (make-lambda 1) (vec))") 1)
      (= ((read-compile "(make-lambda 1)")) 1)
      (= (read-compile "((make-lambda 1))") 1))

;;; ---[ evaaal ]----------------------------------------

(test evaaal
      (eq? (eval '(do-factorial-d)) (do-factorial-d)))
