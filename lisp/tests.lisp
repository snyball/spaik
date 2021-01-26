;;
;; Some tests implementing common functions
;;

(defun fib (n)
  (let ((a 0)
        (b 1)
        (t 0))
    (while (> n 0)
      (println a)
      (set t (+ a b))
      (set b a)
      (set a t)
      (dec n 1))
    b))

(defun fib-rec-0 (n a b)
  (if (> n 0)
      (progn
        (println a)
        (fib-rec-0 (- n 1) b (+ a b)))
    b))

(defun fib-rec (n)
  (fib-rec-0 n 0 1))

(defun fact (n)
  (let ((res 1) (upto 1))
    (while (<= upto n)
      (println res)
      (set res (* upto res))
      (inc upto 1))
    res))

(defun fact-silent (n)
  (let ((res 1))
    (while (> n 0)
           (set res (* n res))
           (dec n 1))
    res))

(defun fact-rec (n)
  (if (> n 0)
      (* n (println (fact-rec (- n 1))))
    1))

(defun sum (xs)
  (let ((x 0)
        (acc 0))
    (while xs
           (set x (car xs))
           (set acc (+ x acc))
           (set xs (cdr xs)))
    acc))

(defun countdown-list (n)
  (if (> n 0)
      (cons n (countdown-list (- n 1)))
    n))


;;; I want this
;; (defun asm-jmp-if (cnd inst label)
;;   (while (= (car cnd) 'not)
;;     (set cnd (cadr cnd))
;;     (set inst (not inst)))
;;   `(inline
;;      ,cnd
;;      (,inst label)))
;; (defun asm-loop (cnd jmp-inst &body body)
;;   (let ((loop-begin (gensym))
;;         (loop-end (gensym)))
;;     `(inline
;;        (#label ,loop-begin)
;;        (asm-jmp-if ,cnd ,jmp-inst ,loop-end)
;;        (progn ,@body)
;;        (#pop 1)
;;        (#jmp ,loop-begin)
;;        (#label ,loop-end))))
;; (defmacro while (cnd &body body)
;;   (asm-loop cnd #'jn body))
;; (defmacro until (cnd &body body)
;;   (asm-loop cnd #'jt body))
;; (println `((fib-max ,fib-max)
;;            (fact-max ,fact-max)
;;            ,@lst))

(defun main ()
  (let ((fib-max 20)
        (fact-max 12)
        (lst '(1 2 3)))
    (println "Fibonacci test:")
    (fib fib-max)
    (println "")

    (println "Recursive fibonacci test:")
    (fib-rec fib-max)
    (println "")

    (println "Factorial test:")
    (fact fact-max)
    (println "")

    (println "Recursive factorial test:")
    (fact-rec fact-max)
    (println "")

    (println "Computing ...")
    (let ((n 1000))
      (while (> n 0)
        (fact-silent 20)
        (dec n 1)))
    (println "Done.")

    (println '(1 2 3))
    (println (list 1 2 3 4))
    (println (list 1 2 3 4 (list 3 2 1) (list 3 2)))
    (println (append (list 1 2) (list 3 4)))
    (println (append (list 1 2) 3))
    (println "Sum of list:")
    (println (sum (list 1 2 3 4 5 6 7 8 9)))
    (println (countdown-list 20))
    1337))
