(defun qts-build ()
  (let ((q '((1 2 3) (4 5 6) (7 8 9))))
    `(,@(car q) ,@(cdar q))))

;; The splice must not have mutated the quoted literal it read from.
(defun qts-source-intact ()
  (let ((q '((1 2 3) (4 5 6) (7 8 9))))
    `(,@(car q) ,@(cdar q))
    (car q)))

;; Walking the tail terminates (a circular splice would not).
(defun qts-walk-len ()
  (let ((n 0) (xs (qts-build)))
    (loop (if (not xs) (break))
      (set n (+ n 1))
      (set xs (cdr xs)))
    n))

(test quasiquote-two-splices
      (eq? (qts-build) (list 1 2 3 2 3))
      (= (len (qts-build)) 5)
      (= (qts-walk-len) 5)
      (eq? (qts-source-intact) (list 1 2 3))
      ;; element-wise, the way the original repro probed it
      (= (car (qts-build)) 1)
      (= (cadr (qts-build)) 2)
      (= (caddr (qts-build)) 3)
      (= (cadddr (qts-build)) 2)
      (= (cadddr (cdr (qts-build))) 3)
      ;; tails
      (eq? (cdr (qts-build)) (list 2 3 2 3))
      (eq? (cddddr (qts-build)) (list 3)))
