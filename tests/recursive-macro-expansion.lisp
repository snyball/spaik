(defmacro rep (n &body body)
  (if (= n 0)
      nil
      `(progn ,@body (rep ,(- n 1) ,@body))))

;; The historical boundary: n=1 always worked, n=2 was the crash.
(defun rme-0 () (let ((c 0)) (rep 0 (set c (+ c 1))) c))
(defun rme-1 () (let ((c 0)) (rep 1 (set c (+ c 1))) c))
(defun rme-2 () (let ((c 0)) (rep 2 (set c (+ c 1))) c))
(defun rme-3 () (let ((c 0)) (rep 3 (set c (+ c 1))) c))
(defun rme-5 () (let ((c 0)) (rep 5 (set c (+ c 1))) c))

;; Well past the old cliff, to catch a regression that merely moves it.
(defun rme-40 () (let ((c 0)) (rep 40 (set c (+ c 1))) c))

;; Multi-form `&body`, spliced twice per level (the shape the original
;; trace blamed: the recursive call nested inside a spliced `,@body`).
(defun rme-multi-body ()
  (let ((c 0) (d 0))
    (rep 4 (set c (+ c 1)) (set d (+ d 2)))
    (list c d)))

;; A second, independently-recursing macro, to check the expander does
;; not carry state across expansions.
(defmacro rep-sum (n acc)
  (if (= n 0) acc `(rep-sum ,(- n 1) (+ 1 ,acc))))
(defun rme-nested-expr () (rep-sum 10 0))

(test recursive-macro-expansion
      (= (rme-0) 0)
      (= (rme-1) 1)
      (= (rme-2) 2)
      (= (rme-3) 3)
      (= (rme-5) 5)
      (= (rme-40) 40)
      (eq? (rme-multi-body) (list 4 8))
      (= (rme-nested-expr) 10))

;;; ---[ runaway expansion is bounded, not fatal ]-----------------------

(defun rme/catch (tag form) (catch tag (eval form)))

;; Expands to itself forever - no base case at all.
(defmacro rme/self (n) `(rme/self ,n))

;; Terminates after `n` levels.
(defmacro rme/counted (n) (if (= n 0) 0 `(rme/counted ,(- n 1))))

(defun rme/runaway ()      (rme/catch 'recursion-limit '(rme/self 1)))
(defun rme/counted-100 ()  (rme/catch 'recursion-limit '(rme/counted 100)))
(defun rme/counted-900 ()  (rme/catch 'recursion-limit '(rme/counted 900)))
(defun rme/counted-1100 () (rme/catch 'recursion-limit '(rme/counted 1100)))

(test recursive-macro-expansion-depth-limit
      ;; runaway expansion is reported, not fatal, and not a crash
      (string? (rme/runaway))
      ;; well under the ceiling: expands normally and yields its value
      (= 0 (rme/counted-100))
      (= 0 (rme/counted-900))
      ;; past the ceiling: the same `recursion-limit` report
      (string? (rme/counted-1100))
      ;; the limit is a macroexpansion limit, not a general recursion
      ;; limit - ordinary deep function recursion is untouched
      (= 10000 (rme/catch 'recursion-limit '(rme/deep-fn 10000))))

(defun rme/deep-fn (n) (if (< n 1) 0 (+ 1 (rme/deep-fn (- n 1)))))
