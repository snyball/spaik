;;; `clone` on callables: lambdas and builtins, alone and nested inside
;;; containers. Each used to abort the process on an unimplemented
;;; path; each now produces a working copy.

;;; ---[ helpers ]-----------------------------------------------------

(defun clc/clone-lambda-call ()
  (let ((f (lambda (x) (* x 3))))
    ((clone f) 14)))

(defun clc/clone-subr-call ()
  ((clone car) (list 7 8)))

(defun clc/clone-in-vec-call ()
  (let ((v (clone (vec 1 (lambda (x) (+ x 1)) 2))))
    ((get v 1) 41)))

(defun clc/clone-in-list-call ()
  ((car (clone (list car))) (list 5 6)))

(defun clc/clone-in-table-call ()
  ((get (clone (make-table :f (lambda (x) (- x 1)))) :f) 43))

;; `eval` of a value clones it, so evaluating a live callable is a
;; second route to the same path.
(defun clc/eval-subr-call ()
  ((eval car) (list 9 10)))

(defun clc/eval-lambda-call ()
  ((eval (lambda (x) (+ x 100))) 1))

;;; ---[ cloning a callable produces a callable copy ]-------------------

(test clc-clone-lambda-is-callable
      (= 42 (clc/clone-lambda-call)))

(test clc-clone-builtin-is-callable
      (= 7 (clc/clone-subr-call)))

;;; ---[ containers holding callables clone element-wise ]---------------

;; `clone` descends into elements, so a vector of handlers or a table
;; of callbacks reaches the same path as cloning the function directly.

(test clc-clone-callable-inside-vec
      (= 42 (clc/clone-in-vec-call)))

(test clc-clone-callable-inside-list
      (= 5 (clc/clone-in-list-call)))

(test clc-clone-callable-inside-table
      (= 42 (clc/clone-in-table-call)))

;;; ---[ the route that does not mention `clone` ]-------------------------

(test clc-eval-of-a-live-callable
      (= 9 (clc/eval-subr-call))
      (= 101 (clc/eval-lambda-call)))

