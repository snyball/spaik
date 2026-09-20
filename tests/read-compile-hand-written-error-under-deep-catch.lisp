;;; `read-compile` of the SAME hand-written erroring source, repeated
;;; under ten nested `catch` handlers, used to segfault once the heap
;;; had to grow. Companion to tests/read-compile-under-deep-catch.lisp,
;;; which pins the machine-generated-text variant of the same family.

(defun rcg/deep (form)
  (catch 'iter-stop (catch 'undefined-variable (catch 'undefined-function
  (catch 'divide-by-zero (catch 'type-error (catch 'arg-error
  (catch 'not-a-proper-list (catch 'unimplemented (catch 'mut-locked
  (catch 'module-load-error
  (eval form))))))))))))

;; 100 iterations is well past the heap-growth threshold that used to
;; fault; the read text is a plain `(car 5)` every time.
(defun rcg/drive ()
  (define i 0)
  (loop
    (if (>= i 100) (break))
    (rcg/deep (list 'read-compile "(car 5)"))
    (set i (+ i 1)))
  :rcg-survived)

(test rcg-repeated-read-compile-under-deep-catch-no-longer-segfaults
      (eq? :rcg-survived (rcg/drive)))
