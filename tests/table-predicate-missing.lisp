(define tpm-table (make-table))

;; `table?` bound as a value rather than called in operator position.
;; (Kept in its own function: the `test` macro evaluates each check's
;; arguments into temporaries, so a check cannot itself be a `let`.)
(defun tpm-via-value (x) (let ((f table?)) (f x)))

(test table-predicate
      (table? tpm-table)
      (not (table? 5))
      (not (table? (vec 1 2)))
      (not (table? "hi"))
      (not (table? (cons 1 2)))
      (not (table? nil))
      ;; still agrees with `type-of`, and the siblings still work
      (eq? (type-of tpm-table) 'table)
      (vec? (vec 1 2))
      (string? "hi")
      (cons? (cons 1 2))
      ;; usable as a first-class value, unlike the opcode-compiled
      ;; builtins still tracked in
      ;; `suspect/list-and-vec-not-first-class-functions.lisp`
      (tpm-via-value tpm-table))
