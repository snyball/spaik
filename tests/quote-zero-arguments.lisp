;;; `(quote)` with no argument is a catchable error, not a compiler panic.
;;; Its sibling special forms report the same shape of mistake as arity.

(defun qz/catch (tag form) (catch tag (eval form)))

(defun qz/starts-with? (prefix s)
  (let ((pit (iter prefix))
        (sit (iter s)))
    (loop
     (let ((p (next pit)))
       (if (iter-end? p)
           (break true)
         (let ((c (next sit)))
           (if (iter-end? c)
               (break nil)
             (unless (= p c)
               (break nil)))))))))

(defun qz/msg? (tag prefix form)
  (let ((v (qz/catch tag form)))
    (and (string? v) (qz/starts-with? prefix v))))

;; `quote` used to take the `car` of its argument list without checking
;; it was non-empty, which panicked the compiler. It now reports the
;; missing form as a type error rather than as an argument count, which
;; is not what its siblings do - `(quasiquote)` says "expected 1
;; arguments, but got 0". Pinned as-is: the day the message becomes an
;; Argument Error should be a deliberate change, not a silent one.
(test qz-zero-arguments-is-a-catchable-error
      (qz/msg? 'type-error "Type Error: Expected cons in quote"
               '(if (quote) 1 2)))

;; The sibling, for contrast, and to keep the comparison honest if
;; either message moves.
(test qz-quasiquote-reports-arity
      (qz/msg? 'arg-error "Argument Error"
               '(if (quasiquote) 1 2)))

;; A one-argument `quote` is untouched.
(test qz-one-argument-still-quotes
      (eq? (quote foo) 'foo)
      (eq? (quote (1 2)) (list 1 2)))
