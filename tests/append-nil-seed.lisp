;;; `append` accepts nil as an empty first argument, and rejects every
;;; other non-cons first argument with a catchable type error.
;;; Pins a shape that used to abort the process instead.

(defun apns/catch (tag form) (catch tag (eval form)))

(defun apns/starts-with? (prefix s)
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

(defun apns/msg? (tag prefix form)
  (let ((v (apns/catch tag form)))
    (and (string? v) (apns/starts-with? prefix v))))

;; `(append nil xs)` answering `xs` is what makes `append` usable as a
;; fold seed. It used to take the whole process down: a nil first
;; argument reached the allocator as a malformed one-element dotted
;; cell and tripped an assertion there. Any change here should be
;; deliberate, including a change back to raising.
(test apns-nil-is-an-empty-first-argument
      (eq? (append nil (list 1)) (list 1))
      (eq? (append nil (list 1 2)) (list 1 2))
      (nil? (append nil))
      (nil? (append nil nil))
      ;; nil in a later position was always fine; pinned as the control
      (eq? (append (list 1) nil) (list 1))
      (eq? (append (list 1) (list 2)) (list 1 2)))

;; Every OTHER wrong first argument is still a type error, which is
;; what says nil is special-cased rather than the check being gone.
;; The erroring call is the condition of an `if` so it cannot be
;; compiled away as a discarded statement.
(test apns-other-first-arguments-still-raise
      (apns/msg? 'type-error "Type Error: Expected cons but got integer"
                 '(if (append 1 2) 1 2))
      (apns/msg? 'type-error "Type Error: Expected cons but got vec"
                 '(if (append (vec) (list 1)) 1 2))
      (apns/msg? 'type-error "Type Error: Expected cons but got string"
                 '(if (append "" (list 1)) 1 2)))
