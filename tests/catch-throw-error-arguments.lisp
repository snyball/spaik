;;; Argument checking of the exception machinery itself: catch, throw,
;;; error, call/cc. Catch outside, eval inside, eval in tail position.
;;; Errors are catchable only inside `eval`; outside it they stay fatal.

(defun cte/catch (tag form) (catch tag (eval form)))

(defun cte/starts-with? (prefix s)
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

(defun cte/msg? (tag prefix form)
  (let ((v (cte/catch tag form)))
    (and (string? v) (cte/starts-with? prefix v))))

;;; ---[ the tag argument must be a symbol ]-----------------------------

(test cte-tag-must-be-a-symbol
      ;; all three name the argument position, and each says which form
      ;; it is complaining about
      (cte/msg? 'type-error "Type Error: Expected symbol for argument 1 of (catch ...), but got integer"
                '(catch 1 2))
      (cte/msg? 'type-error "Type Error: Expected symbol for argument 1 of (catch ...), but got nil"
                '(catch nil 1))
      (cte/msg? 'type-error "Type Error: Expected symbol in throw, but got string"
                '(throw "k" 1))
      (cte/msg? 'type-error "Type Error: Expected symbol in throw, but got nil"
                '(throw nil 1))
      (cte/msg? 'type-error "Type Error: Expected symbol for argument 1 of (error ...), but got integer"
                '(error 5))
      (cte/msg? 'type-error "Type Error: Expected symbol for argument 1 of (error ...), but got nil"
                '(error nil))
      ;; a KEYWORD is a symbol, so it is a legal tag for all three
      (= 1 (cte/catch 'type-error '(catch :cte-kw 1)))
      (eq? :payload (cte/catch :cte-kw '(error :cte-kw :payload))))

;;; ---[ arity ]---------------------------------------------------------

(test cte-arity
      (cte/msg? 'arg-error "Argument Error: catch expected 2" '(catch))
      (cte/msg? 'arg-error "Argument Error: throw expected 2" '(throw))
      (cte/msg? 'arg-error "Argument Error: throw expected 2 argument, but got 1" '(throw 'cte-k))
      (cte/msg? 'arg-error "Argument Error: expected from 1 to 2 arguments, but got 0" '(error))
      (cte/msg? 'arg-error "Argument Error: call/cc expected 1 arguments, but got 0" '(call/cc))
      ;; `catch` is the lenient one: a tag with NO body is legal and
      ;; answers nil, and a multi-form body answers its last form
      (nil? (cte/catch 'arg-error '(catch 'cte-k)))
      (= 2 (cte/catch 'arg-error '(catch 'cte-k 1 2))))

;;; ---[ error's payload rejects reference types ]-------------------------

;; Written without `eval`: a `throw` crossing an eval boundary leaks a
;; stack slot, which re-runs later top-level forms.
(defun cte/throw-a-list ()   (catch 'cte-k (throw 'cte-k (list 1 2))))
(defun cte/throw-a-string () (catch 'cte-k (throw 'cte-k "s")))
(defun cte/throw-from-call-cc ()
  (catch 'cte-k (call/cc (lambda (k) (throw 'cte-k 3)))))

(test cte-error-payload-must-be-immediate
      ;; a list, vec, string or table payload is refused under its own
      ;; tag. The restriction is intended: a payload must be an
      ;; immediate, and anything heap-allocated is refused.
      (cte/msg? 'reference-not-allowed "Reference types are not allowed"
                '(error 'cte-k (list 1 2)))
      (cte/msg? 'reference-not-allowed "Reference types are not allowed"
                '(error 'cte-k (vec 1)))
      (cte/msg? 'reference-not-allowed "Reference types are not allowed"
                '(error 'cte-k (make-table)))
      (cte/msg? 'reference-not-allowed "Reference types are not allowed"
                '(error 'cte-k "s"))
      ;; `throw`, by contrast, takes any value at all
      (eq? '(1 2) (cte/throw-a-list))
      (eq? "s" (cte/throw-a-string)))

;;; ---[ call/cc ]---------------------------------------------------------

(test cte-call-cc-argument-checks
      ;; the argument must be callable ...
      (cte/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                '(call/cc 5))
      ;; ... and must accept exactly the one continuation argument. The
      ;; arity complaint names the lambda `λ`, not call/cc.
      (cte/msg? 'arg-error "Argument Error: λ expected 0 argument, but got 1"
                '(call/cc (lambda () 1)))
      ;; the working shapes
      (= 5 (cte/catch 'type-error '(call/cc (lambda (k) (k 5)))))
      (= 6 (cte/catch 'type-error '(call/cc (lambda (k) 6))))
      ;; a throw out of a call/cc reaches an enclosing catch normally
      (= 3 (cte/throw-from-call-cc)))
