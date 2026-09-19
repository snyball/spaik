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
      ;; `throw` takes 2 OR 3. The 3-argument form is (throw <continuation>
      ;; <tag> <value>); the plural still follows the RECEIVED count, so
      ;; "got 1" reads "argument" and "got 0" reads "arguments".
      (cte/msg? 'arg-error "Argument Error: throw expected from 2 to 3 arguments, but got 0" '(throw))
      (cte/msg? 'arg-error "Argument Error: throw expected from 2 to 3 arguments, but got 1" '(throw 'cte-k))
      (cte/msg? 'arg-error "Argument Error: throw expected from 2 to 3 arguments, but got 4"
                '(throw 'cte-k 1 2 3))
      (cte/msg? 'arg-error "Argument Error: expected from 1 to 2 arguments, but got 0" '(error))
      (cte/msg? 'arg-error "Argument Error: call/cc expected 1 argument, but got 0" '(call/cc))
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
      (cte/msg? 'arg-error "Argument Error: λ expected 0 arguments, but got 1"
                '(call/cc (lambda () 1)))
      ;; the working shapes
      (= 5 (cte/catch 'type-error '(call/cc (lambda (k) (k 5)))))
      (= 6 (cte/catch 'type-error '(call/cc (lambda (k) 6))))
      ;; a throw out of a call/cc reaches an enclosing catch normally
      (= 3 (cte/throw-from-call-cc)))

;;; ---[ the three-argument throw ]----------------------------------------

;; `(throw k tag value)` reinstates the continuation `k` and then performs
;; `(throw tag value)` THERE, so the catch that answers is the one live at
;; k's capture site - not the one around the `throw` itself.

(defun cte/throw-to-self ()
  (catch 'cte-k (call/cc (lambda (k) (throw k 'cte-k 42)))))

(defun cte/throw-to-self-string ()
  (catch 'cte-k (call/cc (lambda (k) (throw k 'cte-k "payload")))))

(test cte-three-argument-throw
      ;; argument 1 must be a continuation, and complains without naming
      ;; an argument position
      (cte/msg? 'type-error "Type Error: Expected continuation but got string"
                '(throw "k" 'cte-k 1))
      (cte/msg? 'type-error "Type Error: Expected continuation but got integer"
                '(throw 5 'cte-k 1))
      ;; argument 2 is still the tag, and is still checked as a symbol,
      ;; under the same message as the two-argument form
      (cte/msg? 'type-error "Type Error: Expected symbol in throw, but got string"
                '(call/cc (lambda (k) (throw k "cte-k" 1))))
      (cte/msg? 'type-error "Type Error: Expected symbol in throw, but got nil"
                '(call/cc (lambda (k) (throw k nil 1))))
      ;; throwing to the continuation you are standing in is the same as a
      ;; plain throw, and the payload is unrestricted
      (= 42 (cte/throw-to-self))
      (eq? "payload" (cte/throw-to-self-string)))

;;; ---[ throw in function position stayed at two arguments ]---------------

;; `lisp/core.lisp` defines `(defun throw (s v) (throw s v))` so that the
;; special form can be passed around as a value. That wrapper was not
;; widened, so the three-argument form is reachable only by writing the
;; special form out literally.

(defun cte/apply-throw () (catch 'cte-k (apply throw (list 'cte-k 9))))

(test cte-throw-as-a-value-takes-two
      (= 9 (cte/apply-throw))
      ;; and the arity complaint comes from the WRAPPER, naming `λ`
      (cte/msg? 'arg-error "Argument Error: λ expected 2 arguments, but got 3"
                '(apply throw (list 'cte-k 1 2))))
