;;; An arbitrary expression in operator position: `((cdr p) 8)`.
;;; `cdr` there compiles and dispatches on the runtime value; opcodes
;;; whose result can never be callable are refused at compile time.

;;; ---[ helpers ]-----------------------------------------------------

(defun opos/catch (tag form)
  (catch tag (eval form)))

(defun opos/starts-with? (prefix s)
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

;; True when `form` raises under `tag` with a message starting `prefix`.
(defun opos/msg? (tag prefix form)
  (let ((v (opos/catch tag form)))
    (and (string? v) (opos/starts-with? prefix v))))

;;; ---[ cdr in operator position ]--------------------------------------

;; The tail of a dotted pair is an arbitrary value and may perfectly
;; well be a lambda, so `(cdr p)` has to be allowed to name the thing
;; being called. It was once refused before the program ran, on the
;; grounds that the `cdr` opcode's static result type is `list`; the
;; same value reached through `let` or `apply` called fine, which is
;; what made the refusal wrong rather than merely strict.

(define opos-pair (cons 1 (lambda (x) (* x 5))))

(defun opos/direct () ((cdr opos-pair) 8))
(defun opos/via-let () (let ((k (cdr opos-pair))) (k 8)))
(defun opos/via-apply () (apply (cdr opos-pair) (list 8)))

(test opos-cdr-in-operator-position
      ;; all three routes to the same lambda agree
      (= 40 (opos/direct))
      (= 40 (opos/via-let))
      (= 40 (opos/via-apply)))

;; `car` was always accepted in this position, and so were the stdlib
;; accessors that reach past the head without compiling to the `cdr`
;; opcode. `tail` is `cdr` by another name - on the dotted pair below it
;; answers the lambda, where on `(list 1 f)` it would answer the
;; one-element list `(f)`. The point of these is that all four agree.

(defun opos/car () ((car (cons (lambda (x) (* x 5)) 1)) 8))
(defun opos/cadr () ((cadr (list 1 (lambda (x) (* x 5)))) 8))
(defun opos/tail () ((tail (cons 1 (lambda (x) (* x 5)))) 8))
(defun opos/cddr () ((cddr (cons 1 (cons 2 (lambda (x) (* x 5))))) 8))

(test opos-every-accessor-agrees
      (= 40 (opos/car))
      (= 40 (opos/cadr))
      (= 40 (opos/tail))
      (= 40 (opos/cddr)))

;;; ---[ shapes the operator expression can take ]------------------------

(defun opos/nested ()
  ((cdr (cdr (cons 0 (cons 1 (lambda (x) (+ x 1)))))) 41))
(defun opos/zero-arg () ((cdr (cons 1 (lambda () 42)))))
(defun opos/varargs () ((cdr (cons 1 (lambda (&rest xs) (len xs)))) 1 2 3))
(defun opos/param (r) ((cdr r) 7))

(test opos-cdr-operator-shapes
      (= 42 (opos/nested))
      (= 42 (opos/zero-arg))
      (= 3 (opos/varargs))
      ;; the pair need not be known at the call site
      (= 35 (opos/param opos-pair)))

;;; ---[ every callable kind reaches the call ]---------------------------

;; Dispatch is on the runtime value, so a subr and a continuation in
;; the tail work as well as a lambda does.

(defun opos/subr () ((cdr (cons 1 car)) (list 7 8)))
(defun opos/continuation ()
  (call/cc (lambda (k) ((cdr (cons 1 k)) 99))))

(test opos-callable-kinds
      (= 7 (opos/subr))
      (= 99 (opos/continuation)))

;;; ---[ a non-callable tail fails at RUNTIME ]---------------------------

;; The refusal that remains for `cdr` is the honest one: it happens when
;; the call is reached, names the value's real type, and leaves every
;; form before it having run. `integer` here is the runtime type of the
;; tail, not the `cdr` opcode's static result type.

(test opos-non-callable-tail-raises-at-runtime
      (opos/msg? 'type-error
                 "Type Error: Expected one of lambda, subr, continuation, object but got integer"
                 '(if ((cdr (cons 1 2)) 3) :opos-then :opos-else)))

;;; ---[ opcodes that can never be callable are still refused early ]-----

;; Pinned as what the compiler currently does. These results genuinely
;; cannot be called, so refusing them before the run is defensible - but
;; note the cost, which is why it is worth having written down: the
;; refusal is a COMPILE error and takes the whole file with it, so one
;; such form anywhere means no top-level form in that file runs at all,
;; and the exit code is still 0. `cdr` is deliberately not in this list.
;;
;; The two refusals are told apart by their wording. Compile time names
;; `apply` and the opcode's static result type; runtime lists the
;; callable types and names the value's own. Only the first appears here.

(defun opos/rejected-early? (form)
  (opos/msg? 'type-error
             "Type Error: Expected lambda for argument 0 of (apply ...), but got "
             form))

(test opos-non-callable-opcodes-refused-at-compile-time
      (opos/rejected-early? '(if ((+ 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((- 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((* 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((< 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((not 1) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((eq? 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((list 1) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((cons 1 2) 3) :opos-then :opos-else))
      (opos/rejected-early? '(if ((vec 1) 3) :opos-then :opos-else)))

;; The static type in the message is the opcode's, so it disagrees with
;; the value when the two differ: `(cons 1 2)` is refused as `cons` and
;; `(list 1)` as `list`, neither of which is a type any runtime message
;; uses. This is the tell that the check ran before the program did.

(test opos-compile-refusal-names-the-opcode-type
      (opos/msg? 'type-error
                 "Type Error: Expected lambda for argument 0 of (apply ...), but got cons"
                 '(if ((cons 1 2) 3) :opos-then :opos-else))
      (opos/msg? 'type-error
                 "Type Error: Expected lambda for argument 0 of (apply ...), but got vec"
                 '(if ((vec 1) 3) :opos-then :opos-else))
      (opos/msg? 'type-error
                 "Type Error: Expected lambda for argument 0 of (apply ...), but got bool"
                 '(if ((< 1 2) 3) :opos-then :opos-else)))
