;;; A lambda in direct call position given MORE arguments than it takes.
;;; That shape used to abort in AST construction, before anything ran.
;;; Companion to tests/arity-message-text.lisp.

(defun ilsa/catch (tag form) (catch tag (eval form)))
(defun ilsa/starts-with? (prefix s)
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
(defun ilsa/msg? (tag prefix form)
  (let ((v (ilsa/catch tag form)))
    (and (string? v) (ilsa/starts-with? prefix v))))

;; Surplus arguments to an INLINED lambda - one written directly in
;; operator position - raise an ordinary catchable `arg-error` naming
;; `λ`. This used to index one past the end of the parameter list while
;; the AST was built, which aborted the process at COMPILE time: the
;; form never ran, and the form's presence anywhere in a file killed
;; that file before any of its other top-level forms executed.
;;
;; The index that overflowed was the lambda's fixed arity, so every
;; arity reached it and all three are pinned here.
(test ilsa-surplus-arguments-raise-instead-of-aborting
      (ilsa/msg? 'arg-error "Argument Error: λ expected 0 arguments, but got 1"
                 '(if ((lambda () 1) 1) :t :f))
      (ilsa/msg? 'arg-error "Argument Error: λ expected 1 argument, but got 2"
                 '(if ((lambda (a) a) 1 2) :t :f))
      (ilsa/msg? 'arg-error "Argument Error: λ expected 2 arguments, but got 3"
                 '(if ((lambda (a b) a) 1 2 3) :t :f)))

;; The count reported is the real one, not just "one too many".
(test ilsa-surplus-count-is-the-count-received
      (ilsa/msg? 'arg-error "Argument Error: λ expected 0 arguments, but got 5"
                 '(if ((lambda () 1) 1 2 3 4 5) :t :f))
      (ilsa/msg? 'arg-error "Argument Error: λ expected 1 argument, but got 4"
                 '(if ((lambda (a) a) 1 2 3 4) :t :f)))

;; Under-application of the same inlined lambda was always graceful, and
;; still reports through `apply` rather than naming `λ` - so the two
;; directions give differently-worded messages for the same lambda.
;; Pinned as-is: the surplus case is the one that changed.
(test ilsa-missing-arguments-report-through-apply
      (ilsa/msg? 'arg-error "Argument Error: apply expected 2 arguments, but got 1"
                 '(if ((lambda (a b) a) 1) :t :f)))

;; A `&rest` parameter absorbs the surplus, which is why it never
;; reached the faulting path. Still the case, and still not an error.
(defun ilsa/rest-tail () ((lambda (a &rest r) r) 1 2 3 4))
(defun ilsa/rest-all () ((lambda (&rest r) r) 1 2 3))
(defun ilsa/exact () ((lambda (a) a) 7))
(test ilsa-rest-absorbs-the-surplus
      (eq? '(2 3 4) (ilsa/rest-tail))
      (eq? '(1 2 3) (ilsa/rest-all))
      (= 7 (ilsa/exact)))
