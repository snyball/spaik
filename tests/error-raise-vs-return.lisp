;;; Proof that each converted error really RAISES rather than returning a
;;; value: the raise is wrapped in an `if` inside the eval'd form, so a
;;; return would show up as the branch value instead of the payload.

;; Why this file exists. `(catch tag (eval form))` answers the payload
;; when `form` raises and `form`'s value when it does not, so on its own
;; it cannot tell the two apart - a test that only checks the answer
;; passes either way. Wrapping the suspect call in an `if` INSIDE the
;; evaluated form fixes that: if it raises, unwinding skips both branches
;; and the catch answers the payload; if it merely returns, one of the
;; two branch markers comes back. Every marker below is a keyword, which
;; no payload ever is.

(defun rvr/catch (tag form) (catch tag (eval form)))

;; True when `form` aborted rather than answering a branch marker.
(defun rvr/raised? (tag form)
  (let ((v (rvr/catch tag form)))
    (if (eq? v :rvr-then) false (not (eq? v :rvr-else)))))

;;; ---[ the discriminator itself ]--------------------------------------

(defun rvr/truthy () (rvr/catch 'type-error '(if 1 :rvr-then :rvr-else)))
(defun rvr/falsey () (rvr/catch 'type-error '(if nil :rvr-then :rvr-else)))

(test rvr-discriminator
      ;; a form that does not raise answers a marker, either branch
      (eq? :rvr-then (rvr/truthy))
      (eq? :rvr-else (rvr/falsey))
      (not (rvr/raised? 'type-error '(if 1 :rvr-then :rvr-else)))
      (not (rvr/raised? 'type-error '(if nil :rvr-then :rvr-else)))
      ;; and one that does raise answers neither
      (rvr/raised? 'type-error '(if (car 5) :rvr-then :rvr-else)))

;;; ---[ every tag: the raise really aborts ]-----------------------------

(test rvr-errors-abort-the-form
      (rvr/raised? 'type-error '(if (car 5) :rvr-then :rvr-else))
      (rvr/raised? 'arg-error '(if (car) :rvr-then :rvr-else))
      (rvr/raised? 'index-error '(if (get (vec) 0) :rvr-then :rvr-else))
      (rvr/raised? 'divide-by-zero '(if (/ 1 0) :rvr-then :rvr-else))
      (rvr/raised? 'divide-by-zero '(if (% 1 0) :rvr-then :rvr-else))
      ;; via `not`: in a BARE `if` condition the i32 check is skipped
      ;; outright, and the un-narrowed value is used. One intervening
      ;; call restores it, which is what `not` is doing here.
      (rvr/raised? 'undefined-variable '(if rvr-no-such-global :rvr-then :rvr-else))
      (rvr/raised? 'undefined-function '(if (rvr-no-such-fn) :rvr-then :rvr-else))
      (rvr/raised? 'unimplemented '(if (read "1") :rvr-then :rvr-else))
      (rvr/raised? 'module-not-found '(if (require rvr-no-such-module) :rvr-then :rvr-else))
      (rvr/raised? 'reference-not-allowed '(if (error 'rvr-k (list 1)) :rvr-then :rvr-else))
      ;; the `error` builtin, and fmt's expansion-time diagnostics
      (rvr/raised? 'rvr-k '(if (error 'rvr-k 1) :rvr-then :rvr-else))
      (rvr/raised? 'trailing-delimiter '(if (fmt "a}b") :rvr-then :rvr-else))
      (rvr/raised? 'unclosed-delimiter '(if (fmt "a{b") :rvr-then :rvr-else))
      (rvr/raised? 'not-enough-format-arguments '(if (fmt "{}") :rvr-then :rvr-else))
      (rvr/raised? 'unused-format-parameters '(if (fmt "x" 1) :rvr-then :rvr-else)))

;;; ---[ next past the end RETURNS, it does not raise ]--------------------

;; The iterator has to be a global: `eval` compiles in the global
;; environment and cannot see a caller's `let`.
(define rvr/it nil)

(defun rvr/exhausted-next ()
  (set rvr/it (iter (list 1)))
  (next rvr/it)
  (rvr/catch 'iter-stop '(if (next rvr/it) :rvr-then :rvr-else)))

(defun rvr/empty-next ()
  (set rvr/it (iter (list)))
  (rvr/catch 'iter-stop '(if (next rvr/it) :rvr-then :rvr-else)))

(defun rvr/exhausted-value ()
  (set rvr/it (iter (list 1)))
  (next rvr/it)
  (next rvr/it))

(test rvr-next-past-the-end-does-not-raise
      ;; It answers the `<ζ>-iter-stop` sentinel as an ordinary VALUE, so
      ;; the `if` around it runs and takes the then-branch - the sentinel
      ;; is truthy. Nothing is tagged `iter-stop`; that tag is not
      ;; reachable this way, which the tail-position form of this test
      ;; could not show.
      (eq? :rvr-then (rvr/exhausted-next))
      (eq? :rvr-then (rvr/empty-next))
      (not (rvr/raised? 'iter-stop '(if (next rvr/it) :rvr-then :rvr-else)))
      ;; the sentinel itself, and what recognizes it
      (iter-end? (rvr/exhausted-value))
      (not (nil? (rvr/exhausted-value))))

;;; ---[ nothing is raised when nothing is wrong ]--------------------------

(test rvr-good-calls-do-not-raise
      ;; the same builtins, called correctly, reach a branch marker - so
      ;; the assertions above are about the bad argument, not the builtin
      (not (rvr/raised? 'type-error '(if (car (list 1)) :rvr-then :rvr-else)))
      (not (rvr/raised? 'index-error '(if (get (vec 1) 0) :rvr-then :rvr-else)))
      (not (rvr/raised? 'divide-by-zero '(if (/ 4 2) :rvr-then :rvr-else)))
      (not (rvr/raised? 'conversion-error '(if (* 2 2) :rvr-then :rvr-else)))
      (not (rvr/raised? 'trailing-delimiter '(if (fmt "a{}b" 1) :rvr-then :rvr-else)))
      (not (rvr/raised? 'module-not-found '(if (len (list)) :rvr-then :rvr-else))))
