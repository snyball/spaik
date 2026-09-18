;;; A non-local exit crossing an `eval` boundary unwinds to the `catch`
;;; instead of resuming at the `eval`, from every argument position.
;;; Companion to tests/throw-across-eval-boundary.lisp.

(defun eup/catch (tag form) (catch tag (eval form)))

(defun eup/starts-with? (prefix s)
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

;; ------------------------------------------------------------------
;; A `throw` from a LATER argument position.
;;
;; The arguments to the left of the `eval` have already been written
;; into the call's slots when the unwind happens. They used to be
;; stranded there and come back as raw untyped memory - `(0u 3)` where
;; `(:a ...)` was written - which crashed whatever dispatched on the
;; type of one, silently ended the program, or swallowed the throw and
;; computed on the payload instead. All four shapes below are now the
;; payload, and nothing to the left of the `eval` is consulted at all.

(defun eup/arg-1 ()  (catch 'eup-k (list (eval '(throw 'eup-k 3)) :b)))
(defun eup/arg-2 ()  (catch 'eup-k (list :a (eval '(throw 'eup-k 3)))))
(defun eup/arg-3 ()  (catch 'eup-k (list :a :b (eval '(throw 'eup-k 3)))))
(defun eup/arg-refs ()
  (catch 'eup-k (list :a (vec 1) "s" (eval '(throw 'eup-k 3)))))

;; `+` consuming the result is the shape that used to swallow the
;; throw outright and answer 4.
(defun eup/arg-arith () (catch 'eup-k (+ 1 (eval '(throw 'eup-k 3)))))
(defun eup/arg-cons ()  (catch 'eup-k (cons 1 (eval '(throw 'eup-k 3)))))

;; The program has to still be running afterwards. The second-argument
;; shape inside a `defun` used to end the process where it stood - no
;; output, empty stderr, exit 0 - so a caller could not tell it from a
;; clean finish.
(defun eup/still-running ()
  (eup/arg-2)
  (eup/arg-refs)
  (let ((n 0))
    (dolist (x '(1 2 3))
      (set n (+ n x)))
    n))

(test eup-throw-from-a-later-argument-unwinds
      (= 3 (eup/arg-1))
      (= 3 (eup/arg-2))
      (= 3 (eup/arg-3))
      (= 3 (eup/arg-refs))
      (= 3 (eup/arg-arith))
      (= 3 (eup/arg-cons))
      (= 6 (eup/still-running)))

;; ------------------------------------------------------------------
;; A CONVERTED error - an interpreter error raised inside `eval` and
;; delivered to a `catch` outside it - unwinds too.
;;
;; It used to resume at the `eval` call site with the message as
;; `eval`'s value, so everything between the two ran on the payload:
;; the counter below reached 1, `(list (eval ...))` answered a LIST
;; holding the message, `(len (eval ...))` answered the message's
;; length, and an `if` around the raise took its then-branch. Each
;; assertion here is one of those, inverted.

(define eup/n 0)
(defun eup/bump (x) (set eup/n (+ eup/n 1)) x)

(defun eup/calls-after-the-error ()
  (set eup/n 0)
  (catch 'type-error (eup/bump (eval '(car 5))))
  eup/n)

(defun eup/payload? (v)
  (and (string? v)
       (eup/starts-with? "Type Error: Expected cons in car" v)))

(defun eup/wrapped ()   (catch 'type-error (list (eval '(car 5)))))
(defun eup/sole-arg ()  (catch 'type-error (len (eval '(car 5)))))
(defun eup/condition () (catch 'type-error (if (eval '(car 5)) :then :else)))

;; A converted error from a non-first argument position used to spin
;; the VM forever, re-executing the enclosing top-level form at 100%
;; CPU with no output.
(defun eup/late-arg ()  (catch 'type-error (list :ok (eval '(car 5)))))
(defun eup/late-arg-2 () (catch 'type-error (cons 1 (eval '(car 5)))))

(test eup-converted-error-unwinds
      (= 0 (eup/calls-after-the-error))
      (eup/payload? (eup/wrapped))
      (eup/payload? (eup/sole-arg))
      (eup/payload? (eup/condition))
      (eup/payload? (eup/late-arg))
      (eup/payload? (eup/late-arg-2)))

;; ------------------------------------------------------------------
;; A `catch` written INSIDE the evaluated form is a recovery point in
;; its own right: the rest of the evaluated form runs after it, and
;; `eval` answers that form's value rather than the payload.
;;
;; This is the shape the style guide still tells tests not to rely on,
;; because for a long time it silently discarded everything between the
;; inner `catch` and the `eval`. What it discarded is exactly what the
;; two assertions below check for.

(defun eup/inner-then-more ()
  (eval '(progn (catch 'type-error (eval '(car 5))) :after)))

(defun eup/inner-in-a-list ()
  (eval '(list :inner (catch 'type-error (eval '(car 5))))))

(defun eup/inner-head () (car (eup/inner-in-a-list)))
(defun eup/inner-tail () (eup/payload? (car (cdr (eup/inner-in-a-list)))))

(test eup-catch-inside-eval-is-a-recovery-point
      (eq? :after (eup/inner-then-more))
      (= 2 (len (eup/inner-in-a-list)))
      (eq? :inner (eup/inner-head))
      (eup/inner-tail))
