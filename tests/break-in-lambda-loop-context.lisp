;;; A lambda does not inherit the loop context of the form that built it.
;;; `break` needs a loop in the SAME function; a closure's own loop counts.
;;; Companion to tests/break-in-cond-clause.lisp.

;; `(lambda (x) (break x))` written inside a `loop` is now REJECTED at
;; compile time with "Syntax Error: Operator break not allowed outside
;; of loop context", the same message a bare `(break 5)` gets.
;;
;; That rejection cannot be asserted here: a Syntax Error is not
;; catchable - no tag converts it - and it ends the run where it stands,
;; so a file containing the form could not pass at all. What is pinned
;; below is the other side of the line: the shapes that MUST keep
;; compiling, which is what a fix for this could plausibly break.
;;
;; It used to be accepted, and compiled to a jump with no valid target.
;; With no inner loop the unit failed to LINK, leaking the compiler's
;; internal label into a user-facing "Link Error: Symbol not found
;; loop_end#2" before any top-level form ran. With an inner loop it was
;; worse: the outer `break` bound to the inner loop's end label, became
;; a self-jump, spun forever, and printed raw unsigned VM stack slots
;; (`1818u`, `0u`) as though they were ordinary values.

;; A lambda carrying its OWN loop is the legal shape and stays legal:
;; the `break` targets that loop, not anything outside the closure.
(define blc/own-loop (lambda (x) (loop (break x))))
(test blc-lambda-with-its-own-loop-breaks-that-loop
      (= 42 (blc/own-loop 42)))

;; The same through a returned closure, with the break reached
;; conditionally and carrying an accumulated value rather than an
;; argument - a real early exit, not a one-shot jump.
(defun blc/make-summer ()
  (lambda (n)
    (let ((s 0) (i 0))
      (loop
       (when (>= i n) (break s))
       (set s (+ s i))
       (set i (+ i 1))))))
(defun blc/sum-below (n) ((blc/make-summer) n))
(test blc-returned-closure-breaks-its-own-loop
      (= 10 (blc/sum-below 5))
      (= 0 (blc/sum-below 0))
      (= 45 (blc/sum-below 10)))

;; Building a closure inside a loop is fine as long as the closure does
;; not itself break outward. This is the shape the bug was found in,
;; minus the offending `break`, and it must keep working.
(define blc/built nil)
(defun blc/build ()
  (loop
   (set blc/built (lambda (x) (* x 2)))
   (break :built)))
(defun blc/build-then-call (x) (blc/build) (blc/built x))
(test blc-closure-built-inside-a-loop-still-works
      (eq? :built (blc/build))
      (= 42 (blc/build-then-call 21)))

;; `break` directly in a loop in a named function was always accepted
;; and is the control for the rule: it is the enclosing FUNCTION that
;; must supply the loop, not the enclosing source text.
(defun blc/plain () (loop (break :ok)))
(test blc-break-in-a-plain-defun-loop
      (eq? :ok (blc/plain)))
