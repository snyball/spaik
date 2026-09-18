;; Pins what `fmt`/`println` PRODUCE: named and positional substitution,
;; and every argument actually consumed. The four error paths are
;; asserted in tests/error-builtin-throws.lisp.

(define fmt-x 7)

;; Named substitution - the only form that worked before the fix.
(defun fmt-named () (fmt "x={fmt-x}"))

;; Positional `{}` consumes one argument each, left to right.
(defun fmt-positional () (fmt "{} + {}" 1 2))
(defun fmt-adjacent () (fmt "{}{}{}" 1 2 3))
(defun fmt-only-placeholder () (fmt "{}" 42))
(defun fmt-edges () (fmt "{}mid{}" 'a 'b))

;; Named and positional mix; the named reference does not consume an
;; argument, so both `{}` still see 1 and 2 in order.
(defun fmt-mixed () (fmt "{fmt-x} {} {fmt-x} {}" 1 2))

;; No placeholders and no arguments still round-trips the literal.
(defun fmt-plain () (fmt "plain"))
(defun fmt-empty () (fmt ""))

;; Each argument expression is emitted once, in source order - the bug
;; report's `{}`-duplicates-the-previous-argument half.
(define fmt-n 0)
(defun fmt-bump () (set fmt-n (+ fmt-n 1)) fmt-n)
(defun fmt-eval-order ()
  (set fmt-n 0)
  (fmt "{} {} {}" (fmt-bump) (fmt-bump) (fmt-bump)))

;; `println`/`print` inherit the fixed behaviour through their expansion.
(defun fmt-via-println () (println "x={} y={}" fmt-x 9))
(defun fmt-via-print () (print "a{}b" 5))

(test fmt-format-arguments
      ;; named substitution still works
      (eq? "x=7" (fmt-named))
      ;; positional arguments are consumed, not dropped
      (eq? "1 + 2" (fmt-positional))
      (eq? "123" (fmt-adjacent))
      (eq? "42" (fmt-only-placeholder))
      (eq? "amidb" (fmt-edges))
      (eq? "7 1 7 2" (fmt-mixed))
      ;; degenerate format strings
      (eq? "plain" (fmt-plain))
      (eq? "" (fmt-empty))
      ;; arguments evaluated once each, in order
      (eq? "1 2 3" (fmt-eval-order))
      (= 3 fmt-n)
      ;; the `println`/`print` wrappers substitute rather than drop
      ;; both return the string they emitted
      (eq? "x=7 y=9" (fmt-via-println))
      (eq? "a5b" (fmt-via-print)))
