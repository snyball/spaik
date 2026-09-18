;;; What `string`/`repr` do when one object appears twice in a value,
;;; and where the `(...)` abbreviation comes from. Pinned as-is: the
;;; abbreviation on plain sharing looks wrong.

;; The printer keeps a set of every reference object it has already
;; visited in this print, not a stack of the ones it is currently
;; inside. So the second appearance of the same object prints as
;; `(...)` whether or not the structure is cyclic. The value itself is
;; unaffected - only the rendering is.
(defun pss/twice (x) (string (list x x)))

(test pss-second-appearance-abbreviates
      (= "((1 2) (...))" (pss/twice (list 1 2)))
      (= "((vec 1) (...))" (pss/twice (vec 1))))

;; It fires on objects that cannot be cyclic at all: an empty vec has no
;; children, and a string has none either.
(test pss-abbreviates-things-that-cannot-be-cyclic
      (= "((vec) (...))" (pss/twice (vec)))
      (= "(\"ab\" (...))" (pss/twice (concat "a" "b")))
      (= "((table) (...))" (pss/twice (make-table))))

;; Immediates are compared by value rather than identity, so repeating
;; one is printed in full.
(test pss-immediates-print-in-full
      (= "(7 7)" (pss/twice 7))
      (= "(foo foo)" (pss/twice 'foo))
      (= "(nil nil)" (pss/twice nil)))

;; Two distinct objects with equal contents both print in full, which is
;; what pins the effect to identity rather than to structural equality.
(defun pss/two-equal-lists () (string (list (list 1 2) (list 1 2))))

(test pss-equal-but-distinct-objects-print-in-full
      (= "((1 2) (1 2))" (pss/two-equal-lists)))

;; The set is per print call, so printing the same object twice in
;; separate calls is unaffected.
(defun pss/separate-calls (x) (list (string x) (string x)))

(test pss-the-set-is-per-call
      (eq? '("(1 2)" "(1 2)") (pss/separate-calls (list 1 2))))

;; A genuine cycle uses the same notation, so the rendering does not
;; distinguish "this is a loop" from "this object appeared earlier".
;; That ambiguity is the reason the behaviour above is worth pinning.
(defun pss/self-referential-vec ()
  (let ((v (vec 1)))
    (push v v)
    (string v)))

(test pss-a-real-cycle-prints-the-same-way
      (= "(vec 1 (...))" (pss/self-referential-vec)))

;; The value is intact behind the abbreviated rendering.
(defun pss/second-element (x) (car (cdr (list x x))))

(test pss-the-value-is-not-truncated
      (eq? '(1 2) (pss/second-element (list 1 2)))
      (= 2 (len (list (list 1 2) (list 1 2)))))
