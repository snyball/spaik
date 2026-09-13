;;;
;;; `=` (reference equality) vs `eq?` (deep structural equality)
;;; across types.
;;;
;;; `eq?` is intended to recurse into any container and compare
;;; contents, regardless of type - see FIXME.md for the currently-open
;;; bug this file targets: `eq?` on `string` compares the underlying
;;; pointers directly instead of dereferencing and comparing the
;;; pointed-to bytes, and `eq?` on `table` is not yet implemented to
;;; do a structural comparison at all. Both cause `eq?` to wrongly
;;; report `false` for two separately-constructed, equal-content
;;; strings/tables - and, since `eq?` recurses, that same wrongness
;;; leaks into any `vec`/`cons` that contains a `string` or `table`.
;;;
;;; These tests are expected to FAIL on the current build (the
;;; `eq-string-*`, `eq-table-*` and `eq-nested-*` tests below) and
;;; PASS once `eq?` is fixed to dereference/recurse for every type.
;;; The `eq-baseline-*` tests already pass today and are here as
;;; regression coverage so a fix doesn't accidentally break the
;;; already-correct `vec`/`cons` recursion.
;;;
;;; NOTE: each clause in a `test` block must be a literal
;;; `(predicate arg-expr...)` form (see `lisp/test.lisp`) - it is NOT
;;; a general expression evaluator, so any fixture that needs `let`
;;; or multiple statements is built by a helper `defun` below instead
;;; of written inline in the `test` block.

(defun eqtest/same-vec-fixture ()
  (let ((v (vec 1 2 3)))
    (eq? v v)))

(defun eqtest/table-a-1 ()
  (let ((tbl (make-table)))
    (set (get tbl :k) 1)
    tbl))

(defun eqtest/table-b-1 ()
  (let ((tbl (make-table)))
    (set (get tbl :k) 1)
    tbl))

(defun eqtest/table-b-2 ()
  (let ((tbl (make-table)))
    (set (get tbl :k) 2)
    tbl))

;;; ---[ baseline: already correct today ]----------------------------

(test eq-baseline-primitives
      (eq? 1 1)
      (eq? 1.5 1.5)
      (eq? true true)
      (eq? false false)
      (eq? nil nil)
      (eq? 'a 'a)
      (not (eq? 1 2))
      (not (eq? true false))
      (not (eq? 'a 'b)))

(test eq-baseline-vec
      ;; two distinct, separately-built vecs with equal contents:
      ;; `=` (reference) is false, `eq?` (structural) is true.
      (eq? (vec 1 2 3) (vec 1 2 3))
      (not (= (vec 1 2 3) (vec 1 2 3)))
      (not (eq? (vec 1 2 3) (vec 1 2 4)))
      (not (eq? (vec 1 2 3) (vec 1 2)))
      (eqtest/same-vec-fixture))

(test eq-baseline-cons-and-list
      (eq? (cons 1 2) (cons 1 2))
      (not (= (cons 1 2) (cons 1 2)))
      (eq? '(1 2 3) '(1 2 3))
      (not (eq? '(1 2 3) '(1 2 4)))
      (not (eq? '(1 2 3) '(1 2))))

(test eq-baseline-vec2-vec3
      ;; fixed-size value types: no separate identity, so `=` and
      ;; `eq?` naturally agree.
      (eq? (vec2 1 2) (vec2 1 2))
      (= (vec2 1 2) (vec2 1 2))
      (eq? (vec3 1 2 3) (vec3 1 2 3))
      (= (vec3 1 2 3) (vec3 1 2 3)))

;;; ---[ currently broken: string ]------------------------------------

(test eq-string-structural
      ;; two separately-constructed strings with equal content must
      ;; be `eq?` (deep structural), even though they are not the same
      ;; reference.
      (eq? (concat "hel" "lo") (concat "hel" "lo"))
      (eq? "hello" (concat "hel" "lo"))
      (not (eq? (concat "hel" "lo") (concat "wor" "ld")))
      (not (eq? "hello" "world")))

;;; ---[ currently broken: table ]--------------------------------------

(test eq-table-structural
      ;; two separately-built tables with identical key/value pairs
      ;; must be `eq?` (deep structural), even though they are not the
      ;; same reference.
      (eq? (eqtest/table-a-1) (eqtest/table-b-1))
      (not (eq? (eqtest/table-a-1) (eqtest/table-b-2)))
      (eq? (make-table) (make-table)))

;;; ---[ currently broken: propagates into containers ]-----------------

(test eq-nested-string-and-table
      ;; the `string`/`table` bug above must not poison the otherwise-
      ;; correct `vec`/`cons` recursion once it's fixed: a `vec`
      ;; holding equal-content strings/tables must itself be `eq?`.
      (eq? (vec "x" "y") (vec "x" "y"))
      (not (eq? (vec "x" "y") (vec "x" "z")))
      (eq? (vec (eqtest/table-a-1)) (vec (eqtest/table-b-1)))
      (eq? (cons "a" "b") (cons "a" "b")))
