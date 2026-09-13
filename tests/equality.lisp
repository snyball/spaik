;;;
;;; `=` (reference equality) vs `eq?` (deep structural equality)
;;; across types.
;;;
;;; `eq?` recurses into any container and compares contents,
;;; regardless of type. This previously did not hold for `string`
;;; (compared the underlying pointers directly instead of dereferencing
;;; and comparing the pointed-to bytes) or `table` (structural
;;; comparison was unimplemented) - see `fixed/eq-not-deep-structural-
;;; for-string-and-table.lisp` and FIXME.md's "Fixed" section; the
;;; `eq-string-structural`/`eq-table-structural`/
;;; `eq-nested-string-and-table` tests below are the regression
;;; coverage for that fix and now pass. The `eq-baseline-*` tests
;;; guard the types that were already correct (`vec`, `cons`/list,
;;; `vec2`/`vec3`/`vec4`) so a future change can't regress them.
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

(test eq-baseline-vec2-vec3-vec4
      ;; fixed-size linear-algebra value types (vec2/vec3/vec4): no
      ;; separate identity from content, so `=` and `eq?` must always
      ;; agree - both true for equal components, both false as soon
      ;; as any single component differs. (mat2/mat3/mat4 do not exist
      ;; in this build - see FIXME.md/ATTEMPTS.md - so are not covered
      ;; here; add matching `eq-baseline-mat*` cases below if/when
      ;; they're implemented.)
      (eq? (vec2 1 2) (vec2 1 2))
      (= (vec2 1 2) (vec2 1 2))
      (not (eq? (vec2 1 2) (vec2 1 3)))
      (not (= (vec2 1 2) (vec2 1 3)))
      (eq? (vec3 1 2 3) (vec3 1 2 3))
      (= (vec3 1 2 3) (vec3 1 2 3))
      (not (eq? (vec3 1 2 3) (vec3 1 2 4)))
      (not (= (vec3 1 2 3) (vec3 1 2 4)))
      (eq? (vec4 1 2 3 4) (vec4 1 2 3 4))
      (= (vec4 1 2 3 4) (vec4 1 2 3 4))
      (not (eq? (vec4 1 2 3 4) (vec4 1 2 3 5)))
      (not (= (vec4 1 2 3 4) (vec4 1 2 3 5))))

(test eq-baseline-mat
      ;; `mat` (2x2/3x3/4x4 matrices) does not exist in this build yet
      ;; (raises "Undefined Function" here - not gated behind anything
      ;; this test can detect ahead of time, so this whole `test`
      ;; block is EXPECTED TO FAIL until a build with `mat` lands).
      ;; Unlike the earlier `mat2`/`mat3`/`mat4` design, `mat` is a
      ;; single function that only accepts column vectors as args and
      ;; picks its return type (2x2/3x3/4x4) from how many are given:
      ;; 2 `vec2` columns -> a 2x2 matrix, 3 `vec3` columns -> 3x3, 4
      ;; `vec4` columns -> 4x4. Once it exists, each of those return
      ;; types should behave exactly like vec2/vec3/vec4 above: no
      ;; identity separate from content, so `=` and `eq?` must always
      ;; agree, for every arity `mat` supports.
      ;;
      ;; NOTE: this only tests `=`/`eq?` consistency, independent of
      ;; whether matrix construction itself is otherwise correct - it
      ;; does not target the separately-reported "duplicate pasted"
      ;; construction bug in the matrix code.

      ;; 2 columns -> 2x2
      (eq? (mat (vec2 1 0) (vec2 0 1)) (mat (vec2 1 0) (vec2 0 1)))
      (= (mat (vec2 1 0) (vec2 0 1)) (mat (vec2 1 0) (vec2 0 1)))
      (not (eq? (mat (vec2 1 0) (vec2 0 1)) (mat (vec2 1 0) (vec2 1 1))))
      (not (= (mat (vec2 1 0) (vec2 0 1)) (mat (vec2 1 0) (vec2 1 1))))

      ;; 3 columns -> 3x3
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1))
           (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)))
      (= (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1))
         (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)))
      (not (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1))
                (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 2))))
      (not (= (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1))
              (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 2))))

      ;; 4 columns -> 4x4
      (eq? (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1))
           (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1)))
      (= (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1))
         (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1)))
      (not (eq? (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1))
                (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 2))))
      (not (= (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1))
              (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 2))))

      ;; different arities (hence different return types/shapes) must
      ;; never be considered equal to one another, by either operator.
      (not (eq? (mat (vec2 1 0) (vec2 0 1))
                (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1))))
      (not (= (mat (vec2 1 0) (vec2 0 1))
              (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)))))

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
