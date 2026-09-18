;;; `=` (reference equality) vs `eq?` (deep structural equality) across
;;; types. `eq?` recurses into any container and compares contents;
;;; `string` and `table` were the two that once did not.

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
      ;; as any single component differs. Matrices are `mat` in this
      ;; build and get their own block below.
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
      ;; `mat` is a single constructor that takes column vectors and
      ;; picks its return type from how many it is given: 2 `vec2`
      ;; columns -> `mat2`, 3 `vec3` -> `mat3`, 4 `vec4` -> `mat4`.
      ;; Those three behave like vec2/vec3/vec4 above - no identity
      ;; separate from content, so `=` and `eq?` must always agree.
      ;;
      ;; NOTE: this only tests `=`/`eq?` consistency, independent of
      ;; whether matrix construction itself is otherwise correct.

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

;;; ---[ string: was reference-only, now structural ]-------------------

(test eq-string-structural
      ;; two separately-constructed strings with equal content must
      ;; be `eq?` (deep structural), even though they are not the same
      ;; reference.
      (eq? (concat "hel" "lo") (concat "hel" "lo"))
      (eq? "hello" (concat "hel" "lo"))
      (not (eq? (concat "hel" "lo") (concat "wor" "ld")))
      (not (eq? "hello" "world")))

;;; ---[ table: was reference-only, now structural ]--------------------

(test eq-table-structural
      ;; two separately-built tables with identical key/value pairs
      ;; must be `eq?` (deep structural), even though they are not the
      ;; same reference.
      (eq? (eqtest/table-a-1) (eqtest/table-b-1))
      (not (eq? (eqtest/table-a-1) (eqtest/table-b-2)))
      (eq? (make-table) (make-table)))

;;; ---[ and it propagates into containers ]----------------------------

(test eq-nested-string-and-table
      ;; `string` and `table` were once compared by reference while
      ;; `vec`/`cons` recursed structurally. A container holding
      ;; equal-content strings/tables must itself be `eq?`.
      (eq? (vec "x" "y") (vec "x" "y"))
      (not (eq? (vec "x" "y") (vec "x" "z")))
      (eq? (vec (eqtest/table-a-1)) (vec (eqtest/table-b-1)))
      (eq? (cons "a" "b") (cons "a" "b")))

;;; ---[ cycles: the identity short-circuit ]---------------------------

;; `eq?` compares an object with ITSELF without walking it, so a
;; structure that contains a reference cycle is answered immediately.
;; That check is all that stands between these cases and unbounded
;; recursion: `eq?` has no visited set, so comparing two DISTINCT
;; cyclic structures still descends forever and takes the interpreter
;; with it. Only the self-comparison is pinned here; the pair case is
;; a live crash and has no business in a suite that must exit 0.
;;
;; The cycle has to be built before the comparison runs. A top-level
;; `define` initialiser is evaluated ahead of the rest of the file, so
;; `(define r (eq? v v))` would compare the vector while it is still
;; empty and prove nothing - hence the helper.
(defun eqtest/self-cycle-vec ()
  (let ((v (vec)))
    (push v v)
    (eq? v v)))

(defun eqtest/self-cycle-table ()
  (let ((tbl (make-table)))
    (set (get tbl :self) tbl)
    (eq? tbl tbl)))

(defun eqtest/self-cycle-member ()
  (let ((v (vec)))
    (push v v)
    (member? v (list v))))

;; A cyclic operand against a plain one terminates for a different
;; reason: they differ at the first level, so the walk answers before
;; it has anywhere to descend to.
(defun eqtest/cycle-vs-shorter ()
  (let ((v (vec)))
    (push v v)
    (member? v (list (vec)))))

(test eq-self-comparison-survives-a-cycle
      (eqtest/self-cycle-vec)
      (eqtest/self-cycle-table)
      (= true (eqtest/self-cycle-member))
      (nil? (eqtest/cycle-vs-shorter)))
