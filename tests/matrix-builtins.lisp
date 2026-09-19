;;; `mat` and the matrix helpers: what each shape constructs, which
;;; operators accept a matrix, and how the errors read.
;;; Angles are checked at 0 only - see the note on the rotation block.

(defun mtx/catch (tag form) (catch tag (eval form)))

(defun mtx/starts-with? (prefix s)
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

(defun mtx/msg? (tag prefix form)
  (let ((v (mtx/catch tag form)))
    (and (string? v) (mtx/starts-with? prefix v))))

;;; ---[ construction ]--------------------------------------------------

;; `mat` is one constructor for three types. It takes column vectors and
;; reads the shape off them: 2 `vec2` -> `mat2`, 3 `vec3` -> `mat3`,
;; 4 `vec4` -> `mat4`. There is no `mat2`/`mat3`/`mat4` constructor of
;; its own - those names are types, not functions.
(defun mtx/m2 () (mat (vec2 1 0) (vec2 0 1)))
(defun mtx/m3 () (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)))
(defun mtx/m4 () (mat (vec4 1 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1)))

(test mtx-mat-picks-its-type-from-the-column-count
      (eq? 'mat2 (type-of (mtx/m2)))
      (eq? 'mat3 (type-of (mtx/m3)))
      (eq? 'mat4 (type-of (mtx/m4)))
      ;; columns are kept in the order given, and print as columns
      (eq? "(mat2 (1 2) (3 4))" (string (mat (vec2 1 2) (vec2 3 4)))))

;; The column count chooses the type BEFORE the columns are checked, so
;; the type error names the width that the count implied - three
;; arguments ask for `vec3` even when all three are `vec2`.
(test mtx-mat-rejects-mismatched-columns
      (mtx/msg? 'type-error "Type Error: Expected vec2 but got vec3"
                '(mat (vec2 1 2) (vec3 3 4 5)))
      (mtx/msg? 'type-error "Type Error: Expected vec3 but got vec2"
                '(mat (vec2 1 0) (vec2 0 1) (vec2 1 1)))
      (mtx/msg? 'type-error "Type Error: Expected vec2 but got integer"
                '(mat 1 2))
      ;; 2 to 4 columns, nothing else
      (mtx/msg? 'arg-error "Argument Error: expected from 2 to 4 argument"
                '(mat (vec2 1 2)))
      (mtx/msg? 'arg-error "Argument Error: expected from 2 to 4 argument"
                '(mat)))

;; Neither of these two messages says which function raised it, while
;; every other builtin names itself somehow ("in car", "of (iter ...)",
;; a leading "vec2"). Pinned as it currently reads; if a name appears,
;; that should be a deliberate change.
;;
;; This comment used to claim they were "the only ones in this build".
;; That was never checked and is false: under-calling all 176 names in
;; `(functions)` finds `(error)` reporting "Argument Error: expected
;; from 1 to 2 arguments, but got 0" with no name either. Pinned just
;; below so the pair stays honest.
(test mtx-mat-errors-do-not-name-mat
      (not (mtx/msg? 'arg-error "Argument Error: mat " '(mat)))
      (not (mtx/msg? 'type-error "Type Error: Expected vec2 in mat" '(mat 1 2))))

;; `error` is the other one, and is not a matrix builtin at all - it is
;; pinned here only to keep the two facts next to each other, since the
;; claim above is about how many there are.
(test mtx-error-builtin-also-names-nothing
      (mtx/msg? 'arg-error "Argument Error: expected from 1 to 2 arguments, but got 0"
                '(error))
      (not (mtx/msg? 'arg-error "Argument Error: error " '(error))))

;;; ---[ the affine helpers ]--------------------------------------------

;; `scale` and `translate` take ONE vector and build the homogeneous
;; matrix one size up: a `vec2` gives a `mat3`, a `vec3` gives a `mat4`.
;; `translate` puts the offset in the last COLUMN, matching the
;; column-major printing above.
(defun mtx/scale2 () (scale (vec2 2 3)))
(defun mtx/translate2 () (translate (vec2 5 6)))

(test mtx-scale-and-translate-go-one-size-up
      (eq? 'mat3 (type-of (scale (vec2 2 3))))
      (eq? 'mat4 (type-of (scale (vec3 2 3 4))))
      (eq? 'mat3 (type-of (translate (vec2 5 6))))
      (eq? 'mat4 (type-of (translate (vec3 5 6 7))))
      (eq? (mat (vec3 2 0 0) (vec3 0 3 0) (vec3 0 0 1)) (mtx/scale2))
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 5 6 1)) (mtx/translate2)))

;; Rotations are checked at angle 0 only: every other angle goes through
;; `sin`/`cos` and lands on values like -0.00000004371139, which no
;; exact comparison can pin. At 0 the result is the identity, except
;; that the zero produced by `-sin 0` prints as `-0`; `eq?` still holds.
(test mtx-rotations-are-the-identity-at-zero
      (eq? (mat (vec2 1 0) (vec2 0 1)) (mat2-rot 0.0))
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)) (mat3-rot-x 0.0))
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)) (mat3-rot-y 0.0))
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 0 0 1)) (mat3-rot-z 0.0))
      (eq? (mtx/m4) (mat4-rot-x 0.0))
      (eq? (mtx/m4) (mat4-rot-y 0.0))
      (eq? (mtx/m4) (mat4-rot-z 0.0)))

;;; ---[ what you can do with one ]---------------------------------------

;; Matrix-vector multiplication exists for 2x2 and 3x3 and is missing for
;; 4x4, so the 2D affine idiom works and the 3D one does not. Only the
;; working half is asserted here: `Operation Not Supported` is one of the
;; few errors that is NOT converted into a catchable throw inside `eval`,
;; so `(* mat4 vec4)` cannot be exercised from a test without killing the
;; run. The missing half, for the record:
;;
;;     (* (mat4 ...)            (vec4 1 2 3 4))  => Operation Not
;;     (* (translate (vec3 ...)) (vec4 1 2 3 1))    Supported:
;;                                                  (* mat4 vec4)
;;
;; which leaves `scale`/`translate`/`mat4-rot-*` on a `vec3` building a
;; matrix that nothing can apply.
(test mtx-multiplication-stops-at-3x3
      (eq? (vec2 23 34) (* (mat (vec2 1 2) (vec2 3 4)) (vec2 5 6)))
      (eq? (vec3 5 6 7) (* (mtx/m3) (vec3 5 6 7)))
      (eq? (vec3 11 22 1) (* (translate (vec2 10 20)) (vec3 1 2 1)))
      (eq? (vec3 2 6 1) (* (scale (vec2 2 3)) (vec3 1 2 1))))

;; A matrix is a value, not a sequence: it can be stored, cloned,
;; compared and printed, but the indexing and iteration entry points all
;; refuse it - including `get`, which does accept `vec2` and `vec3`.
(test mtx-a-matrix-is-not-a-sequence
      (eq? (mtx/m2) (clone (mtx/m2)))
      (eq? (vec (mtx/m2)) (vec (mtx/m2)))
      (mtx/msg? 'type-error "Type Error: Expected one of vec, vec2, vec3, table in get"
                '(if (get (mtx/m2) 0) 1 2))
      (mtx/msg? 'type-error "Type Error: Expected one of nil, cons, string, vec, table"
                '(if (len (mtx/m2)) 1 2))
      (mtx/msg? 'type-error "Type Error: Expected one of list, string, vec, table for argument 1 of (iter ...)"
                '(if (iter (mtx/m2)) 1 2)))
