;;; The exact wording of Argument Error, including which of the two
;;; counts the "argument"/"arguments" plural agrees with. Every other
;;; error test in this tree compares prefixes, which stops short of it.

(defun amt/catch (tag form) (catch tag (eval form)))
(defun amt/starts-with? (prefix s)
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
(defun amt/msg? (tag prefix form)
  (let ((v (amt/catch tag form)))
    (and (string? v) (amt/starts-with? prefix v))))

;; The plural agrees with the number EXPECTED - the number the word is
;; attached to - and not with the number received. One function
;; therefore has one spelling, however badly it is called.
;;
;; `apply` shows it on its own: it expects 2, and both of these read
;; "arguments" even though the first received exactly 1.
(test amt-plural-follows-the-expected-count
      (amt/msg? 'arg-error "Argument Error: apply expected 2 arguments, but got 1"
                '(if (apply +) 1 2))
      (amt/msg? 'arg-error "Argument Error: apply expected 2 arguments, but got 4"
                '(if (apply + 1 2 (list 3)) 1 2)))

;; An expected count of exactly 1 is the only exact count that reads
;; singular; 0, or 2 and up, read plural, whatever arrived.
(test amt-only-an-expected-one-is-singular
      (amt/msg? 'arg-error "Argument Error: car expected 1 argument, but got 0"
                '(if (car) 1 2))
      (amt/msg? 'arg-error "Argument Error: car expected 1 argument, but got 2"
                '(if (car 1 2) 1 2))
      (amt/msg? 'arg-error "Argument Error: cons expected 2 arguments, but got 1"
                '(if (cons 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: cons expected 2 arguments, but got 3"
                '(if (cons 1 2 3) 1 2)))

;; Lisp-defined functions take the same rule, and they are the only way
;; to reach the 0 case: no builtin here expects nothing. A `defun`
;; reports its own name; a bare `lambda` reports as `λ`.
(defun amt/f0 () 1)
(defun amt/f1 (a) a)
(defun amt/f2 (a b) a)
(define amt/lam (lambda (a) a))
(test amt-lambda-arity-takes-the-same-rule
      (amt/msg? 'arg-error "Argument Error: amt/f0 expected 0 arguments, but got 1"
                '(if (amt/f0 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/f1 expected 1 argument, but got 0"
                '(if (amt/f1) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/f2 expected 2 arguments, but got 1"
                '(if (amt/f2 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/f2 expected 2 arguments, but got 3"
                '(if (amt/f2 1 2 3) 1 2))
      (amt/msg? 'arg-error "Argument Error: λ expected 1 argument, but got 0"
                '(if (amt/lam) 1 2)))

;; "at least N" agrees with N by the same rule - singular only at 1.
(defun amt/r1 (a &rest b) a)
(defun amt/r2 (a b &rest c) a)
(test amt-at-least-n-agrees-with-n
      (amt/msg? 'arg-error "Argument Error: amt/r1 expected at least 1 argument, but got 0"
                '(if (amt/r1) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/r2 expected at least 2 arguments, but got 1"
                '(if (amt/r2 1) 1 2)))

;; A range is always plural, "from 0 to 1" included, where neither bound
;; is above one. Only the exact and "at least" forms ever go singular.
(defun amt/o0 (&opt a) a)
(defun amt/o1 (a &opt b) a)
(test amt-a-range-is-always-plural
      (amt/msg? 'arg-error "Argument Error: nth expected from 2 to 3 arguments, but got 1"
                '(if (nth 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/o0 expected from 0 to 1 arguments, but got 2"
                '(if (amt/o0 1 2) 1 2))
      (amt/msg? 'arg-error "Argument Error: amt/o1 expected from 1 to 2 arguments, but got 0"
                '(if (amt/o1) 1 2)))

;; These four used to report the interpreter's internal snake_case `fn`
;; name (`is_void`, `split_list`, `sort_inplace`, `reverse_inplace`),
;; which is not callable and is not in `(functions)`. They now report
;; the name the caller typed. Pinned so a regression is loud.
(test amt-bang-builtins-and-void-name-themselves
      (amt/msg? 'arg-error "Argument Error: void? expected 1 argument, but got 0"
                '(if (void?) 1 2))
      (amt/msg? 'arg-error "Argument Error: split! expected 1 argument, but got 0"
                '(if (split!) 1 2))
      (amt/msg? 'arg-error "Argument Error: sort! expected 1 argument, but got 0"
                '(if (sort!) 1 2))
      (amt/msg? 'arg-error "Argument Error: reverse! expected 1 argument, but got 0"
                '(if (reverse!) 1 2))
      (not (elem? 'split_list (functions)))
      (elem? 'split! (functions)))

;; The matrix-rotation constructors were the other half of that group -
;; they reported `mat2_rot`, `mat3_rot_x` and so on, differing from the
;; lisp name only in punctuation. They name themselves now too.
(test amt-matrix-rotation-constructors-name-themselves
      (amt/msg? 'arg-error "Argument Error: mat2-rot expected 1 argument, but got 0"
                '(if (mat2-rot) 1 2))
      (amt/msg? 'arg-error "Argument Error: mat3-rot-x expected 1 argument, but got 0"
                '(if (mat3-rot-x) 1 2))
      (amt/msg? 'arg-error "Argument Error: mat4-rot-z expected 1 argument, but got 0"
                '(if (mat4-rot-z) 1 2))
      (amt/msg? 'arg-error "Argument Error: translate expected 1 argument, but got 0"
                '(if (translate) 1 2)))

;; Two members of that group are left, and neither names anything you
;; can call. `sys/freeze` reports the bare `freeze` - the namespace
;; prefix is dropped rather than the name being snake_case - and `%`
;; still answers to `modulo`, pinned further down with its type error.
(test amt-two-builtins-still-report-an-uncallable-name
      (amt/msg? 'arg-error "Argument Error: freeze expected 1 argument, but got 0"
                '(if (sys/freeze) 1 2))
      (not (elem? 'freeze (functions)))
      (elem? 'sys/freeze (functions))
      (not (elem? 'modulo (functions)))
      (elem? '% (functions)))

;; `error` used to carry no name at all - "Argument Error: expected from
;; 1 to 2 arguments, but got 0" - which left a caller nothing to search
;; for. It names itself now. `mat` is the last builtin that does not.
(test amt-error-builtin-names-itself
      (amt/msg? 'arg-error "Argument Error: error expected from 1 to 2 arguments, but got 0"
                '(if (error) 1 2))
      (amt/msg? 'arg-error "Argument Error: expected from 2 to 4 arguments, but got 0"
                '(if (mat) 1 2)))

;; `error` used to pay for that with the other number: its RECEIVED
;; count was a constant, so three arguments and eleven both read "but
;; got 0", where every other range-arity builtin - `nth` here, and
;; `throw` and `mat` - reported what actually arrived. It counts for
;; real now, the tag argument included, and on the `apply` path too.
(test amt-error-reports-the-count-it-received
      (amt/msg? 'arg-error "Argument Error: error expected from 1 to 2 arguments, but got 3"
                '(if (error 'amt-k 1 2) 1 2))
      (amt/msg? 'arg-error "Argument Error: error expected from 1 to 2 arguments, but got 11"
                '(if (error 'amt-k 1 2 3 4 5 6 7 8 9 10) 1 2))
      (amt/msg? 'arg-error "Argument Error: error expected from 1 to 2 arguments, but got 3"
                '(if (apply error (list 'amt-k 1 2)) 1 2))
      (amt/msg? 'arg-error "Argument Error: nth expected from 2 to 3 arguments, but got 4"
                '(if (nth 1 (vec 1) 2 3) 1 2))
      (amt/msg? 'arg-error "Argument Error: nth expected from 2 to 3 arguments, but got 6"
                '(if (nth 1 (vec 1) 2 3 4 5) 1 2)))

;; The neighbouring predicates name themselves, which is what made the
;; group above look like omissions rather than a convention.
(test amt-most-builtins-report-their-own-name
      (amt/msg? 'arg-error "Argument Error: nil? expected 1 argument, but got 0"
                '(if (nil?) 1 2))
      (amt/msg? 'arg-error "Argument Error: unsigned-integer? expected 1 argument, but got 0"
                '(if (unsigned-integer?) 1 2))
      (amt/msg? 'arg-error "Argument Error: keyword-name expected 1 argument, but got 0"
                '(if (keyword-name) 1 2)))

;; The variadic comparison builtins used to report `but got 0` however
;; many arguments arrived, so `(< 1)` and `(<)` produced the identical
;; message. They count for real now. Their minimum is 2, so 0 and 1 are
;; the only under-calls there are, and both are pinned.
(test amt-variadic-comparisons-report-the-count-they-received
      (amt/msg? 'arg-error "Argument Error: < expected at least 2 arguments, but got 1"
                '(if (< 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: > expected at least 2 arguments, but got 1"
                '(if (> 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: <= expected at least 2 arguments, but got 1"
                '(if (<= 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: >= expected at least 2 arguments, but got 1"
                '(if (>= 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: = expected at least 2 arguments, but got 1"
                '(if (= 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: < expected at least 2 arguments, but got 0"
                '(if (<) 1 2))
      (amt/msg? 'arg-error "Argument Error: = expected at least 2 arguments, but got 0"
                '(if (=) 1 2)))

;; `-` and `/` belong to the same family at a minimum of 1, where 0 is
;; the only way to under-call them - which is why their count read
;; correctly all along and they never showed the defect above.
(test amt-minus-and-divide-need-one-argument
      (amt/msg? 'arg-error "Argument Error: - expected at least 1 argument, but got 0"
                '(if (-) 1 2))
      (amt/msg? 'arg-error "Argument Error: / expected at least 1 argument, but got 0"
                '(if (/) 1 2)))

;; `%` answers to `modulo` when the arity is wrong and to `%` when the
;; types are. The type message asks for `(integer integer)`, which is
;; what it actually accepts: a float in either position is refused, and
;; the message no longer contradicts itself by naming the wider
;; `(number number)` that `number?` admits a float to.
;;
;; Its two failures also arrive under different TAGS while both messages
;; begin "Argument Error": the arity one is `arg-error`, the type one is
;; `type-error`. The message prefix is not a guide to the tag.
(test amt-percent-has-two-names-and-refuses-floats
      (amt/msg? 'arg-error "Argument Error: modulo expected 2 arguments, but got 1"
                '(if (% 1) 1 2))
      (amt/msg? 'type-error "Argument Error: % expected (integer integer) but got (float integer)"
                '(if (% 7.5 2) 1 2))
      (amt/msg? 'type-error "Argument Error: % expected (integer integer) but got (integer float)"
                '(if (% 7 2.5) 1 2))
      (amt/msg? 'type-error "Argument Error: % expected (integer integer) but got (float float)"
                '(if (% 7.5 2.5) 1 2))
      (number? 7.5)
      (= 1 (% 7 3))
      (= -1 (% -7 3)))
