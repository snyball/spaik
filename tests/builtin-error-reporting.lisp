;;; For each builtin: what a wrong type or wrong arity raises.
;;; Invariant: wrong type is `type-error`, wrong count is `arg-error`,
;;; and the two never swap. Good arguments are in tests/test-builtins.lisp.

;;; ---[ helpers ]-----------------------------------------------------

(defun errx/catch (tag form)
  (catch tag (eval form)))

(defun errx/starts-with? (prefix s)
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

;; True when `form` raises under `tag` with a string payload.
(defun errx/raises? (tag form)
  (string? (errx/catch tag form)))

;; True when `form` raises under `tag` with a message starting `prefix`.
(defun errx/msg? (tag prefix form)
  (let ((v (errx/catch tag form)))
    (and (string? v) (errx/starts-with? prefix v))))

;;; ---[ cons/list builtins ]--------------------------------------------

(test errx-cons-builtins-type-errors
      ;; the cons accessors are cons-only and say so
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(car 5))
      (errx/msg? 'type-error "Type Error: Expected cons in cdr" '(cdr "x"))
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(car "x"))
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(car (vec 1)))
      (errx/msg? 'type-error "Type Error: Expected cons" '(append 1 2))
      ;; nil is not a cons for car/cdr either
      (errx/raises? 'type-error '(car nil)))

(test errx-cons-builtins-arity-errors
      (errx/msg? 'arg-error "Argument Error: cons expected 2" '(cons 1))
      (errx/msg? 'arg-error "Argument Error: car expected 1" '(car))
      (errx/msg? 'arg-error "Argument Error: cdr expected 1" '(cdr)))

;;; ---[ vec builtins ]---------------------------------------------------

(test errx-vec-builtins
      (errx/msg? 'type-error "Type Error: Expected vec in push" '(push 5 1))
      (errx/msg? 'type-error "Type Error: Expected vec in pop" '(pop 5))
      (errx/msg? 'type-error "Type Error: Expected one of vec" '(get 5 0))
      (errx/msg? 'arg-error "Argument Error: get expected 2" '(get (vec 1)))
      ;; reading past the end is an index error, not a type error
      (errx/msg? 'index-error "Index Error: " '(get (vec 1 2) 2))
      (errx/msg? 'index-error "Index Error: " '(get (vec) 0))
      ;; and so is writing past the end
      (errx/msg? 'index-error "Index Error: " '(set (get (vec 1) 5) 2)))

(test errx-fixed-width-vector-arity
      ;; vec2/vec3/vec4 take exactly their width
      (errx/msg? 'arg-error "Argument Error: vec2 expected 2" '(vec2 1))
      (errx/msg? 'arg-error "Argument Error: vec2 expected 2" '(vec2 1 2 3))
      (errx/msg? 'arg-error "Argument Error: vec3 expected 3" '(vec3 1 2))
      (errx/msg? 'arg-error "Argument Error: vec4 expected 4" '(vec4 1 2 3)))

;;; ---[ len / type-of / string / symbol ]---------------------------------

(test errx-len-and-type-of
      ;; `len`'s type error enumerates every type it does accept, so this
      ;; doubles as a check that the accepted set has not silently shrunk
      (errx/msg? 'type-error
                 "Type Error: Expected one of nil, cons, string, vec, table, vec2, vec3, vec4 in len"
                 '(len 5))
      (errx/msg? 'arg-error "Argument Error: len expected 1" '(len))
      (errx/msg? 'arg-error "Argument Error: type-of expected 1" '(type-of))
      (errx/msg? 'arg-error "Argument Error: type-of expected 1" '(type-of 1 2)))

(test errx-symbol-builtins
      (errx/msg? 'type-error "Type Error: Expected string" '(intern 5))
      (errx/msg? 'type-error "Type Error: Expected symbol" '(sym-id 5))
      (errx/msg? 'arg-error "Argument Error: string expected 1" '(string))
      ;; `set`'s first argument must be a place, not a value
      (errx/msg? 'type-error "Type Error: Expected symbol" '(set 5 6)))

;;; ---[ iteration ]--------------------------------------------------------

(test errx-iteration-builtins
      (errx/msg? 'type-error "Type Error: Expected one of cons, string, vec" '(iter 5))
      (errx/msg? 'type-error "Type Error: Expected iter in next" '(next 5))
      (errx/msg? 'type-error "Type Error: Expected iter in next" '(next (list 1)))
      (errx/msg? 'type-error "Type Error: Expected iter in next" '(next "abc")))

;;; ---[ apply / eval ]-----------------------------------------------------

(test errx-apply-and-eval
      ;; apply checks the callee ...
      (errx/msg? 'type-error "Type Error: Expected one of lambda, subr" '(apply 5 (list)))
      ;; ... and the argument sequence
      (errx/msg? 'type-error "Type Error: Expected one of list, vec in apply" '(apply car 5))
      ;; an error raised INSIDE an applied function converts like any other
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(apply car (list 5)))
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(apply car (vec 5)))
      (errx/msg? 'arg-error "Argument Error: eval expected 1" '(eval))
      (errx/msg? 'arg-error "Argument Error: eval expected 1" '(eval 5 6)))

;;; ---[ sequence builtins that take several types ]-------------------------

(test errx-sequence-builtins
      (errx/msg? 'type-error "Type Error: Expected one of vec, cons" '(sort! 5))
      (errx/msg? 'type-error "Type Error: Expected one of vec, cons, string" '(reverse 5))
      (errx/msg? 'type-error "Type Error: Expected one of vec, cons, string" '(reverse (make-table))))

;;; ---[ special forms are arity-checked too ]--------------------------------

(test errx-special-form-arity
      ;; `if`, `catch`, `throw`, `lambda` and friends report through the
      ;; same `arg-error` tag as ordinary subrs
      (errx/msg? 'arg-error "Argument Error: if expected" '(if))
      (errx/msg? 'arg-error "Argument Error: if expected" '(if 1))
      (errx/msg? 'arg-error "Argument Error: catch expected 2" '(catch))
      ;; `throw` takes 2 OR 3 arguments - the 3-argument form throws into
      ;; a saved continuation's extent - so its arity reads as a range
      (errx/msg? 'arg-error "Argument Error: throw expected from 2 to 3" '(throw 'k))
      (errx/msg? 'arg-error "Argument Error: throw expected from 2 to 3" '(throw))
      (errx/msg? 'arg-error "Argument Error: throw expected from 2 to 3" '(throw 'k 1 2 3))
      (errx/msg? 'arg-error "Argument Error: lambda expected at least 1" '(lambda))
      (errx/msg? 'arg-error "Argument Error: set expected 2" '(set))
      (errx/msg? 'arg-error "Argument Error: define expected at least 1" '(define)))

;;; ---[ user functions are arity-checked the same way ]-----------------------

(defun errx/takes-one (x) x)
(defun errx/takes-two (x y) (list x y))
(defun errx/takes-opt (x &opt y) (list x y))
(defun errx/takes-rest (x &rest ys) (list x ys))

(test errx-user-function-arity
      ;; the tag does not depend on the callee being a builtin
      (errx/msg? 'arg-error "Argument Error: " '(errx/takes-one))
      (errx/msg? 'arg-error "Argument Error: " '(errx/takes-one 1 2))
      (errx/msg? 'arg-error "Argument Error: " '(errx/takes-two 1))
      (errx/msg? 'arg-error "Argument Error: " '(errx/takes-opt))
      (errx/msg? 'arg-error "Argument Error: " '(errx/takes-rest))
      ;; ... and the legal arities still work, so the check is not just
      ;; "anything raises"
      (= 1 (errx/catch 'arg-error '(errx/takes-one 1)))
      (eq? '(1 nil) (errx/catch 'arg-error '(errx/takes-opt 1)))
      (eq? '(1 (2 3)) (errx/catch 'arg-error '(errx/takes-rest 1 2 3))))

;;; ---[ stdlib functions written in lisp ]------------------------------------

;; `lisp/core.lisp` raises its own `(error 'index-error)` / `(error
;; 'type-error)` from `nth`, with no message - so the payload is `nil`
;; where a VM-raised error of the same tag carries a string. Both shapes
;; are pinned below; a caller that wants to tell them apart has only the
;; payload to go on.

(test errx-nth-error-paths
      ;; past the end of a list: index-error, raised by core.lisp
      (nil? (errx/catch 'index-error '(nth (list 1 2) 9)))
      ;; ... and of nil
      (nil? (errx/catch 'index-error '(nth nil 0)))
      ;; a non-sequence first argument: type-error, also from core.lisp
      (nil? (errx/catch 'type-error '(nth 5 0)))
      ;; past the end of a VEC the error comes from the VM instead, with
      ;; a message
      (errx/msg? 'index-error "Index Error: " '(nth (vec 1 2) 9))
      ;; an explicit default suppresses all of them
      (= 7 (errx/catch 'index-error '(nth (list 1 2) 9 7)))
      (= 7 (errx/catch 'index-error '(nth nil 0 7)))
      (= 7 (errx/catch 'index-error '(nth (vec 1 2) 9 7)))
      ;; in-range lookups are untouched
      (= 2 (errx/catch 'index-error '(nth (list 1 2) 1)))
      (= 2 (errx/catch 'index-error '(nth (vec 1 2) 1))))

(test errx-stdlib-propagates-the-underlying-error
      ;; `min`/`max`/`sum` are `car`/`iter` loops, so a bad argument
      ;; surfaces as the error of whatever primitive they reached - the
      ;; tag is still correct, which is what a caller needs
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(min 5))
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(max 5))
      (errx/msg? 'type-error "Type Error: Expected one of cons, string, vec" '(sum 5))
      ;; an error inside the function `map` applies propagates out of `map`
      (errx/msg? 'type-error "Type Error: Expected cons in car" '(map car (list 5))))

;;; ---[ tag and message text can disagree ]------------------------------------

(test errx-pow-raises-type-error-but-says-argument-error
      ;; `(pow "x" 2)` is tagged `type-error` while its message opens
      ;; "Argument Error: ". Pinned as-is: if the tag is ever corrected to
      ;; `arg-error` this test should be updated, not deleted, so the
      ;; change is a deliberate one rather than a silent drift.
      (errx/raises? 'type-error '(pow "x" 2))
      (errx/msg? 'type-error "Argument Error: pow expected (number number)" '(pow "x" 2))
      ;; `sqrt` is `(pow x 0.5)`, so it inherits both halves
      (errx/msg? 'type-error "Argument Error: pow expected (number number)" '(sqrt "x")))

;;; ---[ names that do not exist ]-----------------------------------------------

(test errx-missing-names
      ;; a name that is not defined anywhere, in call position
      (eq? 'make-symbol (errx/catch 'undefined-function '(make-symbol 5)))
      (eq? 'errx-not-a-real-builtin
           (errx/catch 'undefined-function '(errx-not-a-real-builtin)))
      ;; ... and in value position
      (eq? 'errx-not-a-real-global
           (errx/catch 'undefined-variable 'errx-not-a-real-global)))
