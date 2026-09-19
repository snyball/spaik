;;; Errors raised inside `eval` are catchable throws: per-tag payload
;;; shapes, tag matching, nested frames, and the statement-position trap.
;;; Catch outside, eval inside, eval in tail position.

;;; ---[ helpers ]-----------------------------------------------------

;; Evaluate `form` under `tag`. Returns the form's value if it does not
;; error, or the throw payload if it raises an error tagged `tag`.
(defun errc/catch (tag form)
  (catch tag (eval form)))

;; Prefix test on strings, built from `iter`/`next` - this dialect has
;; no substring or search builtin.
(defun errc/starts-with? (prefix s)
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

;; True when `form` raises an error tagged `tag` whose payload is a
;; message string starting with `prefix`.
(defun errc/msg? (tag prefix form)
  (let ((v (errc/catch tag form)))
    (and (string? v) (errc/starts-with? prefix v))))

;;; ---[ the helpers themselves ]---------------------------------------

(test errc-helper-starts-with
      ;; `errc/msg?` is load-bearing for most of this file, so pin the
      ;; string primitive it is built out of first.
      (errc/starts-with? "abc" "abcdef")
      (errc/starts-with? "abcdef" "abcdef")
      (errc/starts-with? "" "abcdef")
      (errc/starts-with? "" "")
      (not (errc/starts-with? "abd" "abcdef"))
      (not (errc/starts-with? "abcdefg" "abcdef"))
      (not (errc/starts-with? "x" "")))

;;; ---[ nothing is converted when nothing goes wrong ]------------------

(defun errc/plain-value () (errc/catch 'type-error '(+ 1 2)))
(defun errc/plain-list () (errc/catch 'type-error '(list 1 2)))
(defun errc/plain-nil () (errc/catch 'type-error 'nil))

(test errc-no-error-passes-the-value-through
      ;; A `catch` whose body does not error returns the body's value,
      ;; exactly as it did before errors became throwable. Every tag
      ;; below is one that a failing form WOULD have used, so this also
      ;; rules out the conversion firing spuriously.
      (= 3 (errc/plain-value))
      (eq? '(1 2) (errc/plain-list))
      (nil? (errc/plain-nil))
      (= 3 (errc/catch 'undefined-variable '(+ 1 2)))
      (= 3 (errc/catch 'arg-error '(+ 1 2)))
      (= 3 (errc/catch 'index-error '(+ 1 2)))
      (= 3 (errc/catch 'divide-by-zero '(+ 1 2))))

;;; ---[ undefined-variable: payload is the SYMBOL ]---------------------

(defun errc/uv-bare ()   (errc/catch 'undefined-variable 'errc-no-such-global))
(defun errc/uv-nested () (errc/catch 'undefined-variable '(+ errc-no-such-global 1)))
(defun errc/uv-deep ()   (errc/catch 'undefined-variable '(list 1 (list 2 errc-no-such-global))))
(defun errc/uv-lambda () (errc/catch 'undefined-variable '((lambda () errc-no-such-global))))

(test errc-undefined-variable
      ;; The payload is the offending symbol itself, not a message -
      ;; this is the example from the feature's own description.
      (eq? 'errc-no-such-global (errc/uv-bare))
      (eq? 'errc-no-such-global (errc/uv-nested))
      (eq? 'errc-no-such-global (errc/uv-deep))
      (eq? 'errc-no-such-global (errc/uv-lambda))
      (symbol? (errc/uv-bare))
      ;; a DIFFERENT undefined name comes back as that name
      (eq? 'errc-other-missing
           (errc/catch 'undefined-variable 'errc-other-missing))
      (not (eq? 'errc-no-such-global
                (errc/catch 'undefined-variable 'errc-other-missing))))

;;; ---[ undefined-function: payload is the SYMBOL ]---------------------

(defun errc/uf-direct () (errc/catch 'undefined-function '(errc-no-such-fn 1)))
(defun errc/uf-nested () (errc/catch 'undefined-function '(+ 1 (errc-no-such-fn))))
(defun errc/uf-zero-args () (errc/catch 'undefined-function '(errc-no-such-fn)))

(test errc-undefined-function
      (eq? 'errc-no-such-fn (errc/uf-direct))
      (eq? 'errc-no-such-fn (errc/uf-nested))
      (eq? 'errc-no-such-fn (errc/uf-zero-args))
      (symbol? (errc/uf-direct))
      ;; an undefined NAME in call position is an undefined FUNCTION,
      ;; not an undefined variable - the two tags do not overlap
      (eq? 'errc-no-such-fn
           (errc/catch 'undefined-function '(errc-no-such-fn 1 2 3))))

;;; ---[ type-error: payload is the message string ]---------------------

(defun errc/te-car ()   (errc/msg? 'type-error "Type Error: " '(car 5)))
(defun errc/te-cdr ()   (errc/msg? 'type-error "Type Error: " '(cdr 5)))
(defun errc/te-len ()   (errc/msg? 'type-error "Type Error: " '(len 5)))
(defun errc/te-apply () (errc/msg? 'type-error "Type Error: " '(apply car 5)))
(defun errc/te-next ()  (errc/msg? 'type-error "Type Error: " '(next 5)))
(defun errc/te-iter ()  (errc/msg? 'type-error "Type Error: " '(iter 5)))
(defun errc/te-get ()   (errc/msg? 'type-error "Type Error: " '(get "abc" 0)))
(defun errc/te-set ()   (errc/msg? 'type-error "Type Error: " '(set 5 6)))
(defun errc/te-symid () (errc/msg? 'type-error "Type Error: " '(sym-id 5)))

(test errc-type-error
      (errc/te-car)
      (errc/te-cdr)
      (errc/te-len)
      (errc/te-apply)
      (errc/te-next)
      (errc/te-iter)
      (errc/te-get)
      (errc/te-set)
      (errc/te-symid)
      (string? (errc/catch 'type-error '(car 5))))

;;; ---[ arg-error: payload is the message string ]-----------------------

(defun errc/ae-too-few ()   (errc/msg? 'arg-error "Argument Error: " '(car)))
(defun errc/ae-too-many ()  (errc/msg? 'arg-error "Argument Error: " '(vec2 1 2 3)))
(defun errc/ae-special ()   (errc/msg? 'arg-error "Argument Error: " '(if)))
(defun errc/ae-catch ()     (errc/msg? 'arg-error "Argument Error: " '(catch)))
(defun errc/ae-throw ()     (errc/msg? 'arg-error "Argument Error: " '(throw 'k)))
(defun errc/ae-eval ()      (errc/msg? 'arg-error "Argument Error: " '(eval)))
(defun errc/ae-lambda ()    (errc/msg? 'arg-error "Argument Error: " '(lambda)))
(defun errc/ae-get ()       (errc/msg? 'arg-error "Argument Error: " '(get (make-table) :k :extra)))

(test errc-arg-error
      ;; Arity checking now has a tag of its own - `arg-error`, not
      ;; `argument-error`, despite the message text saying "Argument
      ;; Error".
      (errc/ae-too-few)
      (errc/ae-too-many)
      (errc/ae-get)
      ;; ... and it covers the special forms too, not just subrs
      (errc/ae-special)
      (errc/ae-catch)
      (errc/ae-throw)
      (errc/ae-eval)
      (errc/ae-lambda))

;;; ---[ index-error ]----------------------------------------------------

(defun errc/ie-vec-get ()  (errc/msg? 'index-error "Index Error: " '(get (vec 1 2) 9)))
(defun errc/ie-vec-set ()  (errc/msg? 'index-error "Index Error: " '(set (get (vec 1) 5) 2)))
(defun errc/ie-empty ()    (errc/msg? 'index-error "Index Error: " '(get (vec) 0)))

;; `nth` is NOT one of these: it answers its `alt` argument - nil by
;; default - for an index past the end, so nothing is raised and nothing
;; is converted. `get` on the same vec still raises, which is the whole
;; difference between the two. Note the arguments are in opposite
;; orders: `get` is (get xs idx), `nth` is (nth idx xs).
(defun errc/ie-nth-vec-misses ()
  (eq? :errc-else (errc/catch 'index-error '(if (nth 9 (vec 1 2)) :errc-then :errc-else))))
(defun errc/ie-get-still-raises ()
  (errc/msg? 'index-error "Index Error: " '(if (get (vec 1 2) 9) :errc-then :errc-else)))

(test errc-index-error
      (errc/ie-vec-get)
      (errc/ie-vec-set)
      (errc/ie-empty)
      (errc/ie-nth-vec-misses)
      (errc/ie-get-still-raises))

;;; ---[ divide-by-zero: payload is nil ]---------------------------------

(defun errc/dbz-div () (errc/catch 'divide-by-zero '(/ 1 0)))
(defun errc/dbz-mod () (errc/catch 'divide-by-zero '(% 1 0)))
(defun errc/dbz-chain () (errc/catch 'divide-by-zero '(+ 1 (/ 7 0))))

(test errc-divide-by-zero
      ;; Integer division and modulo by zero both raise; the payload is
      ;; `nil` (there is no message object), so the tag is all you get.
      (nil? (errc/dbz-div))
      (nil? (errc/dbz-mod))
      (nil? (errc/dbz-chain))
      ;; float division by zero is NOT an error - it is an infinity
      (= 3 (errc/catch 'divide-by-zero '(if (= (/ 1.0 0) (/ 2.0 0)) 3 4))))

;;; ---[ unimplemented ]---------------------------------------------------

(defun errc/ui-read ()      (errc/msg? 'unimplemented "Unimplemented: " '(read "1")))
(defun errc/ui-read-from () (errc/msg? 'unimplemented "Unimplemented: " '(read-from "f")))

(test errc-unimplemented
      ;; `read` and `read-from` are declared but not implemented. Both
      ;; used to be Rust `unimplemented!()` panics that took the process
      ;; down; they are ordinary in-language errors now, which is what
      ;; this pins. Replace with real behaviour tests once the builtins
      ;; exist.
      (errc/ui-read)
      (errc/ui-read-from))

;;; ---[ iter-stop: the tag nothing raises ]----------------------------------

;; The iterator has to be a GLOBAL: `eval` compiles its form in the
;; global environment and cannot see a `let` local of the caller.
(define errc/it nil)

(defun errc/iter-exhausted ()
  (set errc/it (iter (list 1)))
  (next errc/it)
  (catch 'iter-stop (eval '(next errc/it))))

(defun errc/iter-not-yet-exhausted ()
  (set errc/it (iter (list 7)))
  (catch 'iter-stop (eval '(next errc/it))))

(test errc-iter-stop
      ;; Running an iterator off its end answers the `<ζ>-iter-stop`
      ;; sentinel - as an ordinary RETURN VALUE, not as a raise. The two
      ;; are indistinguishable here because the `eval` is in tail
      ;; position of the `catch`; `rvr-next-past-the-end-does-not-raise`
      ;; in `tests/error-raise-vs-return.lisp` tells them apart and shows
      ;; nothing is tagged `iter-stop`. What this pins is the value.
      (iter-end? (errc/iter-exhausted))
      ;; an iterator with an element left just yields it
      (= 7 (errc/iter-not-yet-exhausted))
      (not (iter-end? (errc/iter-not-yet-exhausted))))

;;; ---[ the tag has to match ]---------------------------------------------

(defun errc/wrong-tag-falls-through ()
  ;; `errc/catch` under a non-matching tag would be fatal on its own; an
  ;; enclosing `catch` with the right tag picks it up instead, proving the
  ;; inner one did not match and did not swallow it.
  (catch 'type-error (errc/catch 'index-error '(car 5))))

(defun errc/three-deep-outermost-matches ()
  (catch 'undefined-variable
    (catch 'index-error
      (catch 'arg-error
        (eval 'errc-no-such-global)))))

(defun errc/innermost-matching-catch-wins ()
  (catch 'type-error
    (list :outer (catch 'type-error (eval '(car 5))))))

(test errc-tag-matching
      ;; a tag that does not name this error does not catch it
      (string? (errc/wrong-tag-falls-through))
      (eq? 'errc-no-such-global (errc/three-deep-outermost-matches))
      ;; the innermost matching `catch` is the one that handles it, and
      ;; control really does resume there - the enclosing `list` runs
      (eq? :outer (car (errc/innermost-matching-catch-wins)))
      (string? (cadr (errc/innermost-matching-catch-wins))))

;;; ---[ the error can come from arbitrarily deep inside ]-------------------

(defun errc/deep-3 (x) (car x))
(defun errc/deep-2 (x) (errc/deep-3 x))
(defun errc/deep-1 (x) (errc/deep-2 x))
(defun errc/through-calls () (errc/catch 'type-error '(errc/deep-1 5)))

(defun errc/through-map ()    (errc/catch 'type-error '(map car (list 5))))
(defun errc/through-lambda () (errc/catch 'type-error '((lambda (x) (car x)) 5)))
(defun errc/through-apply ()  (errc/catch 'type-error '(apply car (list 5))))

(test errc-error-from-nested-frames
      ;; The conversion is not limited to the top form of the `eval`;
      ;; it covers the whole dynamic extent, across user functions,
      ;; stdlib functions, lambdas and `apply`.
      (string? (errc/through-calls))
      (string? (errc/through-map))
      (string? (errc/through-lambda))
      (string? (errc/through-apply)))

;;; ---[ work done before the error still happened ]--------------------------

(define errc/n 0)
(defun errc/bump () (set errc/n (+ errc/n 1)) errc/n)
(defun errc/side-effects-before-the-error ()
  (set errc/n 0)
  (errc/catch 'type-error '(progn (errc/bump) (errc/bump) (errc/bump) (car 5)))
  errc/n)
(defun errc/no-side-effects-after-the-error ()
  (set errc/n 0)
  ;; the raise is written in VALUE position (an `if` condition) on
  ;; purpose - see `errc-statement-position-eliminates-the-raise` below
  (errc/catch 'type-error '(if (car 5) (errc/bump) (errc/bump)))
  errc/n)

(test errc-unwinding-stops-at-the-error
      ;; Everything before the raise runs; nothing after it does.
      (= 3 (errc/side-effects-before-the-error))
      (= 0 (errc/no-side-effects-after-the-error)))

;;; ---[ the statement-position trap ]----------------------------------------

;; An erroring form whose value is DISCARDED can be eliminated outright,
;; so the error never happens and the `catch` looks like it succeeded.
;; It is the single easiest way to write an error test that silently
;; proves nothing, so it is pinned here: the same `(car 5)` raises in
;; value position and does not raise in statement position.

(defun errc/raise-in-statement-position ()
  (set errc/n 0)
  (errc/catch 'type-error '(progn (car 5) (errc/bump)))
  errc/n)

(defun errc/raise-in-argument-of-discarded-call ()
  (set errc/n 0)
  (errc/catch 'type-error '(progn (list (car 5)) (errc/bump)))
  errc/n)

(defun errc/raise-in-value-position ()
  (set errc/n 0)
  (errc/catch 'type-error '(if (car 5) (errc/bump) (errc/bump)))
  errc/n)

(test errc-statement-position-eliminates-the-raise
      ;; discarded: `(car 5)` is compiled away, `errc/bump` still runs
      (= 1 (errc/raise-in-statement-position))
      ;; discarding the CALL discards its arguments too
      (= 1 (errc/raise-in-argument-of-discarded-call))
      ;; used: the error actually fires and `errc/bump` never runs
      (= 0 (errc/raise-in-value-position))
      ;; ... and in value position it really is the type error that is
      ;; caught, not some other outcome
      (errc/msg? 'type-error "Type Error: " '(if (car 5) 1 2)))

;;; ---[ ordinary throw/catch is unchanged ]----------------------------------

(defun errc/throw-caught ()      (catch 'errc-k (throw 'errc-k 42)))
(defun errc/catch-no-throw ()    (catch 'errc-k 'normal))
(defun errc/thrower ()           (throw 'errc-k 7))
(defun errc/throw-across-call () (catch 'errc-k (errc/thrower)))
(defun errc/throw-past-inner ()
  (catch 'errc-outer (catch 'errc-inner (throw 'errc-outer 9) 'x) 'y))
(defun errc/throw-a-reference ()  (catch 'errc-k (throw 'errc-k (list 1 2))))
(defun errc/throw-a-string ()     (catch 'errc-k (throw 'errc-k "s")))

(test errc-throw-still-works
      ;; The feature adds to `catch`/`throw`, it does not change it.
      ;; (Every form here stays clear of `eval`, so it is unaffected by
      ;; the throw-across-eval stack leak noted at the top of the file.)
      (= 42 (errc/throw-caught))
      (eq? 'normal (errc/catch-no-throw))
      (= 7 (errc/throw-across-call))
      (= 9 (errc/throw-past-inner))
      ;; `throw` takes any value, reference types included
      (eq? '(1 2) (errc/throw-a-reference))
      (eq? "s" (errc/throw-a-string)))
