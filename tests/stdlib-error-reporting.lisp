;;; What the lisp-level stdlib (lisp/core.lisp) raises for bad input.
;;; Catch outside, eval inside, eval in tail position.
;;; Builtins are in tests/builtin-error-reporting.lisp.

(defun stdx/catch (tag form) (catch tag (eval form)))

(defun stdx/starts-with? (prefix s)
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

(defun stdx/msg? (tag prefix form)
  (let ((v (stdx/catch tag form)))
    (and (string? v) (stdx/starts-with? prefix v))))

(defun stdx/raises? (tag form) (string? (stdx/catch tag form)))

;;; ---[ a non-callable where a function was expected ]------------------

;; Every higher-order stdlib function reaches the same VM check, so they
;; all report the same way. Pinned together because the shared message is
;; what tells a caller "you passed a non-function", regardless of which
;; one they called.

(test stdx-higher-order-rejects-a-non-function
      (stdx/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                 '(map 5 (list 1)))
      (stdx/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                 '(for-each 5 (list 1)))
      (stdx/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                 '(filter 5 (list 1)))
      (stdx/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                 '(all? 5 (list 1)))
      (stdx/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                 '(any? 5 (list 1)))
      ;; a callable one of each shape is accepted: subr, lambda, closure
      (eq? '(1) (stdx/catch 'type-error '(map car (list (list 1)))))
      (eq? '(2) (stdx/catch 'type-error '(map (lambda (x) (+ x 1)) (list 1))))
      (= true (stdx/catch 'type-error '(all? string? (list "a")))))

;;; ---[ the error inside the applied function propagates out ]-----------

(test stdx-higher-order-propagates-the-callee-error
      ;; the tag is the callee's, not a wrapper's, and it survives the
      ;; trip out through map/filter/for-each
      (stdx/msg? 'type-error "Type Error: Expected cons in car" '(map car (list 5)))
      (stdx/msg? 'type-error "Type Error: Expected cons in car" '(for-each car (list 5)))
      (stdx/msg? 'type-error "Type Error: Expected cons in car" '(filter car (list 5)))
      ;; a user error raised inside the callee keeps its own tag too
      (eq? :from-callee
           (stdx/catch 'stdx-callee-tag
                       '(map (lambda (x) (error 'stdx-callee-tag :from-callee))
                             (list 1)))))

;;; ---[ iter-based functions reject a non-iterable ]---------------------

(test stdx-iter-based-reject-a-non-iterable
      ;; sum/mean/elem?/member? funnel through `iter`, whose message
      ;; names the argument position as well as the type
      (stdx/msg? 'type-error
                 "Type Error: Expected one of cons, string, vec, table for argument 1 of (iter ...), but got integer"
                 '(sum 5))
      (stdx/msg? 'type-error "Type Error: Expected one of cons, string, vec"
                 '(mean 5))
      (stdx/msg? 'type-error "Type Error: Expected one of cons, string, vec"
                 '(elem? 1 5))
      (stdx/msg? 'type-error "Type Error: Expected one of cons, string, vec"
                 '(member? 1 5))
      ;; `collect` wants a live iterator, not the sequence itself
      (stdx/msg? 'type-error "Type Error: Expected iter in next" '(collect 5))
      (stdx/msg? 'type-error "Type Error: Expected iter in next" '(collect (list 1))))

;;; ---[ car/cdr-based functions reject anything that is not a cons ]------

(test stdx-cons-walkers-reject-a-non-cons
      ;; min/max/zip/find-first-duplicate are raw car/cdr loops, so the
      ;; error they surface is `car`'s, naming the type actually passed
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got integer" '(min 5))
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got integer" '(max 5))
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got integer" '(zip 5 (list 1)))
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got integer"
                 '(find-first-duplicate 5))
      ;; an EMPTY list is not a cons either, so min/max have no identity
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got nil" '(min (list)))
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got nil" '(max (list)))
      ;; ... while the iter-based sum does have one
      (= 0 (stdx/catch 'type-error '(sum (list))))
      ;; a `vec` reaches the same car check: these walkers are
      ;; cons-only, while the iter-based ones accept both
      (stdx/msg? 'type-error "Type Error: Expected cons in car, but got vec" '(min (vec 1 2))))

;;; ---[ division by zero reached through the stdlib ]---------------------

(test stdx-mean-of-empty-is-divide-by-zero
      ;; `(mean xs)` is `(/ (sum xs) (len xs))`, so an empty sequence
      ;; divides by zero rather than raising something of its own. The
      ;; payload is nil, as for every divide-by-zero.
      (nil? (stdx/catch 'divide-by-zero '(mean (list))))
      (nil? (stdx/catch 'divide-by-zero '(mean (vec))))
      (nil? (stdx/catch 'divide-by-zero '(mean "")))
      ;; non-empty is unaffected, and integer division truncates
      (= 2 (stdx/catch 'divide-by-zero '(mean (list 1 2 3))))
      (= 1 (stdx/catch 'divide-by-zero '(mean (list 1 2)))))

;;; ---[ arity of the stdlib's own functions ]-----------------------------

(test stdx-stdlib-arity
      ;; defined with `defun`, so they are arity-checked like any user
      ;; function
      (stdx/msg? 'arg-error "Argument Error: sqrt expected 1 arguments, but got 0" '(sqrt))
      (stdx/msg? 'arg-error "Argument Error: gensym expected 0 argument, but got 1" '(gensym 1))
      (stdx/raises? 'arg-error '(map car))
      (stdx/raises? 'arg-error '(filter car))
      (stdx/raises? 'arg-error '(zip (list 1)))
      ;; `nth`'s third argument is optional, so two AND three are legal
      (= 2 (stdx/catch 'arg-error '(nth (list 1 2) 1)))
      (= 7 (stdx/catch 'arg-error '(nth (list 1 2) 9 7))))

;;; ---[ empty input that is legal, not an error ]--------------------------

(test stdx-empty-input-is-not-an-error
      ;; a nil sequence is the identity case for the walkers, and must
      ;; not be confused with the bad-type cases above
      (nil? (stdx/catch 'type-error '(map car nil)))
      (nil? (stdx/catch 'type-error '(filter car nil)))
      (nil? (stdx/catch 'type-error '(zip nil nil)))
      (nil? (stdx/catch 'type-error '(find-first-duplicate nil)))
      (= 0 (stdx/catch 'type-error '(len (collect (iter (list))))))
      ;; an inverted range is empty, not an error
      (nil? (stdx/catch 'type-error '(range-list 2 1))))
