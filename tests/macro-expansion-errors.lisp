;;; What a malformed macro call raises, at macroexpansion time.
;;; Expansion of an eval'd form happens inside that eval's extent, so
;;; these are catchable: catch outside, eval inside, eval in tail position.

(defun macx/catch (tag form) (catch tag (eval form)))

(defun macx/starts-with? (prefix s)
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

(defun macx/msg? (tag prefix form)
  (let ((v (macx/catch tag form)))
    (and (string? v) (macx/starts-with? prefix v))))

;;; ---[ stdlib macros are arity-checked under their mangled name ]-------

;; A macro defined by `defmacro` is compiled to a function named
;; `<ξ>-NAME`, and that is the name its arity error carries - not the
;; name at the call site. Pinned because it is the only place the
;; mangling is visible to a program.

(test macx-macro-arity-reports-the-mangled-name
      (macx/msg? 'arg-error "Argument Error: <ξ>-while expected at least 1 arguments, but got 0"
                 '(while))
      (macx/msg? 'arg-error "Argument Error: <ξ>-until expected at least 1 arguments, but got 0"
                 '(until))
      (macx/msg? 'arg-error "Argument Error: <ξ>-when expected at least 1 arguments, but got 0"
                 '(when))
      (macx/msg? 'arg-error "Argument Error: <ξ>-case expected at least 1 arguments, but got 0"
                 '(case))
      (macx/msg? 'arg-error "Argument Error: <ξ>-range expected at least 1 arguments, but got 0"
                 '(range))
      (macx/msg? 'arg-error "Argument Error: <ξ>-let expected at least 1 arguments, but got 0"
                 '(let))
      (macx/msg? 'arg-error "Argument Error: <ξ>-defvar expected 2 argument, but got 1"
                 '(defvar macx-v))
      (macx/msg? 'arg-error "Argument Error: <ξ>-set* expected 2 argument, but got 1"
                 '(set* 1))
      (macx/msg? 'arg-error "Argument Error: <ξ>-inc! expected from 1 to 2 arguments, but got 0"
                 '(inc!))
      ;; `defun`/`defmacro` go through the same wrapper
      (macx/msg? 'arg-error "Argument Error: <ξ>-defun expected at least 2 arguments, but got 0"
                 '(defun)))

;;; ---[ malformed binding lists ]-----------------------------------------

(test macx-let-rejects-a-malformed-binding-list
      ;; `let`/`let*` destructure each binding with `car`, so a binding
      ;; that is not a (name init) pair raises `car`'s type error, and
      ;; the type in the message identifies what was written instead
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got symbol" '(let (x) x))
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got nil" '(let ((x)) x))
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got symbol" '(let* (x) 1))
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got nil" '(let* ((x)) 1))
      ;; a well-formed binding list is unaffected
      (= 1 (macx/catch 'type-error '(let ((x 1)) x)))
      (= 3 (macx/catch 'type-error '(let* ((x 1) (y (+ x 2))) y)))
      ;; an EMPTY binding list is legal for both
      (= 9 (macx/catch 'type-error '(let () 9)))
      (= 9 (macx/catch 'type-error '(let* () 9))))

(test macx-dolist-and-cond-reject-malformed-clauses
      ;; `dolist` wants a (var seq) pair ...
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got integer" '(dolist 5 1))
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got nil" '(dolist (x) 1))
      ;; ... and `cond` wants each clause to be a list
      (macx/msg? 'type-error "Type Error: Expected cons in car, but got integer" '(cond 5))
      ;; a one-element cond clause is accepted and answers nil when the
      ;; test is truthy but has no body
      (nil? (macx/catch 'type-error '(cond (5))))
      (= 2 (macx/catch 'type-error '(cond (false 1) (true 2)))))

;;; ---[ macros that accept a degenerate call ]-----------------------------

(test macx-degenerate-calls-that-are-legal
      ;; these look malformed but are not: they expand to nil rather than
      ;; raising, so a test for "raises" here would be wrong
      (nil? (macx/catch 'arg-error '(when 1)))
      (nil? (macx/catch 'arg-error '(unless 1)))
      (nil? (macx/catch 'arg-error '(case 1)))
      (nil? (macx/catch 'arg-error '(cond)))
      (nil? (macx/catch 'arg-error '(if-let (a 1))))
      (nil? (macx/catch 'arg-error '(progn)))
      ;; `and`/`or` with no arguments are their identity elements
      (= true (macx/catch 'arg-error '(and)))
      (= false (macx/catch 'arg-error '(or))))

;;; ---[ require / load ]----------------------------------------------------

(test macx-module-not-found
      ;; a module that is not on `sys/load-path` has a tag of its own,
      ;; `module-not-found`, and the message repeats the name asked for
      (macx/msg? 'module-not-found "Module Not Found: Could not find macx-no-such-module"
                 '(require macx-no-such-module))
      (macx/msg? 'module-not-found "Module Not Found: Could not find macx-other-module"
                 '(load macx-other-module))
      ;; ... and it is not a type-error or an undefined-variable, which
      ;; are the two tags an unknown bare name would otherwise suggest
      (string? (macx/catch 'module-not-found '(require macx-no-such-module))))

(test macx-require-wants-a-symbol
      ;; the module name is a SYMBOL, not a string or a path
      (macx/msg? 'type-error "Type Error: Expected symbol but got string" '(require "macx-x"))
      (macx/msg? 'type-error "Type Error: Expected symbol but got integer" '(require 5))
      (macx/msg? 'type-error "Type Error: Expected symbol but got string" '(load "macx-x"))
      (macx/msg? 'type-error "Type Error: Expected symbol but got integer" '(load 5)))
