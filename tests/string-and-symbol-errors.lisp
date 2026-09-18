;;; What the string/symbol builtins raise, and - just as load-bearing -
;;; which of them accept anything at all.
;;; Catch outside, eval inside, eval in tail position.

(defun strx/catch (tag form) (catch tag (eval form)))

(defun strx/starts-with? (prefix s)
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

(defun strx/msg? (tag prefix form)
  (let ((v (strx/catch tag form)))
    (and (string? v) (strx/starts-with? prefix v))))

;;; ---[ concat and string take ANY type ]-------------------------------

(test strx-concat-and-string-never-type-error
      ;; both stringify whatever they are given, containers included, so
      ;; there is no wrong type to raise on - only the wrong COUNT for
      ;; `string`, which takes exactly one
      (eq? "12" (strx/catch 'type-error '(concat 1 2)))
      (eq? "" (strx/catch 'arg-error '(concat)))
      (eq? "(1)2" (strx/catch 'type-error '(concat (list 1) 2)))
      (eq? "(vec 1)" (strx/catch 'type-error '(string (vec 1))))
      (eq? "(table)" (strx/catch 'type-error '(string (make-table))))
      (strx/msg? 'arg-error "Argument Error: string expected 1 arguments, but got 0" '(string))
      (strx/msg? 'arg-error "Argument Error: string expected 1 arguments, but got 2" '(string 1 2)))

;;; ---[ join checks both arguments, and names the position ]--------------

(test strx-join-argument-checks
      ;; the message identifies WHICH argument was wrong, which `concat`
      ;; never has to do
      (strx/msg? 'type-error
                 "Type Error: Expected one of cons, string, vec for argument 1 of (join ...), but got integer"
                 '(join 5 ","))
      (strx/msg? 'type-error
                 "Type Error: Expected string for argument 2 of (join ...), but got integer"
                 '(join (list 1) 5))
      ;; the working shapes, for both sequence types
      (eq? "1,2" (strx/catch 'type-error '(join (list 1 2) ",")))
      (eq? "1,2" (strx/catch 'type-error '(join (vec 1 2) ",")))
      (eq? "" (strx/catch 'type-error '(join (list) ","))))

;;; ---[ intern and sym-id are strict ]-------------------------------------

(test strx-symbol-builtins-are-strict
      ;; `intern` wants a string and `sym-id` a symbol; neither coerces
      (strx/msg? 'type-error "Type Error: Expected string but got integer" '(intern 5))
      (strx/msg? 'type-error "Type Error: Expected string but got integer" '(intern 5))
      (strx/msg? 'type-error "Type Error: Expected symbol for argument 1 of (sym-id ...), but got string"
                 '(sym-id "x"))
      ;; the round trip works, and interning twice gives the same symbol
      (symbol? (strx/catch 'type-error '(intern "strx-a")))
      (eq? 'strx-a (strx/catch 'type-error '(intern "strx-a")))
      (= true (strx/catch 'type-error '(= (sym-id (intern "strx-a")) (sym-id 'strx-a)))))

;;; ---[ chr is an iterator in disguise ]------------------------------------

(test strx-chr-goes-through-iter
      ;; `(chr s)` is `(next (iter s))`, so a non-iterable argument
      ;; reports as `iter`'s type error rather than as a `chr` one, and
      ;; the message says `(iter ...)` - worth pinning, since the name in
      ;; the message is not the name the caller wrote
      (strx/msg? 'type-error
                 "Type Error: Expected one of cons, string, vec for argument 1 of (iter ...), but got integer"
                 '(chr 5))
      ;; the first character of a non-empty string ...
      (= true (strx/catch 'type-error '(= (chr "abc") (chr "a"))))
      ;; ... and the iterator sentinel for an empty one, NOT an error
      (iter-end? (strx/catch 'iter-stop '(chr ""))))

;;; ---[ keyword-name mangles instead of raising ]-----------------------------

(test strx-keyword-name-does-not-type-check
      ;; It drops the first character of whatever it is handed, so a
      ;; non-keyword argument silently produces a wrong string rather
      ;; than an error.
      ;; Pinned as-is so the day it starts raising is a deliberate change.
      (eq? "bc" (strx/catch 'type-error '(keyword-name 'abc)))
      (eq? "2345" (strx/catch 'type-error '(keyword-name 12345)))
      (string? (strx/catch 'type-error '(keyword-name 5)))
      ;; the intended use is unaffected
      (eq? "kw" (strx/catch 'type-error '(keyword-name :kw)))
      ;; and the predicate it pairs with does answer rather than raise
      (nil? (strx/catch 'type-error '(keyword? 5)))
      (= true (strx/catch 'type-error '(keyword? :kw))))
