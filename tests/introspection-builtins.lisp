;;; `intern`, `sym-id`, `type-of`, `keyword-name` and the three
;;; predicates that never answer true for any value a lisp program can
;;; construct: `unsigned-integer?`, `void?`, `mut-locked?`.

(defun ibx/catch (tag form) (catch tag (eval form)))
(defun ibx/starts-with? (prefix s)
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
(defun ibx/msg? (tag prefix form)
  (let ((v (ibx/catch tag form)))
    (and (string? v) (ibx/starts-with? prefix v))))

;; `intern` maps a string to the symbol of that name, and is idempotent
;; on a symbol. The symbol it answers is the same object the reader
;; would have produced, so `eq?` against a quoted symbol holds.
(test ibx-intern-round-trips
      (eq? 'hello (intern "hello"))
      (eq? 'hello (intern 'hello))
      (symbol? (intern "hello")))

(test ibx-intern-wants-a-string-or-symbol
      (ibx/msg? 'type-error "Type Error: Expected string but got integer"
                '(if (intern 5) 1 2)))

;; `sym-id` is a stable identity for a symbol within one process. Its
;; value is an implementation detail - only stability and the type check
;; are pinned.
(test ibx-sym-id-is-stable-and-symbol-only
      (= (sym-id 'foo) (sym-id 'foo))
      (= (sym-id 'foo) (sym-id (intern "foo")))
      (ibx/msg? 'type-error "Type Error: Expected symbol for argument 1 of (sym-id ...)"
                '(if (sym-id "foo") 1 2)))

;; `gensym` answers a fresh symbol every call.
(test ibx-gensym-is-fresh
      (symbol? (gensym))
      (not (eq? (gensym) (gensym))))

;; `type-of` names the runtime type. A keyword reports as `symbol` -
;; keywords are symbols that `keyword?` recognises by their spelling -
;; and both a builtin and a user lambda report as `lambda`.
(test ibx-type-of-names
      (eq? 'integer (type-of 1))
      (eq? 'float (type-of 1.5))
      (eq? 'string (type-of "s"))
      (eq? 'symbol (type-of 'a))
      (eq? 'cons (type-of (list 1)))
      (eq? 'vec (type-of (vec)))
      (eq? 'table (type-of (make-table)))
      ;; `(type-of nil)` is the SYMBOL `nil`, not the nil value: `'nil`
      ;; in source reads as the value, so the two are not `eq?`
      (symbol? (type-of nil))
      (= "nil" (string (type-of nil))))

(test ibx-type-of-keywords-and-callables
      (eq? 'symbol (type-of :k))
      (keyword? :k)
      (eq? 'lambda (type-of car))
      (eq? 'lambda (type-of (lambda (x) x))))

;; `keyword-name` drops the first character of whatever it is given, so
;; a non-keyword argument silently produces a wrong string rather than
;; an error. Pinned as-is: the day it starts raising should be a
;; deliberate change, not a silent one.
(test ibx-keyword-name-strips-one-character
      (= "abc" (keyword-name :abc))
      (= "ymbol" (keyword-name 'symbol)))

;; These three predicates are in `(functions)` and are callable, and
;; nothing a lisp program can build makes any of them true. They
;; describe VM-internal states - an unsigned stack slot, a void return,
;; a mutation lock - that no value reaching lisp code carries. Pinned so
;; that the day one of them starts answering true is visible.
(defun ibx/unsigned-any? ()
  (or (unsigned-integer? 0)
      (unsigned-integer? 1)
      (unsigned-integer? (len (vec 1 2)))))

(defun ibx/void-any? ()
  (or (void? nil)
      (void? (gc))
      (void? (push (vec) 1))
      (void? 0)))

(defun ibx/mut-locked-any? ()
  (or (mut-locked? (vec 1))
      (mut-locked? (make-table))
      (mut-locked? (list 1))
      (mut-locked? "abc")))

(test ibx-predicates-with-no-inhabitants
      (not (ibx/unsigned-any?))
      (not (ibx/void-any?))
      (not (ibx/mut-locked-any?)))

;; They are real functions, not missing ones: arity is checked.
(test ibx-those-predicates-still-check-arity
      (ibx/msg? 'arg-error "Argument Error: unsigned-integer? expected 1"
                '(if (unsigned-integer?) 1 2))
      ;; `void?` reports itself under its internal Rust name, `is_void`,
      ;; which is not a callable name in this language. Pinned as what it
      ;; says so the day it starts saying `void?` is visible.
      (ibx/msg? 'arg-error "Argument Error: is_void expected 1"
                '(if (void?) 1 2)))

;; `integer?` does answer true for the same values, so the distinction
;; `unsigned-integer?` draws is not visible from lisp at all.
(test ibx-integer-predicate-does-fire
      (integer? 0)
      (integer? (len (vec 1 2)))
      (not (integer? 1.5)))

;;; ---[ what `(functions)` is a list OF ]--------------------------------

;; `(functions)` enumerates global BINDINGS, not everything callable.
;; Nine builtins are compiled straight to an opcode at the call site and
;; have no global binding, so they work in call position, cannot be used
;; as values, and are absent from this list: list, vec, eq?, =, <, >,
;; <=, >= and append. Pinned so that a name appearing - or a listed one
;; vanishing - is a deliberate change rather than a silent one.
(defun ibx/listed? (name) (member? name (functions)))

(test ibx-functions-lists-bound-names-only
      ;; callable in operator position, every one of them
      (eq? '(1 2) (list 1 2))
      (eq? (vec 1 2) (vec 1 2))
      (eq? '(1 2) (append (list 1) (list 2)))
      (< 1 2)
      ;; and absent from the listing all the same
      (nil? (ibx/listed? 'list))
      (nil? (ibx/listed? 'vec))
      (nil? (ibx/listed? 'append))
      (nil? (ibx/listed? 'eq?))
      (nil? (ibx/listed? '<))
      ;; while the ordinary bound ones are there
      (= true (ibx/listed? 'car))
      (= true (ibx/listed? 'map))
      (= true (ibx/listed? 'for-each))
      (= true (ibx/listed? 'mat))
      ;; a name that does not exist at all is absent the same way, so
      ;; the listing cannot distinguish "opcode builtin" from "typo"
      (nil? (ibx/listed? 'ibx-no-such-function)))
