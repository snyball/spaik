;;; What tables and the type predicates raise, and under which tag.
;;; Catch outside, eval inside, eval in tail position.
;;; Companion to tests/builtin-error-reporting.lisp.

(defun tabx/catch (tag form) (catch tag (eval form)))

(defun tabx/starts-with? (prefix s)
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

(defun tabx/msg? (tag prefix form)
  (let ((v (tabx/catch tag form)))
    (and (string? v) (tabx/starts-with? prefix v))))

;;; ---[ make-table takes key/value PAIRS ]-----------------------------

(test tabx-make-table-arity
      ;; an odd argument count is an arity error, and the count it
      ;; reports is the even one it wanted, not the one it got
      (tabx/msg? 'arg-error "Argument Error: make-table expected 2 arguments, but got 1"
                 '(make-table 1))
      (tabx/msg? 'arg-error "Argument Error: make-table expected 2 arguments, but got 1"
                 '(make-table :a))
      (tabx/msg? 'arg-error "Argument Error: make-table expected 4 arguments, but got 3"
                 '(make-table :a 1 :b))
      ;; even counts are fine, and the keys need not be keywords
      (table? (tabx/catch 'arg-error '(make-table)))
      (table? (tabx/catch 'arg-error '(make-table :a 1 :b 2)))
      (table? (tabx/catch 'arg-error '(make-table 1 2))))

;;; ---[ a missing key is nil, not an error ]---------------------------

(test tabx-missing-key-is-not-an-error
      ;; there is no key-error in this dialect: absent keys read as nil,
      ;; on an empty table and a populated one alike
      (nil? (tabx/catch 'index-error '(get (make-table) :k)))
      (nil? (tabx/catch 'index-error '(get (make-table :a 1) :b)))
      (nil? (tabx/catch 'type-error '(get (make-table) 5)))
      ;; present keys read back, including non-keyword keys
      (= 1 (tabx/catch 'index-error '(get (make-table :a 1) :a)))
      (= 2 (tabx/catch 'index-error '(get (make-table 1 2) 1)))
      ;; and writing through a missing key is accepted
      (= 9 (tabx/catch 'index-error '(set (get (make-table) :k) 9))))

;;; ---[ get/set on a non-container ]-----------------------------------

(test tabx-get-type-and-arity
      ;; `get`'s type error enumerates what it does accept, so this
      ;; doubles as a check that the set has not silently changed
      (tabx/msg? 'type-error "Type Error: Expected one of vec, vec2, vec3, table in get, but got integer"
                 '(get 5 :k))
      (tabx/msg? 'type-error "Type Error: Expected one of vec, vec2, vec3, table in get, but got string"
                 '(get "abc" 0))
      (tabx/msg? 'arg-error "Argument Error: get expected 2 arguments, but got 0" '(get))
      (tabx/msg? 'arg-error "Argument Error: get expected 2 arguments, but got 1" '(get (make-table)))
      (tabx/msg? 'arg-error "Argument Error: get expected 2" '(get (make-table) :k :extra)))

;;; ---[ a table is not a sequence ]------------------------------------

(test tabx-table-is-not-a-sequence
      ;; the sequence builtins reject it by name, each naming the types
      ;; it does take
      (tabx/msg? 'type-error "Type Error: Expected one of vec, cons, string but got table"
                 '(reverse (make-table)))
      (tabx/msg? 'type-error "Type Error: Expected one of vec, cons but got table"
                 '(sort (make-table)))
      (tabx/msg? 'type-error "Type Error: Expected vec in push, but got table"
                 '(push (make-table) 1))
      (tabx/msg? 'type-error "Type Error: Expected vec in pop, but got table"
                 '(pop (make-table)))
      ;; ... but `len` and `iter` DO take one
      (= 0 (tabx/catch 'type-error '(len (make-table))))
      (= 2 (tabx/catch 'type-error '(len (make-table :a 1 :b 2))))
      (= 0 (tabx/catch 'type-error '(len (collect (iter (make-table)))))))

;;; ---[ the type predicates are arity-checked ]-------------------------

(test tabx-predicate-arity
      ;; every predicate takes exactly one argument; neither zero nor two
      (tabx/msg? 'arg-error "Argument Error: table? expected 1 argument, but got 0" '(table?))
      (tabx/msg? 'arg-error "Argument Error: table? expected 1 argument, but got 2" '(table? 1 2))
      (tabx/msg? 'arg-error "Argument Error: vec? expected 1 argument, but got 2" '(vec? 1 2))
      (tabx/msg? 'arg-error "Argument Error: string? expected 1 argument, but got 0" '(string?))
      ;; a predicate never raises on a wrong TYPE - that is the point of
      ;; it - so every one-argument call answers instead
      (= false (tabx/catch 'type-error '(table? 5)))
      (= true (tabx/catch 'type-error '(table? (make-table)))))
