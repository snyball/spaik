(defun char=? (a b) (and a (eq? a b)))

(defun ws-char? (c)
  (or (char=? c (%chr " "))
      (or (char=? c (%chr "\t"))
          (or (char=? c (%chr "\n"))
              (char=? c (%chr "\r"))))))

(defun digit-char? (c)
  (case c
    ((%chr "0") true) ((%chr "1") true) ((%chr "2") true)
    ((%chr "3") true) ((%chr "4") true) ((%chr "5") true)
    ((%chr "6") true) ((%chr "7") true) ((%chr "8") true)
    ((%chr "9") true)
    (_ false)))

(defun digit-value (c)
  (case c
    ((%chr "0") 0) ((%chr "1") 1) ((%chr "2") 2)
    ((%chr "3") 3) ((%chr "4") 4) ((%chr "5") 5)
    ((%chr "6") 6) ((%chr "7") 7) ((%chr "8") 8)
    ((%chr "9") 9)
    (_ nil)))

(defun paren-open? (c) (char=? c (%chr "(")))
(defun paren-close? (c) (char=? c (%chr ")")))
(defun quote-char? (c) (char=? c (%chr "'")))
(defun backtick-char? (c) (char=? c (%chr "`")))
(defun comma-char? (c) (char=? c (%chr ",")))
(defun at-char? (c) (char=? c (%chr "@")))
(defun dquote-char? (c) (char=? c (%chr "\"")))
(defun semi-char? (c) (char=? c (%chr ";")))
(defun newline-char? (c) (char=? c (%chr "\n")))
(defun minus-char? (c) (char=? c (%chr "-")))
(defun backslash-char? (c) (char=? c (%chr "\\")))

(defun delim-char? (c)
  (if (not c) true
    (if (ws-char? c) true
      (if (paren-open? c) true
        (if (paren-close? c) true
          (if (quote-char? c) true
            (if (backtick-char? c) true
              (if (comma-char? c) true
                (if (dquote-char? c) true
                  (semi-char? c))))))))))

;; ---- reader parser state ----

(defun make-rparser (s)
  (let ((p (make-table))
        (chars (collect (iter s))))
    (set (get p 'chars) chars)
    (set (get p 'pos) 0)
    (set (get p 'len) (len chars))
    p))

(defun rat-end? (p) (>= (get p 'pos) (get p 'len)))
(defun rpeek (p) (if (rat-end? p) nil (get (get p 'chars) (get p 'pos))))
(defun rpeek-at (p i) (if (>= i (get p 'len)) nil (get (get p 'chars) i)))
(defun radvance! (p)
  (let ((c (rpeek p)))
    (set (get p 'pos) (+ (get p 'pos) 1))
    c))

(defun skip-line! (p)
  (loop
    (if (or (not (rpeek p)) (newline-char? (rpeek p)))
        (break))
    (radvance! p)))

(defun skip-ws-and-comments! (p)
  (loop
    (if (ws-char? (rpeek p))
        (radvance! p)
      (if (semi-char? (rpeek p))
          (skip-line! p)
        (break)))))

;; ---- vec/list glue ----

(defun vec->list (v)
  (let ((r nil) (i (- (len v) 1)))
    (loop
      (if (< i 0) (break))
      (set r (cons (get v i) r))
      (dec! i))
    r))

;; ---- reader: numbers / strings / symbols / lists ----

(defun read-number! (p)
  (let ((neg (if (minus-char? (rpeek p)) (progn (radvance! p) true) false))
        (acc 0))
    (loop
      (if (not (digit-char? (rpeek p)))
          (break))
      (set acc (+ (* acc 10) (digit-value (radvance! p)))))
    (if neg (- acc) acc)))

(defun read-escape! (p)
  (let ((e (radvance! p)))
    (if (char=? e (%chr "n")) (%chr "\n")
      (if (char=? e (%chr "t")) (%chr "\t")
        (if (char=? e (%chr "\\")) (%chr "\\")
          (if (char=? e (%chr "\"")) (%chr "\"")
            e))))))

(defun read-string! (p)
  (radvance! p) ;; opening quote
  (let ((chars (vec)))
    (loop
      (let ((c (rpeek p)))
        (if (not c)
            (error 'unterminated-string)
          (if (dquote-char? c)
              (progn (radvance! p) (break))
            (if (backslash-char? c)
                (progn (radvance! p) (push chars (read-escape! p)))
              (push chars (radvance! p)))))))
    (join chars)))

(defun symbolize (s)
  (if (= s "nil") nil
    (if (= s "true") true
      (if (= s "false") false
        (intern s)))))

(defun read-symbol! (p)
  (let ((chars (vec)))
    (loop
      (if (delim-char? (rpeek p))
          (break))
      (push chars (radvance! p)))
    (symbolize (join chars))))

(defun read-list! (p)
  (radvance! p) ;; '('
  (let ((items (vec)))
    (loop
      (skip-ws-and-comments! p)
      (if (paren-close? (rpeek p))
          (progn (radvance! p) (break))
        (if (not (rpeek p))
            (error 'unterminated-list)
          (push items (read-expr! p)))))
    (vec->list items)))

(defun looks-like-number? (p)
  (let ((c (rpeek p)))
    (or (digit-char? c)
        (and (minus-char? c)
             (digit-char? (rpeek-at p (+ (get p 'pos) 1)))))))

(defun read-quoted-form! (p sym)
  (radvance! p)
  (cons sym (cons (read-expr! p) nil)))

(defun read-comma-form! (p)
  (radvance! p) ;; ','
  (if (at-char? (rpeek p))
      (progn (radvance! p) (cons 'unquote-splicing (cons (read-expr! p) nil)))
    (cons 'unquote (cons (read-expr! p) nil))))

(defun read-expr! (p)
  (skip-ws-and-comments! p)
  (let ((c (rpeek p)))
    (if (not c)
        (error 'unexpected-eof)
      (if (paren-open? c)
          (read-list! p)
        (if (quote-char? c)
            (read-quoted-form! p 'quote)
          (if (backtick-char? c)
              (read-quoted-form! p 'quasiquote)
            (if (comma-char? c)
                (read-comma-form! p)
              (if (dquote-char? c)
                  (read-string! p)
                (if (looks-like-number? p)
                    (read-number! p)
                  (read-symbol! p))))))))))

(defun read-all! (src)
  (let ((p (make-rparser src))
        (out (vec)))
    (loop
      (skip-ws-and-comments! p)
      (if (rat-end? p)
          (break))
      (push out (read-expr! p)))
    out))

;; ---- environments ----
;; env = a (host) cons-list of frames; frame = a (host) table mapping
;; toy-language symbol -> (vec value) wrapper, so presence can be told
;; apart from "bound to nil" (a bare `get` on a missing table key also
;; returns nil - see suspect notes elsewhere on table semantics).

(defun frame-define! (frame sym val)
  (set (get frame sym) (vec val)))

(defun env-lookup (env sym)
  (if (nil? env)
      (error 'unbound-variable)
    (let ((cell (get (car env) sym)))
      (if cell
          (get cell 0)
        (env-lookup (cdr env) sym)))))

(defun env-set! (env sym val)
  (if (nil? env)
      (error 'unbound-variable-set)
    (let ((cell (get (car env) sym)))
      (if cell
          (set (get cell 0) val)
        (env-set! (cdr env) sym val)))))

(defun env-define! (env sym val)
  (frame-define! (car env) sym val))

;; ---- evaluator ----

(defun make-closure-raw (params body env)
  (vec 'closure params body env))

(defun closure? (v)
  (and (vec? v) (> (len v) 0) (= (get v 0) 'closure)))

;; `&opt name` binds to nil when the caller didn't supply that argument.
;; `&rest name` (or the remaining args after &opt ones) binds the rest of
;; the argument list, unevaluated-count-wise, as a single list.
(defun bind-params! (frame params args)
  (if (nil? params)
      nil
    (if (= (car params) '&opt)
        (bind-opt-params! frame (cdr params) args)
      (if (= (car params) '&rest)
          (frame-define! frame (cadr params) args)
        (progn
          (frame-define! frame (car params) (if (nil? args) nil (car args)))
          (bind-params! frame (cdr params) (if (nil? args) nil (cdr args))))))))

(defun bind-opt-params! (frame params args)
  (if (nil? params)
      nil
    (if (= (car params) '&rest)
        (frame-define! frame (cadr params) args)
      (progn
        (frame-define! frame (car params) (if (nil? args) nil (car args)))
        (bind-opt-params! frame (cdr params) (if (nil? args) nil (cdr args)))))))

(defun apply-fn (fn argvals)
  (if (closure? fn)
      (let ((params (get fn 1)) (body (get fn 2)) (closure-env (get fn 3)))
        (let ((frame (make-table)))
          (bind-params! frame params argvals)
          (eval-body body (cons frame closure-env))))
    (apply fn argvals)))

;; A `break` mid-sequence must stop evaluating the REST of the sequence
;; and propagate the break signal upward untouched (see `break-signal?`
;; below, and the note above `eval-loop`/`eval-dolist` on why this is
;; implemented via an ordinary returned value rather than `catch`/`throw`).
(defun eval-body (exprs env)
  (if (nil? exprs)
      nil
    (let ((v (eval-expr (car exprs) env)))
      (if (break-signal? v)
          v
        (if (nil? (cdr exprs))
            v
          (eval-body (cdr exprs) env))))))

(defun eval-if (args env)
  (let ((test (eval-expr (car args) env)))
    (if test
        (eval-expr (cadr args) env)
      (if (cddr args)
          (eval-expr (caddr args) env)
        nil))))

(defun eval-define (args env)
  (let ((target (car args)))
    (if (cons? target)
        (let ((name (car target)) (params (cdr target)))
          (env-define! env name (make-closure-raw params (cdr args) env))
          name)
      (progn
        (env-define! env target (eval-expr (cadr args) env))
        target))))

(defun eval-defun (args env)
  (let ((name (car args)) (params (cadr args)) (body (cddr args)))
    (env-define! env name (make-closure-raw params body env))
    name))

;; `set` supports two kinds of place: a bare variable, or `(get obj key)`
;; (a table/vec field) - the latter mutates the REAL underlying host
;; table/vec object directly via the host's own generalized `set`/`get`,
;; since guest-level tables/vecs ARE host tables/vecs (see file header).
(defun eval-set-form (args env)
  (let ((place (car args)))
    (if (symbol? place)
        (let ((val (eval-expr (cadr args) env)))
          (env-set! env place val)
          val)
      (if (and (cons? place) (= (car place) 'get))
          (let ((obj (eval-expr (cadr place) env))
                (key (eval-expr (caddr place) env))
                (val (eval-expr (cadr args) env)))
            (set (get obj key) val)
            val)
        (error 'bad-set-place)))))

(defun bind-let-frame! (frame bindings env)
  (if (nil? bindings)
      nil
    (let ((b (car bindings)))
      (frame-define! frame (car b) (eval-expr (cadr b) env))
      (bind-let-frame! frame (cdr bindings) env))))

(defun eval-let-form (args env)
  (let ((bindings (car args)) (body (cdr args)))
    (let ((frame (make-table)))
      (bind-let-frame! frame bindings env)
      (eval-body body (cons frame env)))))

;; `let*` bindings see earlier bindings from the SAME `let*` (unlike
;; `let`) - implemented by defining each binding, one at a time, into a
;; single frame that's already threaded into the env used to evaluate the
;; NEXT binding's init expression.
(defun bind-let-star-frame! (frame bindings env)
  (if (nil? bindings)
      nil
    (let ((b (car bindings)))
      (frame-define! frame (car b) (eval-expr (cadr b) (cons frame env)))
      (bind-let-star-frame! frame (cdr bindings) env))))

(defun eval-let-star-form (args env)
  (let ((bindings (car args)) (body (cdr args)))
    (let ((frame (make-table)))
      (bind-let-star-frame! frame bindings env)
      (eval-body body (cons frame env)))))

(defun eval-and (args env)
  (if (nil? args)
      true
    (let ((v (eval-expr (car args) env)))
      (if v
          (if (nil? (cdr args)) v (eval-and (cdr args) env))
        false))))

(defun eval-or (args env)
  (if (nil? args)
      false
    (let ((v (eval-expr (car args) env)))
      (if v v (eval-or (cdr args) env)))))

(defun eval-when (args env)
  (if (eval-expr (car args) env)
      (eval-body (cdr args) env)
    nil))

(defun eval-unless (args env)
  (if (eval-expr (car args) env)
      nil
    (eval-body (cdr args) env)))

(defun eval-cond (clauses env)
  (if (nil? clauses)
      nil
    (let ((clause (car clauses)))
      (if (eval-expr (car clause) env)
          (eval-body (cdr clause) env)
        (eval-cond (cdr clauses) env)))))

;; `case` clause keys are, in practice, always written as quoted literals
;; (e.g. `('archivist-ghost ...)`), so evaluating each key (`quote` just
;; unwraps to the symbol) and comparing with `eq?` matches the intended
;; "compare against this literal" semantics, except for the bare `_`
;; catch-all marker, which is never itself evaluated.
(defun eval-case-clauses (key clauses env)
  (if (nil? clauses)
      nil
    (let ((clause (car clauses)))
      (if (= (car clause) '_)
          (eval-body (cdr clause) env)
        (if (eq? key (eval-expr (car clause) env))
            (eval-body (cdr clause) env)
          (eval-case-clauses key (cdr clauses) env))))))

(defun eval-case (args env)
  (eval-case-clauses (eval-expr (car args) env) (cdr args) env))

;; `loop`/`break`: NOT implemented via the host's `catch`/`throw` - a
;; fuzzing find made while building this: `catch` used as a NON-TAIL
;; statement inside a `let`, with the let-bound variable read again
;; afterward, silently truncates the program (no output at all, exit 0),
;; even when the `catch`'s body never actually `throw`s - see
;; suspect/catch-non-tail-in-let-drops-rest.lisp. Same family as the
;; (fixed) `if`/`loop`-`break` stack-cleanup bugs, but for `catch`, and
;; NOT fixed.
;;
;; Instead, a toy-level `break` is implemented as an ORDINARY VALUE - a
;; tagged "break signal" vec - that `eval-body` (see above) recognizes
;; and propagates without evaluating the rest of a sequence, and that
;; `eval-loop`/`eval-dolist` recognize and use to stop the HOST's own
;; (confirmed-safe) `loop`/`dolist`+`break`. This only needs to work
;; within a single toy-level function activation (the shape every
;; `break` in lisp/adventure.lisp actually uses - never escaping through
;; a toy-level function-call boundary to a caller's loop), so no general
;; non-local-exit mechanism is required at all.
(defun make-break-signal (val) (vec '<break-signal> val))
(defun break-signal? (v) (and (vec? v) (> (len v) 0) (= (get v 0) '<break-signal>)))
(defun break-signal-value (v) (get v 1))

(defun eval-break (args env)
  (make-break-signal (if (nil? args) nil (eval-expr (car args) env))))

(defun eval-loop (body env)
  (let ((result nil))
    (loop
      (let ((v (eval-body body env)))
        (if (break-signal? v)
            (progn (set result (break-signal-value v)) (break))
          nil)))
    result))

;; `dolist` iterates a real host sequence (vec or cons-list) - guest-level
;; sequences ARE host sequences (see file header), so the HOST's own
;; `dolist` can walk it directly; each iteration gets a fresh frame.
(defun eval-dolist (args env)
  (let ((binding (car args)) (body (cdr args)))
    (let ((var (car binding)) (seq (eval-expr (cadr binding) env)) (result nil))
      (dolist (item seq)
        (let ((frame (make-table)))
          (frame-define! frame var item)
          (let ((v (eval-body body (cons frame env))))
            (if (break-signal? v)
                (progn (set result (break-signal-value v)) (break))
              nil))))
      result)))

;; ---- macros ----
;; A separate table (symbol -> macro closure) from the variable
;; environment. Macro closures are created just like function closures
;; (`make-closure-raw`), so expansion reuses `apply-fn`/`bind-params!`
;; unchanged - the only difference is the RAW (unevaluated) argument
;; forms are passed in directly instead of first being evaluated.

(define *macro-table* (make-table))
(defun macro-define! (sym val) (set (get *macro-table* sym) val))
(defun macro-lookup (sym) (if (symbol? sym) (get *macro-table* sym) nil))

(defun eval-defmacro (args env)
  (let ((name (car args)) (params (cadr args)) (body (cddr args)))
    (macro-define! name (make-closure-raw params body env))
    name))

;; ---- quasiquote ----
;; Standard recursive template expansion: `,x` evaluates x and splices
;; its VALUE in; `,@x` evaluates x (expected to be a list) and splices
;; its ELEMENTS in; everything else is copied as literal (unevaluated)
;; data, exactly like `quote`, except symbols are not looked up.

(defun qq-splice-head? (tmpl)
  (and (cons? tmpl) (cons? (car tmpl)) (= (car (car tmpl)) 'unquote-splicing)))

(defun qq-expand (tmpl env)
  (if (cons? tmpl)
      (if (= (car tmpl) 'unquote)
          (eval-expr (cadr tmpl) env)
        (if (qq-splice-head? tmpl)
            (append (eval-expr (cadr (car tmpl)) env) (qq-expand (cdr tmpl) env))
          (cons (qq-expand (car tmpl) env) (qq-expand (cdr tmpl) env))))
    tmpl))

;; ---- list-form dispatch ----

(defun eval-args (args env)
  (map (lambda (a) (eval-expr a env)) args))

(defun eval-list-form (expr env)
  (let ((op (car expr)) (args (cdr expr)))
    (cond
     ((= op 'quote) (car args))
     ((= op 'quasiquote) (qq-expand (car args) env))
     ((= op 'if) (eval-if args env))
     ((= op 'define) (eval-define args env))
     ((= op 'defun) (eval-defun args env))
     ((= op 'set) (eval-set-form args env))
     ((= op 'lambda) (make-closure-raw (car args) (cdr args) env))
     ((= op 'begin) (eval-body args env))
     ((= op 'progn) (eval-body args env))
     ((= op 'let) (eval-let-form args env))
     ((= op 'let*) (eval-let-star-form args env))
     ((= op 'and) (eval-and args env))
     ((= op 'or) (eval-or args env))
     ((= op 'when) (eval-when args env))
     ((= op 'unless) (eval-unless args env))
     ((= op 'cond) (eval-cond args env))
     ((= op 'case) (eval-case args env))
     ((= op 'loop) (eval-loop args env))
     ((= op 'break) (eval-break args env))
     ((= op 'dolist) (eval-dolist args env))
     ((= op 'defmacro) (eval-defmacro args env))
     ;; `%chr` (core.lisp) computes a CHARACTER VALUE directly at
     ;; expansion time (it isn't template/quasiquote-based like ordinary
     ;; macros), so it's handled natively here rather than through the
     ;; guest macro table: `s` below is the raw arg form, which for the
     ;; only shape actually used (a string literal, e.g. `(%chr " ")`) is
     ;; already self-evaluating data, exactly matching what the host's
     ;; own `(defmacro %chr (s) (chr s))` does with its raw macro param.
     ((= op '%chr) (chr (car args)))
     ((macro-lookup op) (eval-expr (apply-fn (macro-lookup op) args) env))
     (true (apply-fn (eval-expr op env) (eval-args args env))))))

;; Anything that isn't a symbol (a variable reference) or a cons (a form
;; to evaluate) is self-evaluating data as-is - this covers numbers,
;; strings, bools, nil, AND characters (produced by `%chr` above; there's
;; no `char?` predicate to special-case them by type, so this is the
;; general rule rather than a type whitelist).
(defun eval-expr (expr env)
  (if (symbol? expr)
      (env-lookup env expr)
    (if (cons? expr)
        (eval-list-form expr env)
      expr)))

;; ---- global environment ----

(defun host-list (&rest xs) xs)
;; `< > <= >= = eq?` (unlike `+ - * /`, and unlike `cons`/`car`/`cdr`/
;; `not` which core.lisp explicitly wraps "so they can be passed as
;; closures") are NOT first-class values in the host language - see
;; suspect/comparison-operators-not-first-class.lisp. Wrap them here so
;; they can live in the toy interpreter's global frame like everything
;; else. `vec`, `make-table`, and `next` turn out to belong to this same
;; "not first-class" family (bare references to them fail to compile at
;; all - "Undefined Variable: vec" etc, confirmed empirically) even
;; though core.lisp never needed to wrap them itself (it only ever uses
;; them in direct call position). `set` is NOT wrapped here at all - it's
;; handled entirely as a special form (see `eval-set-form`) since its
;; first argument is a PLACE, not a value to evaluate normally.
(defun host-lt (a b) (< a b))
(defun host-gt (a b) (> a b))
(defun host-lte (a b) (<= a b))
(defun host-gte (a b) (>= a b))
(defun host-eq (a b) (= a b))
(defun host-eqp (a b) (eq? a b))
(defun host-vec (&rest xs)
  (let ((v (vec)))
    (dolist (x xs) (push v x))
    v))
(defun host-make-table () (make-table))
(defun host-next (it) (next it))

(define *global-frame* (make-table))
(defun gbind! (sym val) (frame-define! *global-frame* sym val))

(gbind! '+ +)
(gbind! '- -)
(gbind! '* *)
(gbind! '/ / )
(gbind! '< host-lt)
(gbind! '> host-gt)
(gbind! '<= host-lte)
(gbind! '>= host-gte)
(gbind! '= host-eq)
(gbind! 'eq? host-eqp)
(gbind! 'cons cons)
(gbind! 'car car)
(gbind! 'cdr cdr)
(gbind! 'not not)
(gbind! 'println _println)
(gbind! 'list host-list)
(gbind! 'nil? nil?)
(gbind! 'cons? cons?)
(gbind! 'vec host-vec)
(gbind! 'vec? vec?)
(gbind! 'make-table host-make-table)
(gbind! 'get get)
(gbind! 'push push)
(gbind! 'len len)
(gbind! 'concat concat)
(gbind! 'join join)
(gbind! 'iter iter)
(gbind! 'next host-next)
(gbind! 'collect collect)
(gbind! 'intern intern)
(gbind! 'zip zip)
(gbind! 'elem? elem?)
(gbind! 'symbol? symbol?)
(gbind! 'string? string?)
(gbind! 'number? number?)
(gbind! 'apply apply-fn)

(define *global-env* (cons *global-frame* nil))

(defun run-toy (src)
  (let ((forms (read-all! src)))
    (dolist (f forms)
      (println (eval-expr f *global-env*)))))

;; Like `run-toy`, but doesn't echo every top-level form's return value -
;; appropriate for running a real PROGRAM (like adventure.lisp) whose own
;; `println` calls are the intended output, rather than the small
;; REPL-style demo below.
(defun run-toy-quiet (src)
  (let ((forms (read-all! src)))
    (dolist (f forms)
      (eval-expr f *global-env*))))

;; ---- demo program, written as toy-language SOURCE TEXT (a string) -
;; parsed by OUR OWN read-all!, not the host reader. ----

(define *program*
  "; factorial via recursion
   (define (fact n)
     (if (= n 0)
         1
         (* n (fact (- n 1)))))
   (println (fact 10))

   ; closures / higher-order functions
   (define (make-adder n)
     (lambda (x) (+ x n)))
   (define add5 (make-adder 5))
   (println (add5 100))

   ; let, and/or, recursion via a helper
   (define (sum-to n acc)
     (if (= n 0)
         acc
         (sum-to (- n 1) (+ acc n))))
   (let ((total (sum-to 10 0)))
     (println total))

   (println (and true true 42))
   (println (and true false 42))
   (println (or false false 7))

   ; lists and quote
   (println (cons 1 (cons 2 (cons 3 nil))))
   (println '(a b c))
   (println (list 1 2 3))

   ; strings
   (println \"hello, self-hosted world\")

   ; mutation via set
   (define counter 0)
   (define (bump!) (set counter (+ counter 1)))
   (bump!) (bump!) (bump!)
   (println counter)

   ; the new stuff: quasiquote/defmacro, loop/break, cond/case, dolist,
   ; tables/vecs, &opt params - all needed by lisp/adventure.lisp.
   (defmacro double! (x) `(set ,x (* ,x 2)))
   (define eight 4)
   (double! eight)
   (println eight)

   (define (count-to n)
     (let ((i 0))
       (loop
         (if (>= i n) (break))
         (set i (+ i 1)))
       i))
   (println (count-to 5))

   (define (classify n)
     (cond
      ((< n 0) 'negative)
      ((= n 0) 'zero)
      (true 'positive)))
   (println (classify -3))
   (println (classify 0))
   (println (classify 3))

   (define (day-kind d)
     (case d
       ('sat 'weekend)
       ('sun 'weekend)
       (_ 'weekday)))
   (println (day-kind 'sat))
   (println (day-kind 'tue))

   (define total-vec 0)
   (dolist (x (vec 1 2 3 4 5))
     (set total-vec (+ total-vec x)))
   (println total-vec)

   (define t (make-table))
   (set (get t 'a) 1)
   (println (get t 'a))

   (define (greet name &opt greeting)
     (concat (or greeting \"Hello\") \", \" name \"!\"))
   (println (greet \"world\"))
   (println (greet \"world\" \"Hi\"))")

(println "=== toy interpreter output ===")
(run-toy *program*)
(println "=== done with demo ===")

;; ---- now the real thing: run lisp/adventure.lisp AS GUEST CODE ----
;;
;; adventure.lisp uses a couple of core.lisp MACROS directly (`inc!`/
;; `dec!`) that aren't special forms of this toy language - define them
;; the same way core.lisp does, as ordinary guest-level macros, before
;; loading the real program.

(define *prelude*
  "(defmacro inc! (var &opt n) `(set ,var (+ ,var ,(or n 1))))
   (defmacro dec! (var &opt n) `(set ,var (- ,var ,(or n 1))))")

(test ultra-synthetic-adventure
      (= "=== adventure.lisp finished ==="
         (progn
           (println "=== running lisp/adventure.lisp through the self-hosted interpreter ===")
           (run-toy-quiet *prelude*)
           (run-toy-quiet (slurp "tests/adventure.lisp"))
           (println "=== adventure.lisp finished ==="))))
