;;; Values the collector can only see through the VM's own machinery:
;;; operand stack, argument lists, macro expander, builtin accumulators.
;;; Every fixture collects while the value has no named binding.

;; Allocation pressure helper. Varied sizes on purpose - a monoculture
;; exercises one free-list path.
(defun gcr/churn (n)
  (let ((s (vec)) (i 0))
    (while (< i n)
      (push s (make-table))
      (push s (vec i (+ i 1)))
      (push s (concat "r-" i))
      (if (> (len s) 300) (set s (vec)))
      (set i (+ i 1)))
    (len s)))

;; ====================================================================
;; alive only on the operand stack
;; ====================================================================
;; The first and last vec exist only as half-evaluated arguments while
;; the middle one forces a collection. Nothing names them.

(defun gcr/operand-stack ()
  (let ((r (list (vec "a" (list 1 2))
                 (progn (gc) 0)
                 (vec "b" (list 3 4)))))
    (list (get (car r) 0) (get (car (cdr (cdr r))) 0))))

;; The same through a user function's parameters rather than a builtin's.
(defun gcr/take (a b c) (list (get a 0) c (get b 0)))
(defun gcr/fn-arguments ()
  (gcr/take (vec "x" (list 1)) (vec "y" (list 2)) (progn (gc) :mid)))

;; And through a rest-argument list, which the VM materialises itself.
(defun gcr/rest (&rest xs)
  (let ((n (len xs)))
    (gc)
    (list n (get (car xs) 0) (get (car (cdr xs)) 0))))
(defun gcr/rest-arguments ()
  (gcr/rest (vec "r0") (vec "r1") (vec "r2")))

(test gcr-values-alive-only-on-the-operand-stack
      (eq? '("a" "b") (gcr/operand-stack))
      (eq? '("x" :mid "y") (gcr/fn-arguments))
      (eq? '(3 "r0" "r1") (gcr/rest-arguments)))


;; ====================================================================
;; locals of every frame in a deep call chain
;; ====================================================================
;; One live compound per frame, 300 frames deep, collected at the
;; bottom. The sum is what proves each frame's local survived.

(defun gcr/deep (n)
  (let ((mine (vec n (concat "d" n))))
    (if (< n 1)
        (progn (gc) (get mine 0))
      (+ (get mine 0) (gcr/deep (- n 1))))))

(test gcr-locals-of-every-frame-survive
      (= 45150 (gcr/deep 300)))


;; ====================================================================
;; inside eval, and inside a macro expander
;; ====================================================================
;; Both run the collector in a phase that is not ordinary evaluation:
;; `eval` compiles first, and the expander runs while a half-built form
;; is live only in the compiler.

(defun gcr/eval-gc ()
  (eval '(let ((v (vec "e" (list 7)))) (gc) (get v 0))))

(defmacro gcr/wrap (&body body)
  (gc)
  (let ((r `(list ,@body)))
    (gc)
    r))
(defun gcr/expander-gc () (gcr/wrap 1 (+ 1 1) "three"))

;; A runtime `macroexpand` with a collection before each one: the form
;; it answers is freshly consed and reachable only from the expander.
(defun gcr/macroexpand-gc (n)
  (let ((bad 0) (i 0))
    (while (< i n)
      (gc)
      (let ((e (macroexpand '(when (< 1 2) (+ 1 2)))))
        (unless (eq? (car e) 'if) (set bad (+ bad 1))))
      (set i (+ i 1)))
    bad))

(test gcr-collections-during-compilation
      (= "e" (gcr/eval-gc))
      (eq? '(1 2 "three") (gcr/expander-gc))
      (= 0 (gcr/macroexpand-gc 200)))


;; ====================================================================
;; accumulators inside builtins, while user code collects
;; ====================================================================
;; `map`, `filter`, `zip`, `sort` and `apply` build their result in
;; Rust while calling back into Lisp. The half-built result is live only
;; in that builtin's own state, so a collection driven from the callback
;; is the case where it has to be a root.

(defun gcr/map-accumulator (n)
  (let ((bad 0) (i 0))
    (dolist (e (map (lambda (x) (gc) (vec x (concat "m" x))) (range-list 0 n)))
      (unless (= (get e 0) i) (set bad (+ bad 1)))
      (unless (= (get e 1) (concat "m" i)) (set bad (+ bad 1)))
      (set i (+ i 1)))
    (unless (= i n) (set bad (+ bad 1)))
    bad))

(defun gcr/filter-accumulator (n)
  (len (filter (lambda (x) (gc) (< x n)) (range-list 0 n))))

(defun gcr/zip-accumulator (n)
  (let ((a (map (lambda (x) (gc) (vec x (concat "z" x))) (range-list 0 n))))
    (let ((z (zip a (range-list 0 n))))
      (list (len z) (get (car (car z)) 1)))))

(defun gcr/sort-accumulator (n)
  (let ((xs (map (lambda (x) (gc) (% (* x 7919) 1000)) (range-list 0 n))))
    (let ((s (sort xs)) (bad 0) (prev -1))
      (dolist (e s)
        (when (< e prev) (set bad (+ bad 1)))
        (set prev e))
      (unless (= (len s) n) (set bad (+ bad 1)))
      bad)))

(defun gcr/apply-arguments (n)
  (apply + (map (lambda (x) (gc) x) (range-list 0 n))))

;; `join` over strings that were each allocated across a collection.
(defun gcr/join-accumulator (n)
  (len (join (map (lambda (x) (gc) (concat "s" x "-")) (range-list 0 n)))))

(test gcr-builtin-accumulators-are-roots
      (= 0 (gcr/map-accumulator 120))
      (= 120 (gcr/filter-accumulator 120))
      (eq? '(120 "z0") (gcr/zip-accumulator 120))
      (= 0 (gcr/sort-accumulator 120))
      (= 7140 (gcr/apply-arguments 120))
      ;; "s0-" .. "s119-": 10*3 + 90*4 + 20*5 = 490
      (= 490 (gcr/join-accumulator 120)))


;; ====================================================================
;; a thrown payload built under pressure, caught through a helper
;; ====================================================================
;; The payload is live only in the unwind machinery between the throw
;; and the catch. `catch` is the tail of its own helper deliberately.

(defun gcr/throw-payload (i)
  (gcr/churn 40)
  (throw 'gcr-tag (vec (concat "t-" i) (list i i))))
(defun gcr/catch-payload (i)
  (catch 'gcr-tag (gcr/throw-payload i)))

(defun gcr/unwound-payloads (rounds)
  (let ((bad 0) (i 0) (got nil))
    (while (< i rounds)
      (set got (gcr/catch-payload i))
      (gc)
      (unless (= (get got 0) (concat "t-" i)) (set bad (+ bad 1)))
      (unless (= (car (get got 1)) i) (set bad (+ bad 1)))
      (set i (+ i 1)))
    bad))

(test gcr-thrown-payload-is-a-root-during-the-unwind
      (= 0 (gcr/unwound-payloads 120)))
