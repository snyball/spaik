;;; A few milliseconds of the MEMORY-sensitive API: allocating every heap
;;; representation into one nested cyclic structure, mutating it in place,
;;; and holding iterators, continuations and generators across collections.

;; Deliberately narrow, and sized to a budget. Arithmetic, message text
;; and the pure-value corners of the stdlib are covered elsewhere and are
;; left out: nothing is asserted here unless the interesting part is an
;; allocation, a write into an object that already exists, a collection,
;; or a stack being saved and reinstated - the places an interpreter
;; keeps its unsafe code. Volumes are the largest that still fit inside
;; roughly 30ms of ordinary interpreter time, so the file stays tractable
;; when every one of those operations is being checked as it runs.
;;
;; Read the per-test times before adding to it: the budget is the whole
;; file, not any one test.

;;; ---[ helpers ]-----------------------------------------------------------

(defun mrm/catch (tag form) (catch tag (eval form)))

;; Allocation pressure: n throwaway compounds, none of them reachable
;; afterwards. Enough to move the collector along without being a
;; benchmark.
(defun mrm/churn (n)
  (let ((junk (vec)))
    (range (i (0 n))
      (push junk (vec i (concat "j" i) (make-table :i i))))
    (len junk)))

;; A vec used as a mutable cell. Lambdas capture immediates by copy, so a
;; counter kept in a plain `let` binding cannot be written from inside a
;; closure - a one-slot vec can, and the write goes through the heap.
(defun mrm/cell ()     (vec 0))
(defun mrm/bump! (c n) (set (get c 0) (+ (get c 0) n)))

;; The standard generator source. Its final value is `:mrm-end` rather
;; than the nil a bare `dolist` leaves, so an exhaustion is always
;; distinguishable from a yield by value alone.
(defun mrm/of (xs)
  (gen (lambda (yi) (dolist (x xs) (yi x)) :mrm-end)))

(defun mrm/drain (co)
  (let ((out (vec)))
    (catch 'done (loop (push out (co nil))))
    out))

(defun mrm/take (co n)
  (let ((out (vec)))
    (while (> n 0)
      (push out (co nil))
      (dec! n))
    out))

;;; ---[ the one big structure ]---------------------------------------------

;; Every runtime representation this dialect can allocate, in one table:
;; the immediates, the three heap sequences, both flavours of callable, a
;; live iterator, a suspended generator, a captured continuation, the
;; fixed-width vectors and the three matrix widths. It closes over itself
;; under `:self`, so anything that walks or marks it has to cope with a
;; cycle, and nests a table inside a vec inside a table under `:inner`.
;;
;; Built fresh per call on purpose: every test gets an untouched copy, so
;; the mutating sections cannot leak into the reading ones, and each call
;; is another round of allocation through every constructor at once.

(defun mrm/world ()
  (let ((tb (make-table
             :int    42
             :float  1.5
             :string (concat "spa" "ik")
             :char   (chr "s")
             :sym    'mrm-a-symbol
             :kw     :mrm-a-keyword
             :bool   true
             :none   nil
             :cons   (list 1 2 3)
             :vec    (vec :a :b :c)
             :fn     (lambda (x) (* x 2))
             :subr   car
             :gen    (mrm/of '(10 20))
             :iter   (iter (list :i0 :i1))
             :v2     (vec2 1 2)
             :v3     (vec3 1 2 3)
             :v4     (vec4 1 2 3 4)
             :m2     (mat (vec2 1 0) (vec2 0 1))
             :m3     (mat (vec3 2 0 0) (vec3 0 2 0) (vec3 0 0 1))
             :m4     (translate (vec3 5 6 7)))))
    (set (get tb :inner) (make-table :deep (vec (list :leaf 7))))
    (set (get tb :cont) (call/cc (lambda (k) k)))
    (set (get tb :self) tb)
    tb))

(defun mrm/field (k) (get (mrm/world) k))

(defun mrm/type-of-field (k) (type-of (mrm/field k)))

;; The type tag of every slot, read back through `get`. A keyword reports
;; as `symbol`; a builtin, a user closure and a generator all report as
;; `lambda`, a generator being a closure like any other.
(defun mrm/all-types ()
  (map mrm/type-of-field
       '(:int :float :string :char :sym :kw :bool :none :cons :vec
         :fn :subr :gen :iter :cont :v2 :v3 :v4 :m2 :m3 :m4 :inner :self)))

;; The expected side is built rather than quoted, because `(type-of nil)`
;; is the SYMBOL `nil` and `nil` inside a quoted list reads as the nil
;; VALUE - the two are not `eq?`. `(intern "nil")` is that symbol.
(defun mrm/expected-types ()
  (list 'integer 'float 'string 'char 'symbol 'symbol 'bool (intern "nil")
        'cons 'vec 'lambda 'lambda 'lambda 'iter 'continuation
        'vec2 'vec3 'vec4 'mat2 'mat3 'mat4 'table 'table))

(test mrm-every-representation-is-allocated
      (eq? (mrm/expected-types) (mrm/all-types))
      ;; the same 23 slots the list walks, and nothing else: a slot cannot
      ;; be added to the structure without the two lists above growing too
      (= 23 (len (mrm/world)))
      (= 23 (len (collect (iter (mrm/all-types))))))

;; Reading each one back out and checking it is the value that went in,
;; not merely something of the right type. The heap string is built by
;; `concat` rather than written as a literal, so it is a fresh allocation
;; rather than a pointer into the constant pool.
(defun mrm/deep-leaf () (car (get (get (mrm/field :inner) :deep) 0)))

(test mrm-every-value-survives-the-round-trip
      (= 42 (mrm/field :int))
      (eq? "spaik" (mrm/field :string))
      (= (chr "s") (mrm/field :char))
      (eq? 'mrm-a-symbol (mrm/field :sym))
      (eq? :mrm-a-keyword (mrm/field :kw))
      (nil? (mrm/field :none))
      (eq? '(1 2 3) (mrm/field :cons))
      (eq? (vec :a :b :c) (mrm/field :vec))
      (= 6 ((mrm/field :fn) 3))
      (= 1 ((mrm/field :subr) (list 1 2)))
      (eq? :leaf (mrm/deep-leaf))
      ;; `get` indexes the fixed-width vectors too, and stops there: vec4
      ;; is not in its accepted list
      (= 1.0 (get (mrm/field :v2) 0))
      (= 3.0 (get (mrm/field :v3) 2))
      (mrm/catch 'type-error '(if (get (vec4 1 2 3 4) 0) 1 2)))

;;; ---[ identity, aliasing and cycles ]-------------------------------------

;; `eq?` is structural and has to terminate on a cycle rather than
;; recurse forever; `clone` answers a structurally equal object; and the
;; same object stored twice stays one object, not two.

(defun mrm/ring () (let ((v (vec 1 2))) (push v v) v))

(defun mrm/self-is-the-same-table ()
  (let ((tb (mrm/world))) (eq? tb (get tb :self))))

(defun mrm/self-two-deep ()
  (let ((tb (mrm/world))) (= 42 (get (get (get tb :self) :self) :int))))

;; One vec reachable through two keys: a write through either is visible
;; through the other, which is what makes it an alias and not a copy.
(defun mrm/alias-is-shared ()
  (let ((v (vec 1))
        (tb (make-table)))
    (set (get tb :a) v)
    (set (get tb :b) v)
    (push (get tb :a) 2)
    (list (get tb :b) (eq? (get tb :a) (get tb :b)))))

;; `clone` breaks the sharing: the copy is equal but writing to the
;; original does not reach it.
(defun mrm/clone-is-independent ()
  (let ((v (vec 1 2)))
    (let ((c (clone v)))
      (push v 3)
      (list c v))))

(test mrm-identity-and-cycles
      (mrm/self-is-the-same-table)
      (mrm/self-two-deep)
      (eq? (mrm/ring) (mrm/ring))
      (eq? (list (vec 1 2) true) (mrm/alias-is-shared))
      (eq? (list (vec 1 2) (vec 1 2 3)) (mrm/clone-is-independent))
      ;; two worlds are NOT equal: each holds a fresh continuation and a
      ;; fresh closure, and those compare by identity
      (not (eq? (mrm/world) (mrm/world))))

;;; ---[ writes into existing objects ]--------------------------------------

;; Every one of these stores a pointer into an object that already
;; exists, which is where a write barrier has to fire. The `gc` at the
;; end of each is the part that matters: a missed barrier shows up as the
;; freshly stored child being collected out from under its new parent.

(defun mrm/mutate ()
  (let ((tb (mrm/world)))
    (set (get tb :int) 43)
    (set (get (get tb :vec) 0) :z)
    (push (get tb :vec) :d)
    (del tb :float)
    (gc)
    (list (get tb :int)
          (get tb :vec)
          (pop (get tb :vec))
          (len tb)
          (nil? (get tb :float)))))

;; An old, already-traced vec receiving a brand-new compound, with
;; collection pressure on both sides of the write. The payload string is
;; reachable ONLY through the wrapper by the time the push happens.
(defun mrm/barrier-vpush (rounds)
  (let ((a (vec)) (holder nil) (wrapper nil) (bad 0))
    (range (r (0 rounds))
      (set holder (vec (concat "payload-" r)))
      (mrm/churn 120)
      (set wrapper (vec (get holder 0)))
      (set holder nil)
      (push a wrapper)
      (mrm/churn 120)
      (unless (eq? (get (get a r) 0) (concat "payload-" r))
        (inc! bad)))
    (list (len a) bad)))

;; The same write through a table key and through a global, which take
;; different paths in the VM.
(defvar mrm/global nil)

(defun mrm/barrier-table (rounds)
  (let ((tb (make-table)) (bad 0))
    (range (r (0 rounds))
      (mrm/churn 90)
      (set (get tb r) (vec (concat "k" r)))
      (mrm/churn 90)
      (unless (eq? (get (get tb r) 0) (concat "k" r)) (inc! bad)))
    (list (len tb) bad)))

(defun mrm/barrier-global (rounds)
  (let ((bad 0))
    (range (r (0 rounds))
      (set mrm/global (vec (concat "g" r) (list r r)))
      (mrm/churn 120)
      (unless (eq? (get mrm/global 1) (list r r)) (inc! bad)))
    bad))

(test mrm-writes-into-live-objects
      (eq? (list 43 (vec :z :b :c) :d 22 true) (mrm/mutate))
      (eq? '(20 0) (mrm/barrier-vpush 20))
      (eq? '(20 0) (mrm/barrier-table 20))
      (= 0 (mrm/barrier-global 20)))

;;; ---[ growth and reallocation ]-------------------------------------------

;; A vec that outgrows its backing store and a table that rehashes, both
;; with collections interleaved, then read back in full. This is the
;; path where the elements move.

(defun mrm/vec-grows (n)
  (let ((v (vec)) (bad 0))
    (range (i (0 n))
      (push v (list i))
      (when (= 0 (% i 16)) (gc)))
    (range (i (0 n))
      (unless (eq? (get v i) (list i)) (inc! bad)))
    (list (len v) bad)))

(defun mrm/table-rehashes (n)
  (let ((tb (make-table)) (bad 0))
    (range (i (0 n))
      (set (get tb i) (concat "v" i))
      (when (= 0 (% i 16)) (gc)))
    (range (i (0 n))
      (unless (eq? (get tb i) (concat "v" i)) (inc! bad)))
    (list (len tb) bad)))

;; Shrinking is the other half: popping a vec and deleting from a table
;; both leave the survivors intact across a collection.
(defun mrm/shrinks (n)
  (let ((v (vec)) (tb (make-table)))
    (range (i (0 n)) (push v (list i)) (set (get tb i) (list i)))
    (range (i (0 n))
      (when (= 0 (% i 2)) (del tb i)))
    (range (i (0 n))
      (when (> (len v) 8) (pop v)))
    (gc)
    (list (len v) (len tb) (get v 0))))

(test mrm-growth-and-rehash
      (eq? '(400 0) (mrm/vec-grows 400))
      (eq? '(320 0) (mrm/table-rehashes 320))
      (eq? (list 8 120 (list 0)) (mrm/shrinks 240)))

;;; ---[ deep and long structures ]------------------------------------------

;; Marking a long cons spine and a deep nest has to be iterative or
;; bounded; both are built, collected under, and then walked end to end.

(defun mrm/spine (n)
  (let ((xs nil))
    (range (i (0 n)) (set xs (cons i xs)))
    xs))

(defun mrm/spine-len (xs)
  (let ((n 0))
    (while xs (inc! n) (set xs (cdr xs)))
    n))

(defun mrm/deep-nest (n)
  (let ((x (vec :bottom)))
    (range (i (0 n)) (set x (vec x)))
    x))

(defun mrm/deep-depth (x)
  (let ((n 0))
    (while (vec? (get x 0))
      (inc! n)
      (set x (get x 0)))
    n))

(defun mrm/long-string (n)
  (let ((s ""))
    (range (i (0 n)) (set s (concat s "ab")))
    (len s)))

(test mrm-deep-and-long-structures
      (= 1600 (let ((xs (mrm/spine 1600))) (gc) (mrm/spine-len xs)))
      (= 300 (let ((x (mrm/deep-nest 300))) (gc) (mrm/deep-depth x)))
      (= 800 (mrm/long-string 400)))

;;; ---[ collection with the structure live ]--------------------------------

;; Held across a collection with unrelated garbage churning underneath:
;; the cycle, the nested table and the heap string all have to come back
;; intact, and the collector has to terminate in the presence of the
;; cycle rather than spin on it.

(defun mrm/world-across-gc ()
  (let ((tb (mrm/world)))
    (gc)
    (mrm/churn 900)
    (gc)
    (list (len tb)
          (get (get tb :self) :int)
          (get tb :string)
          (mrm/deep-leaf))))

;; Garbage that is itself cyclic, dropped and collected: the count is not
;; pinned, only that the collection returns at all.
(defun mrm/cyclic-garbage (n)
  (range (i (0 n))
    (let ((v (vec i)))
      (push v v)))
  (gc)
  n)

(test mrm-collection-with-live-structure
      (eq? (list 23 42 "spaik" :leaf) (mrm/world-across-gc))
      (= 240 (mrm/cyclic-garbage 240)))

;;; ---[ iterators are live cursors into the heap ]--------------------------

;; An iterator holds a position inside an object the collector may move.
;; These hold one open across a collection, and across mutation of the
;; sequence underneath it.

(defun mrm/iter-across-gc ()
  (let ((it (iter (mrm/spine 200))))
    (next it)
    (gc)
    (mrm/churn 600)
    (gc)
    (len (collect it))))

(defun mrm/iter-over-growing-vec (n)
  (let ((v (vec)) (seen 0) (x nil))
    (range (i (0 n)) (push v (list i)))
    (let ((it (iter v)))
      (loop
       (set x (next it))
       (if (iter-end? x) (break))
       (inc! seen)
       (when (= 0 (% seen 4))
         (push v (list (+ n seen)))
         (gc))))
    (list seen (len v))))

(defun mrm/iter-over-shrinking-table (n)
  (let ((tb (make-table)) (seen 0) (x nil))
    (range (i (0 n)) (set (get tb i) (vec i)))
    (let ((it (iter tb)))
      (loop
       (set x (next it))
       (if (iter-end? x) (break))
       (inc! seen)
       (when (= 0 (% seen 3)) (del tb x) (gc))))
    (list seen (len tb))))

;; The iterator built during construction, left untouched until after a
;; collection.
(defun mrm/structure-iter-across-gc ()
  (let ((tb (mrm/world)))
    (gc)
    (mrm/churn 480)
    (collect (get tb :iter))))

(test mrm-iterators-across-gc-and-mutation
      (= 199 (mrm/iter-across-gc))
      ;; the cursor DOES see elements appended behind it - 5 pushes, one
      ;; every fourth step, all of them visited - which is the opposite of
      ;; the table case below
      (eq? (list 106 106) (mrm/iter-over-growing-vec 80))
      (eq? (list 96 64) (mrm/iter-over-shrinking-table 96))
      (eq? (vec :i0 :i1) (mrm/structure-iter-across-gc)))

;;; ---[ continuations: saved and reinstated stacks ]------------------------

;; A continuation is a copy of a stack living on the heap. Capturing one,
;; collecting under it and then resuming it is the whole point of this
;; section; so is a throw, which unwinds without resuming.

(defvar mrm/k nil)

(defun mrm/callcc-reentry ()
  (let ((v (call/cc (lambda (k) (set mrm/k k) 1))))
    (when (= v 1)
      (mrm/churn 450)
      (gc)
      (mrm/resume 99))
    v))

(defun mrm/resume (v) (mrm/k v))

;; A resumed continuation reinstates the stack that was live when it was
;; CAPTURED, so it reaches the handlers that were live then - not one the
;; resuming code wrapped around the resume. `mrm/inner-ran` is the
;; witness: the resuming helper never gets to run its own tail.
(defvar mrm/ck nil)
(defvar mrm/inner-ran nil)

(defun mrm/capture ()
  (call/cc (lambda (kk) (set mrm/ck kk) (throw 'mrm-tag 1)))
  (throw 'mrm-other 2))

(defun mrm/step (kk)
  (let ((v (catch 'mrm-other (kk nil))))
    (set mrm/inner-ran true)
    v))

(defun mrm/drive ()
  (set mrm/inner-ran false)
  (catch 'mrm-other
    (let ((r (catch 'mrm-tag (mrm/capture))))
      (mrm/step mrm/ck))))

;; Unwinding past a `catch` must leave the value stack where it started,
;; so a throw out of a deep call and a throw out of an argument position
;; both have to balance. The sum afterwards is the witness.
(defun mrm/thrower (n) (if (> n 0) (mrm/thrower (- n 1)) (throw 'mrm-deep :bottom)))

(defun mrm/unwind-balance (rounds)
  (let ((acc (vec)))
    (range (r (0 rounds))
      (push acc (catch 'mrm-deep (mrm/thrower 12)))
      (push acc (catch 'mrm-deep (list :arg (mrm/thrower 5)))))
    (list (len acc) (get acc 0) (get acc 1))))

(test mrm-continuations-and-unwinding
      (= 99 (mrm/callcc-reentry))
      (= 2 (mrm/drive))
      (not (progn (mrm/drive) mrm/inner-ran))
      (eq? (list 96 :bottom :bottom) (mrm/unwind-balance 48))
      ;; a continuation captured and then only collected under, never
      ;; resumed, is still a `continuation` afterwards
      (eq? 'continuation (let ((tb (mrm/world))) (gc) (type-of (get tb :cont)))))

;;; ---[ generators: suspended stacks on the heap ]--------------------------

;; `(gen f)` answers a one-argument closure holding a continuation, a
;; table and the body closure. The FIRST call runs the body from the
;; start and discards its argument; every later call resumes it, and its
;; argument becomes the value of the yielder call that suspended it.
;; Running off the end throws `done` at the RESUME SITE carrying the
;; body's own return value, and keeps doing so for every later call.

(defvar mrm/seen nil)

(defun mrm/echo ()
  (gen (lambda (yi)
         (set mrm/seen (cons (yi :a) mrm/seen))
         (set mrm/seen (cons (yi :b) mrm/seen))
         :body-result)))

(defun mrm/echo-run ()
  (set mrm/seen nil)
  (let ((co (mrm/echo)))
    (let ((r1 (co :discarded))
          (r2 (co 20))
          (r3 (catch 'done (list :not-done (co 30)))))
      (list r1 r2 r3 mrm/seen))))

(defun mrm/past-the-end ()
  (let ((co (mrm/of '(1))))
    (list (co nil) (catch 'done (co nil)) (catch 'done (co nil)))))

;; A yielded value is not restricted to immediates - it travels as an
;; ordinary continuation argument - so a reference crosses the suspend.
(defun mrm/yields-references ()
  (mrm/drain (gen (lambda (yi)
                    (yi (list 1 2))
                    (yi (vec :v))
                    (yi (make-table :k 1))
                    (yi (concat "s" "t"))
                    (yi nil)))))

(test mrm-generator-protocol
      (eq? 'lambda (type-of (mrm/of '(1))))
      (eq? (list :a :b :body-result '(30 20)) (mrm/echo-run))
      (eq? '(1 :mrm-end :mrm-end) (mrm/past-the-end))
      (eq? (vec 1 2 3) (mrm/drain (mrm/of '(1 2 3))))
      (eq? (vec) (mrm/drain (mrm/of '())))
      (= 5 (len (mrm/yields-references)))
      (eq? (vec :v) (get (mrm/yields-references) 1))
      (eq? "st" (get (mrm/yields-references) 3))
      (nil? (get (mrm/yields-references) 4)))

;; Each generator owns its own saved stack: two from one constructor must
;; not share a resume point, one built per loop iteration closes over its
;; own copy of the index, and an infinite body is left suspended rather
;; than run to the end.
(defun mrm/two-independent ()
  (let ((a (mrm/of '(1 2 3))) (b (mrm/of '(1 2 3))))
    (a nil) (a nil)
    (list (a nil) (b nil))))

(defun mrm/naturals ()
  (gen (lambda (yi) (let ((i 0)) (loop (yi i) (inc! i))))))

(defun mrm/built-in-a-loop ()
  (let ((gs (vec)) (out (vec)))
    (range (i (0 3)) (push gs (gen (lambda (yi) (yi i)))))
    (dolist (g gs) (push out (g nil)))
    out))

;; A driver keeping its own counter across every resume. A raw
;; continuation would reinstate the driver's earlier frame and revert it;
;; `gen` refreshes its return continuation per call, so the count holds.
(defun mrm/counting-drain (co)
  (let ((seen 0) (out (vec)))
    (catch 'done (loop (push out (co nil)) (inc! seen)))
    (list seen out)))

;; Delegation: the inner `done` is caught INSIDE the outer body, which is
;; what `done` landing at the resume site buys.
(defun mrm/passthrough (inner)
  (gen (lambda (yi) (catch 'done (loop (yi (inner nil)))))))

(test mrm-generator-instances-are-independent
      (eq? '(3 1) (mrm/two-independent))
      (eq? (vec 0 1 2 3) (mrm/take (mrm/naturals) 4))
      (eq? (vec 0 1 2) (mrm/built-in-a-loop))
      (eq? (list 3 (vec :a :b :c)) (mrm/counting-drain (mrm/of '(:a :b :c))))
      (eq? (vec 1 2 3) (mrm/drain (mrm/passthrough (mrm/passthrough (mrm/of '(1 2 3)))))))

;; The body's dynamic extent is saved and restored whole, so a `catch`
;; opened before a yield is still in force after the resume. A plain
;; `throw` from the body unwinds the BODY's stack and reaches the catch
;; that was live when that stack was captured - the call that started the
;; generator - not one wrapped around the resume.
(defun mrm/catch-spans-a-yield ()
  (let ((co (gen (lambda (yi)
                   (yi (catch 'mrm-sp
                         (yi :first)
                         (throw 'mrm-sp :after-resume)
                         :never))
                   :end))))
    (list (co nil) (co :resume))))

(defun mrm/throws-on-resume ()
  (gen (lambda (yi) (yi 1) (throw 'mrm-t :from-body))))

(defun mrm/throw-lands-outside ()
  (let ((co (mrm/throws-on-resume)))
    (catch 'mrm-t
      (let ((a (co nil)))
        (list :inner a (catch 'mrm-t (list :got (co nil))))))))

;; Suspending inside `cond`, `case`, `dolist` and `range` - all of which
;; are built on `catch`/`throw` with gensym tags - and resuming into them
;; later must not disturb those tags.
(defun mrm/inside-control-flow ()
  (mrm/drain (gen (lambda (yi)
                    (dolist (x '(1 2))
                      (cond ((= 0 (% x 2)) (yi (list :even x)))
                            (true          (yi (list :odd x)))))
                    (case :a (:a (yi :ka)) (_ (yi :kz)))
                    (range (i (0 2)) (yi i))))))

(test mrm-generator-dynamic-extent
      (eq? '(:first :after-resume) (mrm/catch-spans-a-yield))
      (eq? :from-body (mrm/throw-lands-outside))
      (eq? (vec '(:odd 1) '(:even 2) :ka 0 1) (mrm/inside-control-flow)))

;;; ---[ generators under collection pressure ]------------------------------

;; A suspended generator is a live reference to a saved stack; nothing in
;; it may be collected while it is reachable, and everything in it must
;; be collected once it is not.

(defun mrm/survives-gc ()
  (let ((a (mrm/of '(1 2 3)))
        (b (mrm/of '(4 5 6))))
    (a nil) (b nil)
    (gc)
    (mrm/churn 600)
    (gc)
    (list (a nil) (b nil) (a nil) (b nil))))

;; Reachable only through a container, never from a local.
(defun mrm/gen-through-a-table ()
  (let ((tb (make-table :g (mrm/naturals))))
    ((get tb :g) nil)
    (gc)
    (mrm/churn 480)
    (list ((get tb :g) nil) ((get tb :g) nil))))

;; Many suspended at once, advanced in three passes, so every one of them
;; is holding a stack across the others' allocations.
(defun mrm/many-at-once (n)
  (let ((gs (vec)) (c (mrm/cell)))
    (range (i (0 n)) (push gs (gen (lambda (yi) (range (j (0 3)) (yi j))))))
    (dolist (g gs) (mrm/bump! c (g nil)))
    (gc)
    (dolist (g gs) (mrm/bump! c (g nil)))
    (dolist (g gs) (mrm/bump! c (g nil)))
    (get c 0)))

;; Generators dropped without ever being exhausted: their stacks are
;; garbage and have to go, which is the case a leak would show up in.
(defun mrm/abandoned (n)
  (range (i (0 n))
    (let ((co (mrm/naturals)))
      (co nil)
      (co nil)))
  (gc)
  n)

(test mrm-generators-under-collection-pressure
      (eq? '(2 5 3 6) (mrm/survives-gc))
      (eq? '(1 2) (mrm/gen-through-a-table))
      ;; 24 generators x (0 + 1 + 2)
      (= 360 (mrm/many-at-once 120))
      (= 200 (mrm/abandoned 200))
      ;; the generator built during construction, started only after a
      ;; collection has moved everything around it
      (eq? (vec 10 20) (let ((tb (mrm/world))) (gc) (mrm/drain (get tb :gen)))))

;;; ---[ allocation inside the collector's own reach ]-----------------------

;; Accumulators the VM holds internally - an argument list being built, a
;; rest parameter, a `catch` payload - are roots the collector has to know
;; about. Each of these allocates hard enough to collect midway through
;; building one.

(defun mrm/takes-rest (&rest r) (len r))

(defun mrm/rest-under-pressure (n)
  (let ((c (mrm/cell)))
    (range (i (0 n))
      (mrm/churn 60)
      (mrm/bump! c (mrm/takes-rest (vec i) (list i) (concat "r" i))))
    (get c 0)))

(defun mrm/payload-under-pressure (n)
  (let ((out (vec)))
    (range (i (0 n))
      (push out (catch 'mrm-pay (progn (mrm/churn 60) (throw 'mrm-pay (list :p i))))))
    (list (len out) (get out 0))))

(defun mrm/apply-under-pressure (n)
  (let ((c (mrm/cell)))
    (range (i (0 n))
      (mrm/churn 60)
      (mrm/bump! c (apply mrm/takes-rest (list (vec i) (list i)))))
    (get c 0)))

(defun mrm/eval-under-pressure (n)
  (let ((out (vec)))
    (range (i (0 n))
      (mrm/churn 60)
      (push out (eval '(list :e (vec 1 2)))))
    (list (len out) (get out 0))))

(test mrm-internal-accumulators-are-rooted
      (= 72 (mrm/rest-under-pressure 24))
      (eq? (list 24 (list :p 0)) (mrm/payload-under-pressure 24))
      (= 48 (mrm/apply-under-pressure 24))
      (eq? (list 24 (list :e (vec 1 2))) (mrm/eval-under-pressure 24)))

;;; ---[ strings and symbols are heap objects too ]--------------------------

;; Built rather than written as literals, so each is a fresh allocation,
;; and checked after a collection has had the chance to move them.

(defun mrm/string-churn (n)
  (let ((v (vec)) (bad 0))
    (range (i (0 n)) (push v (concat "s" i "-" (string (* i 2)))))
    (gc)
    (mrm/churn 360)
    (range (i (0 n))
      (unless (eq? (get v i) (concat "s" i "-" (string (* i 2)))) (inc! bad)))
    (list (len v) bad)))

(defun mrm/symbol-churn (n)
  (let ((v (vec)) (bad 0))
    (range (i (0 n)) (push v (intern (concat "mrm-sym-" i))))
    (gc)
    (range (i (0 n))
      (unless (eq? (get v i) (intern (concat "mrm-sym-" i))) (inc! bad)))
    (list (len v) bad)))

(test mrm-heap-strings-and-symbols
      (eq? '(120 0) (mrm/string-churn 120))
      (eq? '(120 0) (mrm/symbol-churn 120))
      (= 3 (len (concat "a" "b" "c")))
      (symbol? (gensym))
      (not (eq? (gensym) (gensym))))

;;; ---[ the in-place sequence mutators ]------------------------------------

;; `sort!`, `reverse!` and `split!` rewrite their argument where it lies
;; rather than building a new one, and `del`/`pop` shorten one. Each is
;; run on a sequence of heap objects rather than of immediates, so what
;; moves is pointers, and each is checked after a collection.

(defun mrm/boxes (n)
  (let ((v (vec)))
    (range (i (0 n)) (push v (- n i)))
    v))

(defun mrm/sort-in-place (n)
  (let ((v (mrm/boxes n)))
    (sort! v)
    (gc)
    (list (get v 0) (get v (- n 1)) (len v))))

(defun mrm/sort-leaves-alone ()
  (let ((v (vec 3 1 2)))
    (let ((s (sort v)))
      (gc)
      (list v s))))

(defun mrm/reverse-in-place (n)
  (let ((v (mrm/boxes n)))
    (reverse! v)
    (gc)
    (list (get v 0) (get v (- n 1)))))

(defun mrm/split-halves ()  (split! (mrm/spine 64)))
(defun mrm/split-truncates ()
  (let ((xs (mrm/spine 64)))
    (split! xs)
    (gc)
    (mrm/spine-len xs)))

(defun mrm/pop-to-empty (n)
  (let ((v (mrm/boxes n)) (last nil))
    (while (> (len v) 0) (set last (pop v)) )
    (gc)
    (list (len v) last (nil? (pop v)))))

(test mrm-in-place-sequence-mutators
      (eq? (list 1 80 80) (mrm/sort-in-place 80))
      (eq? (list (vec 3 1 2) (vec 1 2 3)) (mrm/sort-leaves-alone))
      (eq? (list 1 80) (mrm/reverse-in-place 80))
      ;; `split!` answers (first-half . second-half), so the car is the
      ;; first thirty-two cells and the cdr is the remaining thirty-two
      (= 32 (mrm/spine-len (car (mrm/split-halves))))
      (= 32 (mrm/spine-len (cdr (mrm/split-halves))))
      (= 32 (mrm/split-truncates))
      (eq? (list 0 48 true) (mrm/pop-to-empty 48))
      (eq? '(3 2 1) (reverse '(1 2 3)))
      (eq? (vec 1 2 3) (sort (vec 3 1 2))))

;;; ---[ walking the heap to build a value ]---------------------------------

;; `map`, `filter`, `zip` and `collect` each hold a half-built result
;; while calling back into the interpreter, which can collect underneath
;; them. Driven over heap elements, with churn in the callback.

(defun mrm/map-under-pressure (n)
  (map (lambda (x) (mrm/churn 30) (vec x)) (mrm/spine n)))

(defun mrm/filter-under-pressure (n)
  (filter (lambda (x) (mrm/churn 30) (= 0 (% x 2))) (mrm/spine n)))

(defun mrm/collect-shapes ()
  (list (collect (iter (list (vec 1) (vec 2))))
        (collect (iter (vec (list 1))))
        (collect (iter (concat "a" "b")))
        (collect (iter (make-table :k (vec 1))))
        (collect (iter nil))))

(test mrm-heap-walking-builders
      (= 60 (mrm/spine-len (mrm/map-under-pressure 60)))
      (eq? (vec 59) (car (mrm/map-under-pressure 60)))
      (= 30 (mrm/spine-len (mrm/filter-under-pressure 60)))
      (eq? (list (vec (vec 1) (vec 2))
                 (vec (list 1))
                 (vec (chr "a") (chr "b"))
                 (vec :k)
                 (vec))
           (mrm/collect-shapes))
      (eq? '((1 . 3) (2 . 4)) (zip (list 1 2) (list 3 4)))
      (= 6 (sum (vec 1 2 3)))
      (= 6 (apply + (list 1 2 3))))

;;; ---[ printing walks the live structure ]---------------------------------

;; The printer follows every pointer it is given, so it has to notice
;; shared structure and stop at a cycle rather than run off the end of
;; the heap. `string` on the cyclic world is the load-bearing line here.

(defun mrm/print-the-world () (len (string (mrm/world))))
(defun mrm/print-a-ring ()    (string (mrm/ring)))

(defun mrm/print-after-gc ()
  (let ((tb (mrm/world)))
    (gc)
    (mrm/churn 360)
    (> (len (string tb)) 0)))

(test mrm-printing-a-cyclic-structure-terminates
      (> (mrm/print-the-world) 0)
      (string? (mrm/print-a-ring))
      (mrm/print-after-gc)
      (eq? "(1 2)" (string (list 1 2)))
      (eq? "\"x\"" (repr (concat "" "x")))
      (eq? "(vec 1)" (repr (vec 1)))
      (string? (dbg-repr (vec 1 2)))
      (eq? "1 (vec 1)" (fmt "{} {}" 1 (vec 1))))

;;; ---[ the compiler allocates too ]----------------------------------------

;; `eval`, `macroexpand` and macro expansion in general build forms on
;; the same heap everything else lives on, and do it while the collector
;; is free to run.

(defmacro mrm/twice (x) `(list ,x ,x))
(defmacro mrm/splice (xs) `(list :head ,@xs))

(defun mrm/qq (x) `(a ,x ,@(list (vec 1) (vec 2))))

(defun mrm/expand-under-pressure (n)
  (let ((out (vec)))
    (range (i (0 n))
      (mrm/churn 45)
      (push out (macroexpand '(when (vec 1) (vec 2)))))
    (list (len out) (eq? (get out 0) (get out (- n 1))))))

(test mrm-compiler-allocations
      (eq? (list (vec 1) (vec 1)) (mrm/twice (vec 1)))
      (eq? '(:head 1 2) (mrm/splice (1 2)))
      (eq? (list 'a 5 (vec 1) (vec 2)) (mrm/qq 5))
      (eq? '(24 true) (mrm/expand-under-pressure 24))
      (eq? (vec 1 2) (eval '(vec 1 2))))

;;; ---[ the fixed-width vectors and matrices ]------------------------------

;; These are stored unboxed and read back through the same `get` as a
;; vec, so the indexing path is a different one from everything above.
;; Built into a vec, collected under, then read back.

(defun mrm/linalg-across-gc (n)
  (let ((v (vec)) (bad 0))
    (range (i (0 n))
      (push v (mat (vec3 i 0 0) (vec3 0 i 0) (vec3 0 0 1))))
    (gc)
    (mrm/churn 360)
    (range (i (0 n))
      (unless (eq? (get v i) (mat (vec3 i 0 0) (vec3 0 i 0) (vec3 0 0 1)))
        (inc! bad)))
    (list (len v) bad)))

(test mrm-fixed-width-values
      (eq? '(96 0) (mrm/linalg-across-gc 96))
      (eq? 'mat3 (type-of (scale (vec2 2 3))))
      (eq? 'mat4 (type-of (translate (vec3 5 6 7))))
      (eq? 'mat2 (type-of (mat2-rot 0)))
      (eq? 'mat4 (type-of (mat4-rot-x 0)))
      (eq? (mat (vec3 1 0 0) (vec3 0 1 0) (vec3 5 6 1)) (translate (vec2 5 6)))
      (eq? "(mat2 (1 2) (3 4))" (string (mat (vec2 1 2) (vec2 3 4))))
      ;; `len` on a fixed-width vector is its MAGNITUDE, not a count
      (= 5.0 (len (vec2 3 4))))

;;; ---[ table keys ]--------------------------------------------------------

;; Keys are immediate-only: an integer, symbol, keyword, char or bool
;; hashes. A reference key is refused with `Reference types cannot be
;; used as keys`, which is NOT an in-language error and is not catchable
;; under any tag even inside `eval` - so it cannot be asserted here
;; without ending the run, and only the accepted keys are exercised.

(defun mrm/keys-of-every-immediate ()
  (let ((tb (make-table)))
    (set (get tb 7) (vec :i))
    (set (get tb 'mrm-sym) (vec :s))
    (set (get tb :kw) (vec :k))
    (set (get tb (chr "c")) (vec :c))
    (set (get tb true) (vec :b))
    (gc)
    (list (len tb)
          (get tb 7) (get tb 'mrm-sym) (get tb :kw)
          (get tb (chr "c")) (get tb true))))

(defun mrm/missing-key-is-nil ()
  (let ((tb (make-table :a 1)))
    (list (nil? (get tb :zz)) (nil? (del tb :zz)) (len tb))))

(test mrm-table-keys
      (eq? (list 5 (vec :i) (vec :s) (vec :k) (vec :c) (vec :b))
           (mrm/keys-of-every-immediate))
      (eq? '(true true 1) (mrm/missing-key-is-nil)))

;;; ---[ closures hold heap values ]-----------------------------------------

;; A closure's captured environment is another object the collector has
;; to trace. These capture compounds, survive a collection, and are
;; reached only through a container.

(defun mrm/make-reader (v) (lambda () (get v 0)))

(defun mrm/closures-across-gc (n)
  (let ((fs (vec)) (bad 0))
    (range (i (0 n)) (push fs (mrm/make-reader (vec (list i)))))
    (gc)
    (mrm/churn 480)
    (gc)
    (range (i (0 n))
      (unless (eq? ((get fs i)) (list i)) (inc! bad)))
    (list (len fs) bad)))

;; Closures stored in a table, calling each other, with the intermediate
;; results kept only in another closure's environment.
(defun mrm/closure-in-a-table ()
  (let ((tb (make-table)))
    (set (get tb :f) (mrm/make-reader (vec (concat "in" "side"))))
    (gc)
    (mrm/churn 360)
    ((get tb :f))))

;; A closure capturing a generator, and a generator whose body captures a
;; closure: both directions of the same reference.
(defun mrm/closure-over-a-generator ()
  (let ((co (mrm/of '(1 2 3))))
    (let ((step (lambda () (co nil))))
      (step)
      (gc)
      (list (step) (step)))))

(defun mrm/generator-over-a-closure ()
  (let ((f (mrm/make-reader (vec :captured))))
    (mrm/drain (gen (lambda (yi) (yi (f)) (gc) (yi (f)))))))

(test mrm-closures-hold-heap-values
      (eq? '(80 0) (mrm/closures-across-gc 80))
      (eq? "inside" (mrm/closure-in-a-table))
      (eq? '(2 3) (mrm/closure-over-a-generator))
      (eq? (vec :captured :captured) (mrm/generator-over-a-closure)))

;;; ---[ reference payloads through an unwind ]------------------------------

;; Outside an `eval` boundary a `throw` may carry a reference, so the
;; unwind moves a heap pointer past frames that are being torn down. Done
;; repeatedly with allocation on both sides, and once out of a generator
;; body, where the stack being unwound is a saved one.

(defun mrm/throw-a-vec (i)
  (catch 'mrm-ref (progn (mrm/churn 60) (throw 'mrm-ref (vec i (list i))))))

(defun mrm/ref-payloads (n)
  (let ((out (vec)))
    (range (i (0 n)) (push out (mrm/throw-a-vec i)))
    (gc)
    (list (len out) (get out 0) (get out (- n 1)))))

(defun mrm/throw-from-a-body ()
  (let ((co (gen (lambda (yi) (yi 1) (throw 'mrm-ref (vec :from-body))))))
    (catch 'mrm-ref
      (let ((a (co nil)))
        (co nil)))))

(test mrm-reference-payloads-survive-an-unwind
      (eq? (list 40 (vec 0 (list 0)) (vec 39 (list 39))) (mrm/ref-payloads 40))
      (eq? (vec :from-body) (mrm/throw-from-a-body)))

;;; ---[ source text becomes code on the same heap ]-------------------------

;; `read-compile` turns a string into a code object and runs it. The
;; string is built rather than written as a literal, and there is churn
;; between the rounds, so the compiler is allocating into a heap that is
;; actively being collected.

(defun mrm/compile-a-string (i)
  (read-compile (concat "(list " (string i) " (vec " (string i) "))")))

(defun mrm/compile-under-pressure (n)
  (let ((out (vec)) (bad 0))
    (range (i (0 n))
      (mrm/churn 60)
      (push out (mrm/compile-a-string i)))
    (gc)
    (range (i (0 n))
      (unless (eq? (get out i) (list i (vec i))) (inc! bad)))
    (list (len out) bad)))

(test mrm-compiling-from-a-string
      (eq? '(32 0) (mrm/compile-under-pressure 32))
      (= 3 (read-compile "(+ 1 2)")))

;;; ---[ calling through every callable representation ]---------------------

;; A subr, a closure, a generator and a continuation are all reached by
;; the same call path. `apply` goes through it with a heap-built argument
;; list, which is the version that allocates.

(defun mrm/apply-a-generator ()
  (let ((co (mrm/of '(:x :y))))
    (list (apply co (list nil)) (apply co (list nil)))))

;; `list` and `vec` are not first-class functions, so `apply` needs a
;; named wrapper to build a pair through.
(defun mrm/pair (a b) (list a b))

(defun mrm/apply-building-a-pair (n)
  (let ((out (vec)))
    (range (i (0 n))
      (mrm/churn 60)
      (push out (apply mrm/pair (list (vec i) (concat "a" i)))))
    (list (len out) (get out 0))))

(test mrm-calling-through-every-callable
      (eq? '(:x :y) (mrm/apply-a-generator))
      (eq? (list 40 (list (vec 0) "a0")) (mrm/apply-building-a-pair 40))
      (= 1 (apply car (list (list 1 2))))
      (= 6 (apply (lambda (a b) (* a b)) (list 2 3)))
      ;; a continuation called with the value it should answer with
      (= 7 (call/cc (lambda (k) (apply k (list 7))))))

;;; ---[ catch around eval, in every shape ]---------------------------------

;; `(catch tag (eval form))` is the shape that runs the compiler, the VM
;; and the unwinder against each other inside one expression, so it gets
;; its own section rather than being used only as a helper. `catch`
;; outside, `eval` inside, `eval` in tail position throughout.

;; A form in statement position is compiled away, so the error never
;; happens; the suspect call has to sit where its value is USED.
(defun mrm/eval-builds (form) (eval form))

(test mrm-eval-builds-every-container
      (eq? (vec 1 2) (mrm/eval-builds '(vec 1 2)))
      (eq? '(1 2) (mrm/eval-builds '(list 1 2)))
      (table? (mrm/eval-builds '(make-table :a (vec 1))))
      (eq? (vec (list 1) (vec 2)) (mrm/eval-builds '(vec (list 1) (vec 2))))
      (eq? "ab" (mrm/eval-builds '(concat "a" "b")))
      (eq? 'lambda (type-of (mrm/eval-builds '(lambda (x) x))))
      (eq? 'lambda (type-of (mrm/eval-builds '(gen (lambda (yi) (yi 1))))))
      (eq? 'continuation (mrm/eval-builds '(call/cc type-of))))

;; A raise from the first argument position, from a later one, and from
;; inside a nested call all unwind to the same outer `catch`. Nothing
;; between the raise and the catch may run - the marker would show up in
;; the answer if it did.
(defun mrm/raise-first ()  (mrm/catch 'type-error '(if (car 5) :then :else)))
(defun mrm/raise-later ()  (mrm/catch 'type-error '(if (list (vec 1) (car 5)) :then :else)))
(defun mrm/raise-nested () (mrm/catch 'type-error '(if (car (car (car 5))) :then :else)))

;; A `catch` written INSIDE the evaluated form is a real recovery point:
;; the rest of that form runs and `eval` answers its value.
(defun mrm/recovers-inside ()
  (eval '(list :ok (catch 'mrm-ev (throw 'mrm-ev (vec 1))) :after)))

;; Nested evals, each with its own catch, unwinding through both.
(defun mrm/nested-eval ()
  (catch 'mrm-outer
    (eval '(list :a (catch 'mrm-inner (eval '(throw 'mrm-inner 1)))))))

(defun mrm/nested-eval-escapes ()
  (catch 'mrm-outer
    (eval '(list :a (catch 'mrm-inner (eval '(throw 'mrm-outer 2)))))))

(test mrm-catch-around-eval
      (string? (mrm/raise-first))
      (string? (mrm/raise-later))
      (string? (mrm/raise-nested))
      (eq? (list :ok (vec 1) :after) (mrm/recovers-inside))
      (eq? '(:a 1) (mrm/nested-eval))
      (= 2 (mrm/nested-eval-escapes))
      ;; the tag has to match: an unmatched throw passes straight through
      ;; the inner catch to the outer one
      (eq? :got (catch 'mrm-a (eval '(catch 'mrm-b (throw 'mrm-a :got))))))

;; Every immediate kind as a payload across the boundary. A REFERENCE is
;; refused there by design - even with the matching catch right outside -
;; and that refusal ends the run, so it is described rather than asserted.
(defun mrm/crosses (form) (catch 'mrm-x (eval form)))

(test mrm-eval-boundary-carries-immediates
      (= 3 (mrm/crosses '(throw 'mrm-x 3)))
      (eq? :k (mrm/crosses '(throw 'mrm-x :k)))
      (eq? 'sym (mrm/crosses '(throw 'mrm-x 'sym)))
      (nil? (mrm/crosses '(throw 'mrm-x nil)))
      (eq? true (mrm/crosses '(throw 'mrm-x true)))
      ;; the interpreter's own errors are exempt: one arrives as a
      ;; message string, which is a reference, when caught by its own tag
      (string? (mrm/catch 'type-error '(if (car 5) 1 2))))

;; The same thing repeatedly, with the compiler allocating into a heap
;; that is being collected, and with the payload built inside the form.
(defun mrm/eval-catch-under-pressure (n)
  (let ((out (vec)))
    (range (i (0 n))
      (mrm/churn 60)
      (push out (catch 'mrm-p (list :v (eval '(vec 1 2))))))
    (list (len out) (get out 0) (eq? (get out 0) (get out (- n 1))))))

;; An `eval` inside a generator body: the compiler runs on a stack that
;; is about to be saved, and the value it produces has to survive the
;; suspend.
(defun mrm/eval-inside-a-generator ()
  (mrm/drain (gen (lambda (yi)
                    (yi (eval '(vec :a)))
                    (gc)
                    (yi (catch 'mrm-g (eval '(throw 'mrm-g :thrown))))
                    (yi (eval '(list 1 2)))))))

;; An `eval` under a continuation capture, resumed afterwards.
(defvar mrm/ek nil)

(defun mrm/eval-then-resume ()
  (let ((v (call/cc (lambda (k) (set mrm/ek k) (eval '(vec :first))))))
    (if (vec? v)
        (progn (gc) (mrm/ek :second))
      v)))

(test mrm-eval-under-collection-pressure
      (eq? (list 24 (list :v (vec 1 2)) true) (mrm/eval-catch-under-pressure 24))
      (eq? (vec (vec :a) :thrown '(1 2)) (mrm/eval-inside-a-generator))
      (eq? :second (mrm/eval-then-resume)))

;;; ---[ vectors and tables, every accessor, under pressure ]----------------

;; One pass over the whole vec and table surface with heap elements and a
;; collection in the middle, so each accessor is exercised against an
;; object that has been moved since it was built.

(defun mrm/vec-surface (n)
  (let ((v (vec)))
    (range (i (0 n)) (push v (list i)))
    (gc)
    (let ((first (get v 0))
          (last (get v (- n 1)))
          (size (len v)))
      (set (get v 0) (vec :replaced))
      (mrm/churn 120)
      ;; `elem?` compares references by IDENTITY, so the element itself
      ;; is found and an equal-but-distinct cons is not
      (list size first last (get v 0) (pop v) (len v) (vec? v)
            (elem? (get v 1) v)
            (elem? (list 1) v)))))

(defun mrm/table-surface (n)
  (let ((tb (make-table)))
    (range (i (0 n)) (set (get tb i) (list i)))
    (gc)
    (let ((size (len tb))
          (mid (get tb (/ n 2))))
      (del tb 0)
      (mrm/churn 120)
      (list size mid (len tb) (nil? (get tb 0)) (table? tb)
            (len (collect (iter tb)))))))

(test mrm-vec-and-table-surface
      (eq? (list 32 (list 0) (list 31) (vec :replaced) (list 31) 31 true true nil)
           (mrm/vec-surface 32))
      (eq? (list 32 (list 16) 31 true true 31) (mrm/table-surface 32)))
