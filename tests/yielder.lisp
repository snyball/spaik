;;; The `gen` generator protocol: suspend, resume, exhaust, and nest.
;;; Also pins WHERE each throw lands - `done` at the resume site, a
;;; throw from the body at the site that started it.

;;; ---[ the driver helpers every section below uses ]-----------------------

;; Runs a generator to exhaustion and answers everything it yielded.
;; `done` is thrown at the call site of the exhausting call, so one
;; `catch` around the loop is enough.
(defun yld/drain (co)
  (let ((out (vec)))
    (catch 'done
      (loop (push out (co nil))))
    out))

;; Takes exactly n values, leaving the generator suspended. Safe on an
;; infinite generator, and never reaches `done` if n is in range.
(defun yld/take (co n)
  (let ((out (vec)))
    (while (> n 0)
      (push out (co nil))
      (set n (- n 1)))
    out))

;; The workhorse constructor: yield each element of a sequence.
(defun yld/of (xs)
  (gen (lambda (yi)
         (dolist (x xs) (yi x)))))

;;; ---[ the introductory example ]------------------------------------------

;; Three yields off a captured argument, driven by a caller that does not
;; know how many there are: the extra calls fall out through `done`.

(defun yld/my-gen (x)
  (gen
   (lambda (yi)
     (yi (+ x 1))
     (yi (+ x 2))
     (yi (+ x 3)))))

(defun yld/my-gen-run ()
  (let ((co (yld/my-gen 3))
        (count 0))
    (catch 'done
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1)))
      (set count (+ count (co 1))))
    count))

(test generators
      ;; 4 + 5 + 6; the fourth call throws `done` and abandons the rest
      (= (yld/my-gen-run) 15))

;;; ---[ the shape of the protocol ]-----------------------------------------

;; `(gen f)` answers a one-argument closure. The FIRST call runs `f` from
;; the start and its argument is discarded - there is no yielder call
;; waiting to receive it yet. Every later call resumes the body, and its
;; argument becomes the value of the yielder call that suspended it.

(defvar yld/seen nil)

(defun yld/echo ()
  (gen (lambda (yi)
         (set yld/seen (cons (yi :a) yld/seen))
         (set yld/seen (cons (yi :b) yld/seen))
         :body-result)))

(defun yld/echo-run ()
  (set yld/seen nil)
  (let ((co (yld/echo)))
    (let ((r1 (co :discarded))
          (r2 (co 20))
          (r3 (catch 'done (list :not-done (co 30)))))
      (list r1 r2 r3 yld/seen))))

(defun yld/echo-yields ()   (car (yld/echo-run)))
(defun yld/echo-yields-2 () (car (cdr (yld/echo-run))))
(defun yld/echo-done ()     (car (cddr (yld/echo-run))))
(defun yld/echo-received () (car (cdddr (yld/echo-run))))

(defun yld/type-of-a-generator () (type-of (yld/of '(1))))

(test yld-protocol-shape
      ;; a generator is just a closure
      (eq? 'lambda (yld/type-of-a-generator))
      ;; the call answers what the body yielded
      (eq? :a (yld/echo-yields))
      (eq? :b (yld/echo-yields-2))
      ;; the resume value arrives at the yielder call, newest first, and
      ;; the first call's argument is nowhere in that list
      (eq? '(30 20) (yld/echo-received))
      ;; exhaustion throws `done` carrying the body's OWN return value, so
      ;; a generator can return something: `:body-result` arrives at the
      ;; call that ran off the end, in place of a yielded value.
      (eq? :body-result (yld/echo-done)))

;;; ---[ draining, and the degenerate bodies ]-------------------------------

(defun yld/drain-list ()  (yld/drain (yld/of '(1 2 3))))
(defun yld/drain-empty () (yld/drain (yld/of '())))
(defun yld/drain-one ()   (yld/drain (yld/of '(:a))))

;; A body that never yields at all: the first call already exhausts it,
;; and `:nothing` is what that call's `done` carries.
(defun yld/drain-silent () (yld/drain (gen (lambda (yi) :nothing))))
(defun yld/silent-final () (catch 'done ((gen (lambda (yi) :nothing)) nil)))

(test yld-drain
      (eq? (vec 1 2 3) (yld/drain-list))
      (eq? (vec) (yld/drain-empty))
      (eq? (vec :a) (yld/drain-one))
      (eq? (vec) (yld/drain-silent))
      (eq? :nothing (yld/silent-final)))

;;; ---[ each generator has its own state ]----------------------------------

;; Two closures from one constructor must not share a resume point, and
;; must be drivable in any order.

(defun yld/two-independent ()
  (let ((a (yld/of '(1 2 3)))
        (b (yld/of '(1 2 3))))
    (a nil)
    (a nil)
    (list (a nil) (b nil))))

(defun yld/interleave-two ()
  (let ((a (yld/of '(1 2 3)))
        (b (yld/of '(10 20 30)))
        (out (vec)))
    (range (i (0 3))
      (push out (a nil))
      (push out (b nil)))
    out))

;; Generators held in a vec and in a table stay drivable from there.
(defun yld/from-a-vec ()
  (let ((v (vec)))
    (push v (yld/of '(1 2)))
    (push v (yld/of '(:a :b)))
    (list (yld/drain (get v 0)) (yld/drain (get v 1)))))

(defun yld/from-a-table ()
  (let ((tb (make-table :g (yld/of '("x" "y")))))
    (yld/drain (get tb :g))))

;; Each generator built in a loop closes over its own copy of the index.
(defun yld/built-in-a-loop ()
  (let ((gs (vec))
        (out (vec)))
    (range (i (0 3))
      (push gs (gen (lambda (yi) (yi i) (yi (* i 10))))))
    (dolist (g gs)
      (push out (g nil))
      (push out (g nil)))
    out))

(test yld-instances-are-independent
      (eq? '(3 1) (yld/two-independent))
      (eq? (vec 1 10 2 20 3 30) (yld/interleave-two))
      (eq? (list (vec 1 2) (vec :a :b)) (yld/from-a-vec))
      (eq? (vec "x" "y") (yld/from-a-table))
      (eq? (vec 0 0 1 10 2 20) (yld/built-in-a-loop)))

;;; ---[ infinite generators ]-----------------------------------------------

;; The point of the construct: a body whose loop never terminates, which
;; the caller stops by simply not calling again.

(defun yld/naturals ()
  (gen (lambda (yi)
         (let ((i 0))
           (loop (yi i) (set i (+ i 1)))))))

(defun yld/fibs ()
  (gen (lambda (yi)
         (let ((a 0) (b 1))
           (loop (yi a)
                 (let ((n (+ a b)))
                   (set a b)
                   (set b n)))))))

(defun yld/cycle (xs)
  (gen (lambda (yi)
         (loop (dolist (x xs) (yi x))))))

(defun yld/take-5-naturals () (yld/take (yld/naturals) 5))
(defun yld/take-8-fibs ()     (yld/take (yld/fibs) 8))
(defun yld/take-7-cycle ()    (yld/take (yld/cycle '(:a :b :c)) 7))

;; Two infinite generators suspended at once do not disturb each other.
(defun yld/two-infinite ()
  (let ((a (yld/naturals))
        (b (yld/fibs))
        (out (vec)))
    (range (i (0 4))
      (push out (a nil))
      (push out (b nil)))
    out))

(test yld-infinite-generators
      (eq? (vec 0 1 2 3 4) (yld/take-5-naturals))
      (eq? (vec 0 1 1 2 3 5 8 13) (yld/take-8-fibs))
      (eq? (vec :a :b :c :a :b :c :a) (yld/take-7-cycle))
      (eq? (vec 0 0 1 1 2 1 3 2) (yld/two-infinite)))

;;; ---[ resuming with a value: two-way generators ]-------------------------

;; The yielder call answers whatever the next driver call passed, so a
;; generator can consume as well as produce.

(defun yld/adder ()
  (gen (lambda (yi)
         (let ((total 0))
           (loop (set total (+ total (yi total))))))))

(defun yld/adder-run ()
  (let ((co (yld/adder)))
    (list (co nil) (co 5) (co 7) (co 100))))

;; A generator that echoes back what it is sent, one step behind.
(defun yld/mirror ()
  (gen (lambda (yi)
         (let ((last :initial))
           (loop (set last (yi last)))))))

(defun yld/mirror-run ()
  (let ((co (yld/mirror)))
    (list (co nil) (co :one) (co :two))))

(test yld-two-way
      ;; the running total is yielded before the next addend arrives
      (eq? '(0 5 12 112) (yld/adder-run))
      (eq? '(:initial :one :two) (yld/mirror-run)))

;;; ---[ the yielder is an ordinary value inside the body ]------------------

;; Nothing requires the yielder call to be lexically inside the generator
;; body: it can be passed to a helper, to a recursive function, or to a
;; higher-order builtin.

;; A helper taking the yielder as its first argument.
(defun yld/emit-pair (yi x)
  (yi (list :k x))
  (yi (list :v (* x 2))))

(defun yld/via-helper (xs)
  (gen (lambda (yi)
         (dolist (x xs) (yld/emit-pair yi x)))))

;; Recursion: an in-order walk of (left value right) triples.
(defun yld/walk (yi tree)
  (when tree
    (yld/walk yi (car tree))
    (yi (cadr tree))
    (yld/walk yi (caddr tree))))

(defun yld/tree (tree)
  (gen (lambda (yi) (yld/walk yi tree))))

(defun yld/walk-run ()
  (yld/drain (yld/tree '((nil 1 nil) 2 ((nil 3 nil) 4 nil)))))

;; Handed straight to `map` and reached through `apply`.
(defun yld/via-map (xs)   (gen (lambda (yi) (map yi xs))))
(defun yld/via-apply ()   (gen (lambda (yi) (apply yi (list :x)) (apply yi (list :y)))))

(test yld-yielder-is-first-class
      (eq? (vec '(:k 1) '(:v 2) '(:k 5) '(:v 10))
           (yld/drain (yld/via-helper '(1 5))))
      (eq? (vec 1 2 3 4) (yld/walk-run))
      (eq? (vec 1 2 3) (yld/drain (yld/via-map '(1 2 3))))
      (eq? (vec :x :y) (yld/drain (yld/via-apply))))

;;; ---[ yielding out of the control-flow macros ]---------------------------

;; `cond`, `case` and `dolist` are built on `catch`/`throw` with gensym
;; tags. Suspending in the middle of one and resuming into it later must
;; not disturb those tags.

(defun yld/cond-body (xs)
  (gen (lambda (yi)
         (dolist (x xs)
           (cond ((= 0 (% x 2)) (yi (list :even x)))
                 (true          (yi (list :odd x))))))))

(defun yld/case-body (xs)
  (gen (lambda (yi)
         (dolist (x xs)
           (case x
             (:a (yi 1))
             (:b (yi 2))
             (_  (yi 0)))))))

(defun yld/while-body (n)
  (gen (lambda (yi)
         (let ((i 0))
           (while (< i n)
             (when (> i 0) (yi i))
             (set i (+ i 1)))))))

(defun yld/nested-loops ()
  (gen (lambda (yi)
         (range (i (0 3))
           (range (j (0 2))
             (yi (list i j)))))))

(test yld-yield-inside-control-flow
      (eq? (vec '(:odd 1) '(:even 2) '(:odd 3))
           (yld/drain (yld/cond-body '(1 2 3))))
      (eq? (vec 1 2 0) (yld/drain (yld/case-body '(:a :b :z))))
      (eq? (vec 1 2 3) (yld/drain (yld/while-body 4)))
      (eq? (vec '(0 0) '(0 1) '(1 0) '(1 1) '(2 0) '(2 1))
           (yld/drain (yld/nested-loops))))

;;; ---[ generators driving generators ]-------------------------------------

;; Delegation: the outer body drains inner generators and re-yields. The
;; inner `done` is caught inside the outer body, which is the whole point
;; of `done` landing at the call site rather than at the capture site.

(defun yld/chain (xs ys)
  (gen (lambda (yi)
         (let ((a (yld/of xs)))
           (catch 'done (loop (yi (a nil)))))
         (let ((b (yld/of ys)))
           (catch 'done (loop (yi (b nil))))))))

(defun yld/zip-gens (xs ys)
  (gen (lambda (yi)
         (let ((a (yld/of xs))
               (b (yld/of ys)))
           (catch 'done
             (loop (yi (a nil))
                   (yi (b nil))))))))

;; A generator whose yielded values are themselves generators.
(defun yld/gen-of-gens ()
  (gen (lambda (yi)
         (yi (yld/of '(1 2)))
         (yi (yld/of '(:a :b))))))

(defun yld/gen-of-gens-run ()
  (let ((outer (yld/gen-of-gens)))
    (let ((g1 (outer nil))
          (g2 (outer nil)))
      (list (yld/drain g1) (yld/drain g2)))))

;; Three levels: a generator over a generator over a generator.
(defun yld/passthrough (inner)
  (gen (lambda (yi)
         (catch 'done (loop (yi (inner nil)))))))

(defun yld/three-deep ()
  (yld/drain (yld/passthrough (yld/passthrough (yld/of '(1 2 3))))))

(test yld-nested-generators
      (eq? (vec 1 2 3 4) (yld/drain (yld/chain '(1 2) '(3 4))))
      (eq? (vec 1 :a 2 :b 3 :c) (yld/drain (yld/zip-gens '(1 2 3) '(:a :b :c))))
      ;; the shorter side stops the interleave
      (eq? (vec 1 :a 2 :b) (yld/drain (yld/zip-gens '(1 2) '(:a :b :c :d))))
      (eq? (list (vec 1 2) (vec :a :b)) (yld/gen-of-gens-run))
      (eq? (vec 1 2 3) (yld/three-deep)))

;;; ---[ where a throw out of a generator lands ]----------------------------

;; This is the part the reworked semantics changed, and the two cases go
;; opposite ways.
;;
;; A plain `(throw tag v)` from the body unwinds the body's OWN stack, so
;; it reaches whichever catch was live when that stack was captured - the
;; call that started the generator - and not a catch wrapped around the
;; resume that happened to trigger it.
;;
;; `done` is different: `gen` raises it with the three-argument
;; `(throw k tag v)` against the continuation of the CURRENT call, so it
;; is delivered at the resume site like an ordinary return would be.

;; Same tag on both catches, so only the landing site can tell them apart.
(defun yld/throws-on-resume ()
  (gen (lambda (yi)
         (yi 1)
         (throw 'yld-t :from-body))))

(defun yld/throw-lands-outside ()
  (let ((co (yld/throws-on-resume)))
    (catch 'yld-t                                   ; live at the first call
      (let ((a (co nil)))
        (list :inner a
              (catch 'yld-t                         ; live only at the resume
                (list :got (co nil))))))))

(defun yld/done-lands-inside ()
  (let ((co (yld/of '(1))))
    (catch 'done                                    ; live at the first call
      (let ((a (co nil)))
        (list :inner a
              (catch 'done                          ; live only at the resume
                (list :got (co nil))))))))

;; On the FIRST call the body runs on the caller's own stack, so a throw
;; from it behaves like a throw from any ordinary function call.
(defun yld/throws-immediately ()
  (gen (lambda (yi)
         (throw 'yld-t :immediate)
         (yi 1))))

(defun yld/throw-on-first-call ()
  (let ((co (yld/throws-immediately)))
    (catch 'yld-t (list :no (co nil)))))

(test yld-where-a-throw-lands
      ;; the INNER catch never sees it - the whole form answers the payload
      (eq? :from-body (yld/throw-lands-outside))
      ;; whereas `done` is caught by the inner one, and carries nil
      (eq? '(:inner 1 nil) (yld/done-lands-inside))
      (eq? :immediate (yld/throw-on-first-call)))

;;; ---[ a catch inside the body survives suspension ]-----------------------

;; The body's dynamic extent is saved and restored whole, so a `catch`
;; opened before a yield is still in force after the resume.

(defun yld/catch-spans-a-yield ()
  (gen (lambda (yi)
         (yi (catch 'yld-sp
               (yi :first)
               (throw 'yld-sp :thrown-after-resume)
               :never))
         :end)))

(defun yld/spanning-run ()
  (let ((co (yld/catch-spans-a-yield)))
    (list (co nil) (co :resume))))

;; And a catch that opens and closes between two yields is ordinary.
(defun yld/catch-between-yields ()
  (gen (lambda (yi)
         (yi (catch 'yld-ic (throw 'yld-ic :caught)))
         (yi :second))))

(defun yld/between-run ()
  (let ((co (yld/catch-between-yields)))
    (list (co nil) (co nil))))

(test yld-body-dynamic-extent-survives
      (eq? '(:first :thrown-after-resume) (yld/spanning-run))
      (eq? '(:caught :second) (yld/between-run)))

;;; ---[ what a generator may yield ]----------------------------------------

;; Unlike an `error` payload, a yielded value is not restricted to
;; immediates: the value travels as an ordinary continuation argument.

(defun yld/mixed ()
  (gen (lambda (yi)
         (yi 1)
         (yi "a string")
         (yi (list 1 2))
         (yi (vec :v))
         (yi (make-table :k 1))
         (yi nil)
         (yi :kw))))

(defun yld/mixed-values () (yld/drain (yld/mixed)))
(defun yld/mixed-count ()  (len (yld/mixed-values)))
(defun yld/mixed-nth (i)   (get (yld/mixed-values) i))

(test yld-yielded-values-are-unrestricted
      (= 7 (yld/mixed-count))
      (= 1 (yld/mixed-nth 0))
      (eq? "a string" (yld/mixed-nth 1))
      (eq? '(1 2) (yld/mixed-nth 2))
      (eq? (vec :v) (yld/mixed-nth 3))
      (table? (yld/mixed-nth 4))
      ;; a nil yield is a value, not an end-of-stream marker: the vec
      ;; still holds all seven slots
      (nil? (yld/mixed-nth 5))
      (eq? :kw (yld/mixed-nth 6)))

;;; ---[ exhaustion, and every call after it ]-------------------------------

;; Running off the end installs a resume slot that throws the SAME `done`
;; with the SAME final value again. A spent generator therefore does not
;; start erroring and never becomes unusable: it answers its final value,
;; at the resume site, for as long as anyone keeps calling it. There is no
;; separate "you already finished this one" condition to catch.

;; `yld/of` ends in a `dolist`, whose value is nil, so its final value is
;; nil - which is why `yld/drain` can discard it without losing anything.
(defun yld/of-ret (xs)
  (gen (lambda (yi) (dolist (x xs) (yi x)) :of-end)))

(defun yld/past-the-end ()
  (let ((co (yld/of-ret '(1))))
    (list (co nil)
          (catch 'done (co nil))
          (catch 'done (co nil))
          (catch 'done (co nil)))))

(defun yld/implicit-final-value ()
  (let ((co (yld/of '(1))))
    (co nil)
    (catch 'done (co nil))))

;; A reference-typed final value is allowed, and it is the same object
;; every time - the slot holds one value, it is not recomputed per call.
(defun yld/ref-final ()
  (let ((co (gen (lambda (yi) (yi 1) (list :r)))))
    (co nil)
    (let ((a (catch 'done (co nil)))
          (b (catch 'done (co nil))))
      (list (eq? '(:r) a) (eq? a b)))))

;; Draining a spent generator answers no further values rather than
;; raising, so a second and third drain are simply empty.
(defun yld/second-drain ()
  (let ((co (yld/of '(1 2))))
    (list (yld/drain co) (yld/drain co) (yld/drain co))))

(test yld-past-the-end
      (eq? '(1 :of-end :of-end :of-end) (yld/past-the-end))
      (nil? (yld/implicit-final-value))
      (eq? '(true true) (yld/ref-final))
      (eq? (list (vec 1 2) (vec) (vec)) (yld/second-drain)))

;;; ---[ argument checking ]-------------------------------------------------

(defun yld/catch (tag form) (catch tag (eval form)))

(defun yld/starts-with? (prefix s)
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

(defun yld/msg? (tag prefix form)
  (let ((v (yld/catch tag form)))
    (and (string? v) (yld/starts-with? prefix v))))

;; `gen` does not check that its argument is callable - it only stores
;; it - so a bad argument is reported at the first call, by the caller,
;; and names `λ` rather than `gen`.
(defun yld/gen-of-an-integer-is-made () (if (gen 5) true false))

(test yld-argument-checks
      (yld/msg? 'arg-error "Argument Error: gen expected 1 arguments, but got 0" '(gen))
      (yld/msg? 'arg-error "Argument Error: gen expected 1 arguments, but got 2"
                '(gen (lambda (yi) 1) 2))
      ;; constructing with a non-callable succeeds ...
      (yld/gen-of-an-integer-is-made)
      ;; ... and only the first call complains
      (yld/msg? 'type-error "Type Error: Expected one of lambda, subr, continuation, object"
                '(if ((gen 5) nil) 1 2))
      ;; the body must take exactly the one yielder argument
      (yld/msg? 'arg-error "Argument Error: λ expected 0 argument, but got 1"
                '(if ((gen (lambda () 1)) nil) 1 2))
      ;; the plural follows the RECEIVED count, so "got 1" reads "argument"
      (yld/msg? 'arg-error "Argument Error: λ expected 2 argument, but got 1"
                '(if ((gen (lambda (yi z) 1)) nil) 1 2))
      ;; and the yielder itself takes exactly one value
      (yld/msg? 'arg-error "Argument Error: λ expected 1 arguments, but got 0"
                '(if ((gen (lambda (yi) (yi))) nil) 1 2))
      (yld/msg? 'arg-error "Argument Error: λ expected 1 arguments, but got 2"
                '(if ((gen (lambda (yi) (yi 1 2))) nil) 1 2)))

;;; ---[ suspended generators are live references ]--------------------------

;; A suspended generator holds a continuation, a table and a closure. All
;; three have to survive collection, and the values yielded afterwards
;; have to be intact.

(defun yld/churn (n)
  (let ((junk (vec)))
    (range (i (0 n))
      (push junk (vec i i i)))
    (len junk)))

(defun yld/survives-gc ()
  (let ((a (yld/of '(1 2 3)))
        (b (yld/of '(4 5 6))))
    (a nil)
    (b nil)
    (gc)
    (yld/churn 200)
    (gc)
    (list (a nil) (b nil) (a nil) (b nil))))

;; A generator that only ever becomes reachable through a table.
(defun yld/gc-through-a-table ()
  (let ((tb (make-table :g (yld/naturals))))
    ((get tb :g) nil)
    (gc)
    (yld/churn 200)
    (gc)
    (list ((get tb :g) nil) ((get tb :g) nil))))

(test yld-suspended-generators-survive-collection
      (eq? '(2 5 3 6) (yld/survives-gc))
      (eq? '(1 2) (yld/gc-through-a-table)))

;;; ---[ volume ]------------------------------------------------------------

;; A thousand suspend/resume round trips through one generator, and a
;; hundred generators suspended at the same time. Both are here because
;; every resume reinstates a saved stack; if that leaked, these would be
;; where it showed.

(defun yld/counted (n)
  (gen (lambda (yi) (range (i (0 n)) (yi i)))))

(defun yld/sum-of (n)
  (let ((co (yld/counted n))
        (s 0))
    (range (i (0 n)) (set s (+ s (co nil))))
    s))

(defun yld/many-at-once (n)
  (let ((gs (vec))
        (s 0))
    (range (i (0 n))
      (push gs (yld/counted 3)))
    ;; advance every one of them one step, then finish them all
    (dolist (g gs) (set s (+ s (g nil))))
    (dolist (g gs) (set s (+ s (g nil))))
    (dolist (g gs) (set s (+ s (g nil))))
    s))

(test yld-volume
      (= 499500 (yld/sum-of 1000))
      ;; 100 generators x (0 + 1 + 2)
      (= 300 (yld/many-at-once 100)))

(defun yld/end-of-line ()
  (gen (lambda (yi)
         (yi 1)
         (yi 2)
         'hello)))

(test yld-end-of-line
      (eq? '(1 2 hello hello hello hello)
           (let ((co (yld/end-of-line)))
             (list
              (catch 'done (co 1))
              (catch 'done (co 1))
              (catch 'done (co 1))
              (catch 'done (co 1))
              (catch 'done (co 1))
              (catch 'done (co 1))))))
