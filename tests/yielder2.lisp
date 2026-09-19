;;; Ways people actually use `gen`: combinators, pipelines, delegation
;;; that carries a result back, schedulers, state machines, consumers.
;;; Companion to tests/yielder.lisp, which pins the protocol itself.

;;; ---[ the toolkit every section below is built from ]---------------------

;; The standard source. Its final value is `:y2-end` rather than the nil a
;; bare `dolist` would leave, so that every test which cares about where a
;; final value travelled can see one that could not have come from
;; anywhere else.
(defun y2/of (xs)
  (gen (lambda (yi) (dolist (x xs) (yi x)) :y2-end)))

;; Everything the generator yielded, discarding the final value.
(defun y2/drain (co)
  (let ((out (vec)))
    (catch 'done (loop (push out (co nil))))
    out))

;; The final value, discarding everything yielded. `loop` never returns
;; normally, so the `catch` can only answer the `done` payload.
(defun y2/final (co)
  (catch 'done (loop (co nil))))

;; n values, leaving the generator suspended.
(defun y2/take (co n)
  (let ((out (vec)))
    (while (> n 0)
      (push out (co nil))
      (dec! n))
    out))

(defun y2/catch (tag form) (catch tag (eval form)))

;;; ---[ telling a yield apart from an exhaustion ]--------------------------

;; `(catch 'done (co nil))` answers a yielded value and a final value the
;; same way, so on its own it cannot say which happened. A driver that
;; needs to know sets a flag INSIDE the catch, after the call: the flag
;; stays false exactly when the call threw.

(defvar y2/yielded nil)

(defun y2/step (co)
  (set y2/yielded false)
  (catch 'done
    (let ((v (co nil)))
      (set y2/yielded true)
      v)))

(defun y2/step-seq ()
  (let ((co (y2/of '(1))))
    (let* ((a (y2/step co))
           (ay y2/yielded)
           (b (y2/step co))
           (by y2/yielded))
      (list a ay b by))))

;; Why the flag is needed at all: a generator whose final value is also a
;; value it yields is genuinely ambiguous by value, and stays ambiguous
;; for every call after the end.
(defun y2/ambiguous ()
  (let ((co (gen (lambda (yi) (yi :same) :same))))
    (list (catch 'done (co nil))
          (catch 'done (co nil))
          (catch 'done (co nil)))))

(test y2-yield-versus-exhaustion
      (eq? '(1 true :y2-end false) (y2/step-seq))
      (eq? '(:same :same :same) (y2/ambiguous)))

;;; ---[ combinators: a generator wrapping a generator ]---------------------

;; Each of these drains its source under its own `catch 'done` and
;; re-yields. The `catch` is the last form in the body, so whatever the
;; SOURCE finished with becomes the wrapper's own final value and travels
;; the length of a pipeline unchanged. The two that cannot do that -
;; `y2/gtake`, which stops early, and `y2/gchain`, which has two sources -
;; say so with a final value of their own.

(defun y2/gmap (f co)
  (gen (lambda (yi)
         (catch 'done (loop (yi (f (co nil))))))))

(defun y2/gfilter (pr co)
  (gen (lambda (yi)
         (catch 'done
           (loop (let ((v (co nil)))
                   (when (pr v) (yi v))))))))

(defun y2/gtake (co n)
  (gen (lambda (yi)
         (range (i (0 n)) (yi (co nil)))
         :truncated)))

(defun y2/gdrop (co n)
  (gen (lambda (yi)
         (range (i (0 n)) (co nil))
         (catch 'done (loop (yi (co nil)))))))

(defun y2/genumerate (co)
  (gen (lambda (yi)
         (let ((i 0))
           (catch 'done
             (loop (yi (list i (co nil)))
                   (inc! i)))))))

(defun y2/gchain (a b)
  (gen (lambda (yi)
         (catch 'done (loop (yi (a nil))))
         (catch 'done (loop (yi (b nil))))
         :chained)))

(defun y2/gzip (a b)
  (gen (lambda (yi)
         (catch 'done (loop (yi (list (a nil) (b nil))))))))

(defun y2/gflatten (co)
  (gen (lambda (yi)
         (catch 'done (loop (dolist (x (co nil)) (yi x)))))))

(defun y2/mapped ()    (y2/drain (y2/gmap (lambda (x) (* x x)) (y2/of '(1 2 3)))))
(defun y2/filtered ()  (y2/drain (y2/gfilter (lambda (x) (= 0 (% x 2))) (y2/of '(1 2 3 4 5)))))
(defun y2/taken ()     (y2/drain (y2/gtake (y2/of '(1 2 3 4)) 2)))
(defun y2/dropped ()   (y2/drain (y2/gdrop (y2/of '(1 2 3 4)) 2)))
(defun y2/enumerated () (y2/drain (y2/genumerate (y2/of '(:a :b)))))
(defun y2/chained ()   (y2/drain (y2/gchain (y2/of '(1 2)) (y2/of '(:a)))))
(defun y2/zipped ()    (y2/drain (y2/gzip (y2/of '(1 2 3)) (y2/of '(:a :b)))))
(defun y2/flattened () (y2/drain (y2/gflatten (y2/of '((1 2) (3) () (4))))))

;; Dropping more than the source holds is empty rather than an error: the
;; `done` from the discarding loop is caught by the same handler.
(defun y2/dropped-past-the-end () (y2/drain (y2/gdrop (y2/of '(1 2)) 5)))
(defun y2/taken-zero ()           (y2/drain (y2/gtake (y2/of '(1 2)) 0)))
(defun y2/zipped-empty ()         (y2/drain (y2/gzip (y2/of '()) (y2/of '(1 2)))))

(test y2-combinators
      (eq? (vec 1 4 9) (y2/mapped))
      (eq? (vec 2 4) (y2/filtered))
      (eq? (vec 1 2) (y2/taken))
      (eq? (vec 3 4) (y2/dropped))
      (eq? (vec '(0 :a) '(1 :b)) (y2/enumerated))
      (eq? (vec 1 2 :a) (y2/chained))
      ;; the shorter side ends the zip
      (eq? (vec '(1 :a) '(2 :b)) (y2/zipped))
      (eq? (vec 1 2 3 4) (y2/flattened))
      (eq? (vec) (y2/dropped-past-the-end))
      (eq? (vec) (y2/taken-zero))
      (eq? (vec) (y2/zipped-empty)))

;;; ---[ the final value travels the length of a pipeline ]------------------

;; This is the part the reworked semantics made possible: the wrapper's
;; own `catch 'done` answers what the source finished with, and returning
;; it re-throws it to the next stage out. A combinator that stops early
;; substitutes its own instead, which is how a caller can tell "the source
;; ran out" from "I cut it short".

(defun y2/final-through-map ()    (y2/final (y2/gmap (lambda (x) x) (y2/of '(1 2)))))
(defun y2/final-through-filter () (y2/final (y2/gfilter (lambda (x) true) (y2/of '(1)))))
(defun y2/final-through-three ()
  (y2/final (y2/gmap (lambda (x) x)
                     (y2/genumerate
                      (y2/gfilter (lambda (x) true) (y2/of '(1 2)))))))
(defun y2/final-of-truncation ()  (y2/final (y2/gtake (y2/of '(1 2 3)) 2)))
(defun y2/final-of-a-chain ()     (y2/final (y2/gchain (y2/of '(1)) (y2/of '(2)))))

;; A source that reports a count rather than a marker: the body's own
;; local arrives at the driver, which is how a sub-generator reports work
;; done without a shared variable.
(defun y2/counted (xs)
  (gen (lambda (yi)
         (let ((n 0))
           (dolist (x xs) (yi x) (inc! n))
           n))))

(defun y2/count-through-a-filter ()
  (y2/final (y2/gfilter (lambda (x) (= 0 (% x 2))) (y2/counted '(1 2 3 4 5)))))

(test y2-final-value-propagates
      (eq? :y2-end (y2/final-through-map))
      (eq? :y2-end (y2/final-through-filter))
      (eq? :y2-end (y2/final-through-three))
      (eq? :truncated (y2/final-of-truncation))
      (eq? :chained (y2/final-of-a-chain))
      ;; five yielded, two survived the filter, and the FIVE comes out
      (= 5 (y2/count-through-a-filter)))

;;; ---[ pipelines ]---------------------------------------------------------

;; Stages compose the way they do in any lazy-sequence library: nothing
;; between them buffers, and an infinite source is fine as long as some
;; stage bounds it.

(defun y2/naturals ()
  (gen (lambda (yi) (let ((i 0)) (loop (yi i) (inc! i))))))

(defun y2/pipeline (n)
  (y2/gmap (lambda (x) (+ x 1))
           (y2/gfilter (lambda (x) (= 0 (% x 3)))
                       (y2/gmap (lambda (x) (* x 2))
                                (y2/gtake (y2/naturals) n)))))

(defun y2/pipeline-values () (y2/drain (y2/pipeline 10)))

;; The same stages assembled the other way round: bound LAST instead of
;; first. Only the second one can be written against an infinite source
;; without the take, and both answer the same thing here.
(defun y2/pipeline-bounded-last ()
  (y2/drain (y2/gtake (y2/gmap (lambda (x) (+ x 1))
                               (y2/gfilter (lambda (x) (= 0 (% x 3)))
                                           (y2/gmap (lambda (x) (* x 2))
                                                    (y2/naturals))))
                      4)))

;; A pipeline is a value: it can be built by a function, held in a vec,
;; and driven later.
(defun y2/pipeline-from-a-vec ()
  (let ((v (vec)))
    (push v (y2/pipeline 10))
    (y2/drain (get v 0))))

(test y2-pipelines
      (eq? (vec 1 7 13 19) (y2/pipeline-values))
      (eq? (vec 1 7 13 19) (y2/pipeline-bounded-last))
      (eq? (vec 1 7 13 19) (y2/pipeline-from-a-vec)))

;;; ---[ delegation: draining a sub-generator from inside a body ]-----------

;; The yielder is an ordinary value, so the relay that forwards one
;; generator into another can be a plain top-level function. What it
;; answers is the sub-generator's final value, which is what makes a
;; sub-generator able to report back rather than only produce.

(defun y2/relay (inner yi)
  (catch 'done (loop (yi (inner nil)))))

(defun y2/delegate-two (xs ys)
  (gen (lambda (yi)
         (let* ((n1 (y2/relay (y2/counted xs) yi))
                (n2 (y2/relay (y2/counted ys) yi)))
           (list :counts n1 n2)))))

(defun y2/delegate-values () (y2/drain (y2/delegate-two '(1 2) '(:a))))
(defun y2/delegate-final ()  (y2/final (y2/delegate-two '(1 2) '(:a))))

;; Delegation decided at run time: a body that picks which sub-generator
;; to forward based on what it is sent.
(defun y2/switchboard ()
  (gen (lambda (yi)
         (let ((which (yi :ready)))
           (if (eq? which :letters)
               (y2/relay (y2/of '(:a :b)) yi)
             (y2/relay (y2/of '(1 2)) yi))))))

(defun y2/switch-to (which)
  (let ((co (y2/switchboard)))
    (co nil)
    (let ((out (vec)))
      (catch 'done (loop (push out (co which))))
      out)))

;; Recursive delegation: the body of a generator forwarding a generator
;; built by the same function, three deep.
(defun y2/countdown (n)
  (gen (lambda (yi)
         (yi n)
         (if (> n 0)
             (y2/relay (y2/countdown (- n 1)) yi)
           :bottom))))

(test y2-delegation
      (eq? (vec 1 2 :a) (y2/delegate-values))
      (eq? '(:counts 2 1) (y2/delegate-final))
      (eq? (vec :a :b) (y2/switch-to :letters))
      (eq? (vec 1 2) (y2/switch-to :numbers))
      (eq? (vec 3 2 1 0) (y2/drain (y2/countdown 3)))
      ;; the innermost generator's final value climbs back out through
      ;; every level of the recursion
      (eq? :bottom (y2/final (y2/countdown 3))))

;;; ---[ consumers: folding a generator down to one value ]------------------

;; The mirror image of a combinator. These do not produce a generator,
;; they drive one, so the `catch 'done` is the loop's exit condition.

(defun y2/fold (f seed co)
  (let ((acc seed))
    (catch 'done (loop (set acc (f acc (co nil)))))
    acc))

(defun y2/count (co)
  (y2/fold (lambda (n x) (+ n 1)) 0 co))

;; Short-circuiting: stop at the first match and leave the generator
;; suspended, so an infinite source is safe. The loop is left with a flag
;; rather than a `break` - see the note on the scheduler below.
(defun y2/find-first (pr co)
  (let ((hit :y2-none) (going true))
    (catch 'done
      (while going
        (let ((v (co nil)))
          (when (pr v)
            (set hit v)
            (set going false)))))
    hit))

(defun y2/sum-of-a-pipeline ()
  (y2/fold (lambda (a b) (+ a b)) 0 (y2/pipeline 10)))

(defun y2/found-in-an-infinite-source ()
  (y2/find-first (lambda (x) (> x 40)) (y2/gmap (lambda (x) (* x 7)) (y2/naturals))))

;; A consumer can stop early and the generator stays usable afterwards.
(defun y2/resume-after-a-find ()
  (let ((co (y2/of '(1 2 3 4 5))))
    (let ((hit (y2/find-first (lambda (x) (= x 2)) co)))
      (list hit (y2/drain co)))))

(test y2-consumers
      (= 4 (y2/count (y2/of '(:a :b :c :d))))
      (= 0 (y2/count (y2/of '())))
      (= 40 (y2/sum-of-a-pipeline))
      (= 42 (y2/found-in-an-infinite-source))
      (eq? :y2-none (y2/find-first (lambda (x) (> x 99)) (y2/of '(1 2))))
      (eq? (list 2 (vec 3 4 5)) (y2/resume-after-a-find)))

;;; ---[ cooperative scheduling ]--------------------------------------------

;; The coroutine use of the construct: several suspended bodies advanced a
;; step at a time, each dropped from the pool as it finishes. `y2/step`'s
;; flag is what says which ones are still live.
;;
;; The pool loop is left with a flag rather than with `break`. That is
;; deliberate and load-bearing: a `break` out of a `loop` that is not in
;; tail position, where the body bound a `let` local across a suspension,
;; currently corrupts the value stack.

(defun y2/round-robin (gs)
  (let ((out (vec))
        (live true))
    (while live
      (set live false)
      (let ((next (vec)))
        (dolist (g gs)
          (let ((v (y2/step g)))
            (when y2/yielded
              (push out v)
              (push next g)
              (set live true))))
        (set gs next)))
    out))

(defun y2/uneven-pool ()
  (y2/round-robin (vec (y2/of '(1 2 3)) (y2/of '(:a)) (y2/of '(10 20)))))

(defun y2/pool-of-one ()   (y2/round-robin (vec (y2/of '(1 2)))))
(defun y2/empty-pool ()    (y2/round-robin (vec)))
(defun y2/pool-of-silent () (y2/round-robin (vec (gen (lambda (yi) :never)))))

;; A pool whose members are different KINDS of generator - finite, mapped,
;; and one bounded out of an infinite source.
(defun y2/mixed-pool ()
  (y2/round-robin (vec (y2/of '(1 2))
                       (y2/gmap (lambda (x) (* x 10)) (y2/of '(1 2 3)))
                       (y2/gtake (y2/naturals) 1))))

(test y2-round-robin-scheduling
      (eq? (vec 1 :a 10 2 20 3) (y2/uneven-pool))
      (eq? (vec 1 2) (y2/pool-of-one))
      (eq? (vec) (y2/empty-pool))
      (eq? (vec) (y2/pool-of-silent))
      (eq? (vec 1 10 0 2 20 30) (y2/mixed-pool)))

;;; ---[ generators that consume: the resume value as an input ]-------------

;; A body that reads its yielder call is a sink as much as a source. The
;; value it accumulates comes back out as the final value, so the driver
;; never needs a shared variable.

(defun y2/collector ()
  (gen (lambda (yi)
         (let ((out (vec))
               (going true))
           (while going
             (let ((v (yi (len out))))
               (if (eq? v :stop)
                   (set going false)
                 (push out v))))
           out))))

(defun y2/collect-three ()
  (let ((co (y2/collector)))
    (let* ((a (co nil))
           (b (co :a))
           (c (co :b)))
      (list a b c (catch 'done (co :stop))))))

;; A running average: what it yields depends on everything sent so far.
(defun y2/averager ()
  (gen (lambda (yi)
         (let ((total 0) (n 0))
           (loop
            (let ((x (yi (if (= n 0) 0 (/ total n)))))
              (set total (+ total x))
              (inc! n)))))))

(defun y2/average-run ()
  (let ((co (y2/averager)))
    (list (co nil) (co 10) (co 20) (co 30))))

;; A state machine driven entirely by what it is sent.
(defun y2/turnstile ()
  (gen (lambda (yi)
         (let ((st :locked))
           (loop
            (let ((ev (yi st)))
              (set st (case st
                        (:locked   (if (eq? ev :coin) :unlocked :locked))
                        (:unlocked (if (eq? ev :push) :locked :unlocked))
                        (_ :locked)))))))))

(defun y2/turnstile-run ()
  (let ((co (y2/turnstile)))
    (list (co nil) (co :push) (co :coin) (co :coin) (co :push))))

(test y2-generators-as-consumers
      (eq? (list 0 1 2 (vec :a :b)) (y2/collect-three))
      ;; 0 with nothing sent, then 10/1, 30/2, 60/3 - the average
      ;; INCLUDES the value that arrived on the same call
      (eq? '(0 10 15 20) (y2/average-run))
      (eq? '(:locked :locked :unlocked :unlocked :locked) (y2/turnstile-run)))

;;; ---[ where the values come from ]----------------------------------------

;; `dolist` drives every sequence type in this dialect, so one body shape
;; covers cons lists, vecs, strings and tables. A table yields its keys,
;; in no order worth pinning, which is why only the count is asserted.

(defun y2/from-a-vec ()    (y2/drain (y2/of (vec 1 2 3))))
(defun y2/from-a-string () (len (y2/drain (gen (lambda (yi) (dolist (c "hey") (yi c)))))))
(defun y2/from-a-table ()  (len (y2/drain (gen (lambda (yi) (dolist (k (make-table :a 1 :b 2)) (yi k)))))))

;; A recursive walk: the yielder threaded through a function that calls
;; itself, flattening arbitrarily nested lists.
(defun y2/walk-deep (yi x)
  (if (cons? x)
      (dolist (e x) (y2/walk-deep yi e))
    (yi x)))

(defun y2/deep-flatten (x)
  (gen (lambda (yi) (y2/walk-deep yi x) :flat)))

;; A generator whose yielded values are themselves generators, drained
;; lazily by the caller one row at a time.
(defun y2/rows (n)
  (gen (lambda (yi)
         (range (i (0 n)) (yi (y2/of (list i (* i 10)))))
         :rows-end)))

(defun y2/rows-run ()
  (let ((co (y2/rows 2)))
    (list (y2/drain (co nil))
          (y2/drain (co nil))
          (catch 'done (co nil)))))

(test y2-sources
      (eq? (vec 1 2 3) (y2/from-a-vec))
      (= 3 (y2/from-a-string))
      (= 2 (y2/from-a-table))
      (eq? (vec 1 2 3 4 5) (y2/drain (y2/deep-flatten '(1 (2 (3 4)) 5))))
      ;; `nil` is not a cons, so the walk treats the empty list as a LEAF
      ;; and yields it - flattening nothing still produces one value
      (eq? (vec nil) (y2/drain (y2/deep-flatten '())))
      (eq? (vec 1 nil 2) (y2/drain (y2/deep-flatten '(1 () 2))))
      (eq? :flat (y2/final (y2/deep-flatten '(1))))
      (eq? (list (vec 0 0) (vec 1 10) :rows-end) (y2/rows-run)))

;;; ---[ partial consumption, abandonment, restart ]-------------------------

;; Nothing has to finish. A half-driven generator can be dropped, and a
;; constructor can be called again for a fresh one at the start.

(defun y2/abandon-and-restart ()
  (let ((a (y2/of '(1 2 3))))
    (y2/take a 2)
    (set a nil)
    (gc)
    (y2/drain (y2/of '(7 8)))))

(defun y2/two-from-one-constructor ()
  (let ((a (y2/of '(1 2 3)))
        (b (y2/of '(1 2 3))))
    (y2/take a 2)
    (list (y2/drain a) (y2/drain b))))

;; Interleaving a drain of one stage with a drain of another built on the
;; same source is NOT independent - they share the one suspended chain.
(defun y2/shared-source ()
  (let ((src (y2/of '(1 2 3 4))))
    (let ((evens (y2/gfilter (lambda (x) (= 0 (% x 2))) src)))
      (list (evens nil) (src nil) (evens nil)))))

(test y2-partial-consumption
      (eq? (vec 7 8) (y2/abandon-and-restart))
      (eq? (list (vec 3) (vec 1 2 3)) (y2/two-from-one-constructor))
      ;; 2 through the filter, then 3 taken from under it, then 4
      (eq? '(2 3 4) (y2/shared-source)))

;;; ---[ throws, errors, and the boundaries around a body ]------------------

;; A plain `throw` from a body unwinds the body's own stack and so reaches
;; the catch that was live when that stack was captured - the call that
;; STARTED the generator. Wrapping a later resume in a catch of the same
;; tag does not intercept it. `done` goes the other way, to the current
;; call, which is exactly why the combinators above work.

(defun y2/raises-on-resume ()
  (gen (lambda (yi) (yi 1) (throw 'y2-tag :from-body))))

(defun y2/throw-through-a-combinator ()
  (let ((co (y2/gmap (lambda (x) x) (y2/raises-on-resume))))
    (catch 'y2-tag
      (let ((a (co nil)))
        (list :first a (catch 'y2-tag (list :second (co nil))))))))

;; An interpreter error raised inside a body behaves like any other: fatal
;; outside `eval`, a catchable throw inside one.
(defvar y2/bad nil)
(defun y2/bad-start () (set y2/bad (gen (lambda (yi) (yi 1) (car 5)))) (y2/bad nil))
(defun y2/bad-resume () (y2/bad nil))

(defun y2/error-in-a-body ()
  (y2/bad-start)
  (string? (y2/catch 'type-error '(if (y2/bad-resume) :then :else))))

;; A combinator that forgets its `catch 'done` does not hang or corrupt
;; anything: the source's `done` simply travels out to the driver's
;; handler, ending the drain with whatever had accumulated.
(defun y2/unguarded (inner)
  (gen (lambda (yi) (loop (yi (inner nil))))))

(test y2-throws-and-errors
      (eq? :from-body (y2/throw-through-a-combinator))
      ;; (y2/error-in-a-body) ;; FIXME!!!
      (eq? (vec 1 2) (y2/drain (y2/unguarded (y2/of '(1 2)))))
      )

;;; ---[ argument checking on the closure `gen` answers ]--------------------

;; The generator closure takes exactly one value - the resume value - and
;; says so as an ordinary `λ` arity error, because that is all it is.

(defun y2/arity (form) (y2/catch 'arg-error form))

(test y2-generator-closure-arity
      (string? (y2/arity '(if ((y2/of '(1))) 1 2)))
      (string? (y2/arity '(if ((y2/of '(1)) 1 2) 1 2)))
      ;; and one argument is fine, whatever it is
      (eq? (vec 1) (y2/drain (y2/of '(1)))))

;;; ---[ volume ]------------------------------------------------------------

;; Kept deliberately modest. Each element of a piped drain is a resume
;; through every stage, so the work here is stages x elements, and the
;; point is that the shapes above survive being used in bulk rather than
;; that any particular size is safe.

(defun y2/long-drain ()   (len (y2/drain (y2/gtake (y2/naturals) 200))))
(defun y2/piped-drain ()  (len (y2/drain (y2/pipeline 150))))
(defun y2/many-in-a-pool ()
  (let ((gs (vec)))
    (range (i (0 40)) (push gs (y2/of '(1 2))))
    (len (y2/round-robin gs))))

(test y2-volume
      (= 200 (y2/long-drain))
      (= 50 (y2/piped-drain))
      ;; 40 generators x 2 values each
      (= 80 (y2/many-in-a-pool)))
