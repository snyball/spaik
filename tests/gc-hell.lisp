;;; Collector and write-barrier stress: one test per heap shape.
;;; Barrier sections avoid (gc) on purpose - a forced full collection
;;; re-scans roots and would heal the very hole under test.

;; Every section is the same adversarial shape aimed at a different
;; mutating opcode or heap topology:
;;
;;   1. build a victim reachable only through a temporary
;;   2. allocate hard, so the destination container is already Black
;;   3. write the victim into the Black container   <- barrier here
;;   4. drop every other path to the victim
;;   5. allocate hard again, to drive the cycle into sweep/compact
;;   6. read the victim back and check it is intact
;;
;; Objects are allocated BLACK, so a freshly allocated compound is
;; never traced at birth; anything it points at has to be reached some
;; other way, or protected by the write barrier on whichever opcode
;; installed it. A section returns its mismatch count, so a collector
;; that reclaims a live object shows up as a wrong value rather than as
;; a program that merely finished.


;; ====================================================================
;; shared fixtures
;; ====================================================================

;; Small LCG. Kept under 2^16 so that seed*25173 stays inside i32 -
;; (+ 2147483647 1) is a checked overflow in this dialect.
(define gch/seed 12345)
(defun gch/rand (n)
  (set gch/seed (% (+ (* gch/seed 25173) 13849) 65536))
  (% gch/seed n))

;; Allocation pressure: a burst of varied, immediately-garbage objects.
;; Varied on purpose - different size classes exercise different
;; free-list and compaction paths than a monoculture of tables would.
(defun gch/churn (n)
  (let ((sink (vec))
        (i 0))
    (while (< i n)
      (push sink (make-table))
      (push sink (vec i (+ i 1) (+ i 2)))
      (push sink (cons i (cons (+ i 1) nil)))
      (push sink (concat "churn-" i))
      (if (> (len sink) 400) (set sink (vec)))
      (set i (+ i 1)))
    (len sink)))


;; ====================================================================
;; SET(var) barrier - global slot
;; ====================================================================

(define gch/global-slot nil)

(defun gch/set-global (rounds)
  (let ((bad 0) (r 0))
    (while (< r rounds)
      (gch/churn 60)
      ;; victim is built inline and installed straight into a global
      (set gch/global-slot (vec (concat "g-" r) (list r (+ r 1)) (make-table)))
      (set (get (get gch/global-slot 2) :tag) r)
      (gch/churn 120)
      (unless (= (get gch/global-slot 0) (concat "g-" r)) (set bad (+ bad 1)))
      (unless (= (car (get gch/global-slot 1)) r) (set bad (+ bad 1)))
      (unless (= (get (get gch/global-slot 2) :tag) r) (set bad (+ bad 1)))
      (set r (+ r 1)))
    ;; leave nothing of ours reachable from a global: every later test
    ;; in the suite would otherwise re-trace it on every collection
    (set gch/global-slot nil)
    bad))

(test gch-set-var-barrier-global-slot
      (= 0 (gch/set-global 300)))


;; ====================================================================
;; SET(var) barrier - closure-captured slot
;; ====================================================================

(defun gch/set-closure (rounds)
  (let ((bad 0) (r 0) (box (vec nil)))
    ;; the mutator only ever touches `box` through a closure, so the
    ;; write goes through the captured reference rather than a local
    (let ((put (lambda (v) (set (get box 0) v)))
          (peek (lambda () (get box 0))))
      (while (< r rounds)
        (gch/churn 50)
        (put (list (concat "c-" r) (vec r) (cons r r)))
        (gch/churn 100)
        (unless (= (car (peek)) (concat "c-" r)) (set bad (+ bad 1)))
        (unless (= (get (car (cdr (peek))) 0) r) (set bad (+ bad 1)))
        (set r (+ r 1))))
    bad))

(test gch-set-var-barrier-closure-slot
      (= 0 (gch/set-closure 300)))


;; ====================================================================
;; VPUSH barrier - Black-at-birth wrapper into a Black vec
;; ====================================================================

(defun gch/vpush (rounds)
  (let ((bad 0) (r 0) (acc (vec)) (tmp (vec)) (idx 0) (w nil))
    (while (< r rounds)
      (set tmp (vec (concat "p-" r)))
      (gch/churn 80)                    ; get `acc` fully traced / Black
      (set w (vec (get tmp 0) (list r) (make-table)))
      (set tmp (vec))                   ; sole path to victim is now `w`
      (set idx (len acc))
      (push acc w)                      ; <- the write under test
      (set w nil)
      (gch/churn 80)
      (unless (= (get (get acc idx) 0) (concat "p-" r)) (set bad (+ bad 1)))
      (unless (= (car (get (get acc idx) 1)) r) (set bad (+ bad 1)))
      (if (> (len acc) 500) (set acc (vec)))
      (set r (+ r 1)))
    bad))

(test gch-vpush-barrier-black-wrapper
      (= 0 (gch/vpush 300)))


;; ====================================================================
;; VSET barrier - overwrite an interior slot of a Black vec
;; ====================================================================

(defun gch/vset (rounds)
  (let ((bad 0) (r 0) (slots (vec 0 0 0 0 0 0 0 0)) (k 0))
    (while (< r rounds)
      (gch/churn 90)
      (set k (% r 8))
      ;; overwrite in place; the old occupant dies at the same instant
      (set (get slots k) (vec (concat "s-" r) (list r r r)))
      (gch/churn 90)
      (unless (= (get (get slots k) 0) (concat "s-" r)) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-vset-barrier-interior-slot
      (= 0 (gch/vset 300)))


;; ====================================================================
;; APN barrier - append onto a cons chain that is already Black
;; ====================================================================

(defun gch/append-barrier (rounds)
  (let ((bad 0) (r 0) (box (vec (list "seed"))))
    (while (< r rounds)
      (gch/churn 70)
      (set (get box 0) (append (get box 0) (list (concat "a-" r) (vec r))))
      (gch/churn 70)
      (unless (= (car (cdr (get box 0))) (concat "a-" r)) (set bad (+ bad 1)))
      (unless (= (get (car (cdr (cdr (get box 0)))) 0) r) (set bad (+ bad 1)))
      (set (get box 0) (list "seed"))
      (set r (+ r 1)))
    bad))

(test gch-apn-barrier-black-cons-chain
      (= 0 (gch/append-barrier 300)))


;; ====================================================================
;; table insert barrier - fresh compound into a Black table
;; ====================================================================

(defun gch/table-insert (rounds)
  (let ((bad 0) (r 0) (tb (make-table)) (k 0))
    (while (< r rounds)
      (gch/churn 80)
      (set k (% r 32))
      (set (get tb k) (vec (concat "t-" r) (list r) (make-table)))
      (gch/churn 80)
      (unless (= (get (get tb k) 0) (concat "t-" r)) (set bad (+ bad 1)))
      (unless (= (car (get (get tb k) 1)) r) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-table-insert-barrier
      (= 0 (gch/table-insert 300)))


;; ====================================================================
;; cycles - a vec that contains itself
;; ====================================================================
;; A naive mark that does not colour-check before recursing never
;; terminates here; a naive sweep frees a live object. This pins
;; MARKING: every pointer reads back intact, including the ones that
;; close the loop. Reclamation of cycles is a separate test below.

(defun gch/self-cycle (rounds)
  (let ((bad 0) (r 0) (v nil))
    (while (< r rounds)
      (set v (vec (concat "cyc-" r)))
      (push v v)                        ; direct self-reference
      (push v (vec v v))                ; and again, one level down
      (gch/churn 60)
      (unless (= (get (get v 1) 0) (concat "cyc-" r)) (set bad (+ bad 1)))
      (unless (= (get (get (get v 2) 0) 0) (concat "cyc-" r)) (set bad (+ bad 1)))
      ;; walk the cycle a few hops to be sure the pointers are real
      (unless (= (get (get (get v 1) 1) 0) (concat "cyc-" r)) (set bad (+ bad 1)))
      (set v nil)
      (gch/churn 60)
      (set r (+ r 1)))
    bad))

(test gch-self-referential-vec-marks-correctly
      (= 0 (gch/self-cycle 300)))


;; ====================================================================
;; mutual cycles through tables and vecs
;; ====================================================================

(defun gch/mutual-cycle (rounds)
  (let ((bad 0) (r 0) (a nil) (b nil) (c nil))
    (while (< r rounds)
      (set a (vec (concat "a-" r)))
      (set b (make-table))
      (set c (list "c" nil))
      (push a b)                        ; a -> b
      (set (get b :back) a)             ; b -> a
      (set (get b :c) c)                ; b -> c
      (set (get b :self) b)             ; b -> b
      (push a c)                        ; a -> c
      (gch/churn 80)
      (unless (= (get (get (get a 1) :back) 0) (concat "a-" r)) (set bad (+ bad 1)))
      (unless (= (get (get (get a 1) :self) :back) a) (set bad (+ bad 1)))
      (unless (= (car (get (get a 1) :c)) "c") (set bad (+ bad 1)))
      (set a nil) (set b nil) (set c nil)
      (gch/churn 80)
      (set r (+ r 1)))
    bad))

(test gch-mutual-cycle-through-table-and-vec
      (= 0 (gch/mutual-cycle 300)))


;; ====================================================================
;; cycle reclamation at scale
;; ====================================================================
;; Cycles that are garbage by the time the collection runs. A reachable
;; reference cycle used to spin `(gc)` forever with `total_frees` pinned
;; at 0 for the rest of the process - one self-referential vector was
;; enough. The two marking tests above deliberately stop short of this.

(defun gch/cycle-reclamation (rounds)
  (let ((r 0) (v nil))
    (while (< r rounds)
      (set v (vec r))
      (let ((w (vec v))) (push v w))
      (set v nil)
      (set r (+ r 1)))
    (gc)
    0))

(test gch-cycle-reclamation-at-scale-terminates
      (= 0 (gch/cycle-reclamation 2000)))

;; The same claim over three cycle shapes at once - a vec holding
;; itself, a pair of vecs holding each other, and a table under its own
;; key - all dropped together before the collection runs.

(defun gch/make-cycles (n)
  (let ((keep (vec)))
    (range (i (0 n))
      (let ((v (vec)) (a (vec)) (b (vec)) (tb (make-table :i i)))
        (push v v)
        (push a b) (push b a)
        (set (get tb :self) tb)
        (push keep v) (push keep a) (push keep tb)))
    (len keep)))

(defun gch/cyclic-garbage (n)
  (let ((bad 0))
    (unless (= (gch/make-cycles n) (* 3 n)) (set bad (+ bad 1)))
    (gc)
    (gc)
    bad))

(test gch-three-cycle-shapes-collect-together
      (= 0 (gch/cyclic-garbage 1500)))


;; ====================================================================
;; deep nesting - a vec-in-vec spine
;; ====================================================================
;; Exercises mark-stack growth rather than breadth.

(defun gch/deep-nest (rounds depth)
  (let ((bad 0) (r 0) (spine nil) (i 0) (probe nil))
    (while (< r rounds)
      (set spine (vec "bottom"))
      (set i 0)
      (while (< i depth)
        (set spine (vec spine i))       ; each level is Black-at-birth
        (set i (+ i 1)))
      (gch/churn 100)
      ;; walk all the way back down
      (set probe spine)
      (set i 0)
      (while (< i depth)
        (set probe (get probe 0))
        (set i (+ i 1)))
      (unless (= (get probe 0) "bottom") (set bad (+ bad 1)))
      (set spine nil) (set probe nil)
      (set r (+ r 1)))
    bad))

(test gch-deep-vec-spine-survives
      (= 0 (gch/deep-nest 40 400)))


;; ====================================================================
;; wide shared DAG - one victim reachable by many paths
;; ====================================================================
;; Every holder must keep the victim alive; dropping all but one must
;; still keep it alive.

(defun gch/shared-dag (rounds fanout)
  (let ((bad 0) (r 0) (victim nil) (holders (vec)) (i 0) (keep nil))
    (while (< r rounds)
      (set victim (vec (concat "shared-" r) (list r)))
      (set holders (vec))
      (set i 0)
      (while (< i fanout)
        (push holders (vec victim (make-table) i))
        (set (get (get (get holders i) 1) :v) victim)
        (set i (+ i 1)))
      (gch/churn 90)
      ;; keep exactly one path, drop the rest
      (set keep (get holders (% r fanout)))
      (set holders (vec))
      (set victim nil)
      (gch/churn 120)
      (unless (= (get (get keep 0) 0) (concat "shared-" r)) (set bad (+ bad 1)))
      (unless (= (get (get (get keep 1) :v) 0) (concat "shared-" r)) (set bad (+ bad 1)))
      (unless (= (get (get keep 0) 0) (get (get (get keep 1) :v) 0)) (set bad (+ bad 1)))
      (set keep nil)
      (set r (+ r 1)))
    bad))

(test gch-shared-dag-last-path-keeps-victim
      (= 0 (gch/shared-dag 200 16)))


;; ====================================================================
;; string churn - concat/join build fresh heap strings
;; ====================================================================

(defun gch/string-churn (rounds)
  (let ((bad 0) (r 0) (keep (vec)) (s nil) (parts nil))
    (while (< r rounds)
      (set parts (vec))
      (let ((i 0))
        (while (< i 12)
          (push parts (concat "seg" i "-"))
          (set i (+ i 1))))
      (set s (concat (join parts) "|" r))
      (push keep (vec s (len s)))
      (gch/churn 40)
      (if (> (len keep) 64)
          (let ((j 0))
            (while (< j (len keep))
              (unless (= (len (get (get keep j) 0)) (get (get keep j) 1))
                (set bad (+ bad 1)))
              (set j (+ j 1)))
            (set keep (vec))))
      (set r (+ r 1)))
    bad))

(test gch-heap-strings-keep-their-length
      (= 0 (gch/string-churn 400)))


;; ====================================================================
;; symbol churn - intern/gensym grow the symbol table
;; ====================================================================

(defun gch/symbol-churn (rounds)
  (let ((bad 0) (r 0) (syms (vec)) (s nil))
    (while (< r rounds)
      (set s (intern (concat "gch-sym-" r)))
      (push syms (vec s (concat "gch-sym-" r)))
      (push syms (vec (gensym) "g"))
      (gch/churn 40)
      (if (> (len syms) 200)
          (let ((j 0))
            (while (< j (len syms))
              (unless (= (type-of (get (get syms j) 0)) 'symbol) (set bad (+ bad 1)))
              (set j (+ j 1)))
            (set syms (vec))))
      (set r (+ r 1)))
    bad))

(test gch-interned-symbols-stay-symbols
      (= 0 (gch/symbol-churn 400)))


;; ====================================================================
;; closure churn - many closures, each capturing a fresh box
;; ====================================================================

(defun gch/closure-churn (rounds)
  (let ((bad 0) (r 0) (fns (vec)) (i 0))
    (while (< r rounds)
      ;; each iteration makes a closure over a fresh vec; the vec is
      ;; reachable ONLY through the closure's captured environment
      (push fns (let ((box (vec (concat "clo-" r) (list r))))
                  (lambda () box)))
      (gch/churn 60)
      (if (> (len fns) 100)
          (progn
            (set i 0)
            (while (< i (len fns))
              (unless (= (car (get ((get fns i)) 1)) (- (+ r 1) (- (len fns) i)))
                (set bad (+ bad 1)))
              (set i (+ i 1)))
            (set fns (vec))))
      (set r (+ r 1)))
    bad))

(test gch-captured-environments-survive
      (= 0 (gch/closure-churn 400)))


;; ====================================================================
;; catch/throw unwinding with live allocations in flight
;; ====================================================================
;; The catch is the tail of its own helper: a non-tail catch in a `let`
;; used to drop the rest of the enclosing body outright.

(defun gch/unwind-victim (r)
  (catch 'gch-tag
    ;; the thrown value is a fresh compound built during the unwind
    (let ((local (vec (concat "u-" r) (make-table))))
      (gch/churn 30)
      (throw 'gch-tag (vec (get local 0) (list r) local)))))

(defun gch/throw-unwind (rounds)
  (let ((bad 0) (r 0) (got nil))
    (while (< r rounds)
      (gch/churn 50)
      (set got (gch/unwind-victim r))
      (gch/churn 80)
      (unless (= (get got 0) (concat "u-" r)) (set bad (+ bad 1)))
      (unless (= (car (get got 1)) r) (set bad (+ bad 1)))
      (unless (= (get (get got 2) 0) (concat "u-" r)) (set bad (+ bad 1)))
      (set got nil)
      (set r (+ r 1)))
    bad))

(test gch-thrown-payload-survives-the-unwind
      (= 0 (gch/throw-unwind 300)))


;; ====================================================================
;; nested catch/throw, allocating at every level
;; ====================================================================

(defun gch/nested-inner (r a)
  (catch 'gch-inner
    (let ((b (vec (concat "n2-" r) a)))
      (gch/churn 20)
      (throw 'gch-inner (vec (concat "n3-" r) b)))))

(defun gch/nested-outer (r)
  (catch 'gch-outer
    (let ((a (vec (concat "n1-" r))))
      (gch/churn 20)
      ;; the inner catch's value is discarded on purpose; `a` must
      ;; still be intact after that unwind
      (gch/nested-inner r a)
      (gch/churn 40)
      (throw 'gch-outer (vec (concat "n4-" r) a)))))

(defun gch/nested-catch (rounds)
  (let ((bad 0) (r 0) (got nil))
    (while (< r rounds)
      (set got (gch/nested-outer r))
      (gch/churn 40)
      (unless (= (get got 0) (concat "n4-" r)) (set bad (+ bad 1)))
      (unless (= (get (get got 1) 0) (concat "n1-" r)) (set bad (+ bad 1)))
      (set got nil)
      (set r (+ r 1)))
    bad))

(test gch-nested-unwind-keeps-the-outer-frames-objects
      (= 0 (gch/nested-catch 200)))


;; ====================================================================
;; in-place rearrangement - sort!/reverse!/clone under pressure
;; ====================================================================

(defun gch/inplace (rounds)
  (let ((bad 0) (r 0) (v nil) (c nil) (n 0))
    (while (< r rounds)
      (set v (vec))
      (set n 0)
      (while (< n 24)
        (push v (gch/rand 1000))
        (set n (+ n 1)))
      (set c (clone v))
      (gch/churn 60)
      (sort! v)
      (gch/churn 60)
      (reverse! c)
      (gch/churn 60)
      (unless (= (len v) 24) (set bad (+ bad 1)))
      (unless (= (len c) 24) (set bad (+ bad 1)))
      ;; sorted must be non-decreasing
      (set n 1)
      (while (< n (len v))
        (when (< (get v n) (get v (- n 1))) (set bad (+ bad 1)))
        (set n (+ n 1)))
      (set r (+ r 1)))
    bad))

(test gch-in-place-mutators-under-pressure
      (= 0 (gch/inplace 200)))


;; ====================================================================
;; eval at runtime, building fresh compounds
;; ====================================================================
;; An `eval` whose value is USED once leaked one VM stack slot per call
;; and segfaulted as soon as any other call frame was pushed on top of
;; the leaked region - here, the churn helper's own frame.

(defun gch/eval-churn (rounds)
  (let ((bad 0) (r 0) (got nil))
    (while (< r rounds)
      (gch/churn 60)
      (set got (eval (list 'vec (concat "e-" r) (list 'list r (+ r 1)))))
      (gch/churn 60)
      (unless (= (get got 0) (concat "e-" r)) (set bad (+ bad 1)))
      (unless (= (car (get got 1)) r) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-runtime-eval-results-survive
      (= 0 (gch/eval-churn 300)))


;; ====================================================================
;; continuations held live across collections
;; ====================================================================
;; A continuation captures a slice of the VM stack. Holding one across
;; heavy allocation means the collector has to trace a root that is not
;; the live stack.

(defun gch/continuations (rounds)
  (let ((bad 0) (r 0) (saved (vec)) (i 0) (payload nil))
    (while (< r rounds)
      (set payload (vec (concat "k-" r) (list r)))
      (push saved (vec (call/cc (lambda (k) k)) payload))
      (gch/churn 70)
      (if (> (len saved) 40)
          (progn
            (set i 0)
            (while (< i (len saved))
              (unless (= (type-of (get (get saved i) 0)) 'continuation)
                (set bad (+ bad 1)))
              (unless (= (car (get (get (get saved i) 1) 1))
                         (- (+ r 1) (- (len saved) i)))
                (set bad (+ bad 1)))
              (set i (+ i 1)))
            (set saved (vec))))
      (set r (+ r 1)))
    bad))

(test gch-held-continuations-are-traced
      (= 0 (gch/continuations 200)))


;; ====================================================================
;; live iterator over a collection that keeps growing
;; ====================================================================
;; The iterator holds an internal cursor into the backing store; a
;; compaction that moves the store has to fix it up.

(defun gch/live-iterator (rounds)
  (let ((bad 0) (r 0) (v nil) (it nil) (seen 0) (x nil))
    (while (< r rounds)
      (set v (vec))
      (let ((i 0))
        (while (< i 20) (push v (vec i (concat "e" i))) (set i (+ i 1))))
      (set it (iter v))
      (set seen 0)
      ;; consume half, allocate hard, grow the backing vec, consume the rest
      (let ((j 0))
        (while (< j 10)
          (set x (next it))
          (unless (= (get x 0) j) (set bad (+ bad 1)))
          (set seen (+ seen 1))
          (set j (+ j 1))))
      (gch/churn 90)
      (let ((j 20))
        (while (< j 30) (push v (vec j (concat "e" j))) (set j (+ j 1))))
      (gch/churn 90)
      (loop
        (set x (next it))
        (if (iter-end? x) (break))
        (unless (= (get x 0) seen) (set bad (+ bad 1)))
        (set seen (+ seen 1)))
      (unless (= seen 30) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-iterator-cursor-survives-compaction
      (= 0 (gch/live-iterator 200)))


;; ====================================================================
;; table rehash churn - grow past every resize boundary, then shrink
;; ====================================================================

(defun gch/table-rehash (rounds)
  (let ((bad 0) (r 0) (tb nil) (i 0))
    (while (< r rounds)
      (set tb (make-table))
      ;; grow: every value is a fresh compound reachable only via `tb`
      (set i 0)
      (while (< i 160)
        (set (get tb i) (vec (concat "k" i "-" r) (list i)))
        (set i (+ i 1)))
      (gch/churn 60)
      ;; verify everything survived the resizes
      (set i 0)
      (while (< i 160)
        (unless (= (get (get tb i) 0) (concat "k" i "-" r)) (set bad (+ bad 1)))
        (set i (+ i 1)))
      ;; shrink: delete every other key, then check the rest
      (set i 0)
      (while (< i 160)
        (del tb i)
        (set i (+ i 2)))
      (gch/churn 60)
      (set i 1)
      (while (< i 160)
        (unless (= (get (get tb i) 0) (concat "k" i "-" r)) (set bad (+ bad 1)))
        (set i (+ i 2)))
      (unless (= (len tb) 80) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-table-values-survive-rehash-and-delete
      (= 0 (gch/table-rehash 60)))


;; ====================================================================
;; pop/shrink - the popped value must outlive its container
;; ====================================================================

(defun gch/pop-survives (rounds)
  (let ((bad 0) (r 0) (v nil) (held nil))
    (while (< r rounds)
      (set v (vec))
      (let ((i 0))
        (while (< i 12) (push v (vec (concat "p" i "-" r) (list i))) (set i (+ i 1))))
      (gch/churn 60)
      (set held (pop v))                ; sole surviving reference
      (set v nil)                       ; container gone
      (gch/churn 120)
      (unless (= (get held 0) (concat "p11-" r)) (set bad (+ bad 1)))
      (unless (= (car (get held 1)) 11) (set bad (+ bad 1)))
      (set held nil)
      (set r (+ r 1)))
    bad))

(test gch-popped-value-outlives-its-container
      (= 0 (gch/pop-survives 300)))


;; ====================================================================
;; vec oscillation - grow and shrink across the realloc boundary
;; ====================================================================
;; Repeated push/pop over a size that keeps crossing a capacity
;; boundary; every reallocation moves the backing store while the
;; elements must stay reachable.

(defun gch/vec-oscillation (rounds)
  (let ((bad 0) (r 0) (v (vec)) (n 0) (held nil))
    (while (< r rounds)
      ;; grow
      (set n 0)
      (while (< n 40)
        (push v (vec (concat "o-" r "-" n) (list n)))
        (set n (+ n 1)))
      (gch/churn 30)
      ;; hold a reference to something in the middle
      (set held (get v 20))
      ;; shrink most of the way back
      (set n 0)
      (while (< n 36)
        (pop v)
        (set n (+ n 1)))
      (gch/churn 30)
      ;; the held element was popped, but our reference must survive
      (unless (= (get held 0) (concat "o-" r "-20")) (set bad (+ bad 1)))
      ;; and what is left in the vec must be intact
      (unless (= (get (get v 0) 0) (concat "o-" r "-0")) (set bad (+ bad 1)))
      (unless (= (len v) 4) (set bad (+ bad 1)))
      (set v (vec))
      (set held nil)
      (set r (+ r 1)))
    bad))

(test gch-vec-oscillation-across-realloc
      (= 0 (gch/vec-oscillation 200)))


;; ====================================================================
;; fragmentation - alternating big and tiny allocations
;; ====================================================================
;; Big blocks interleaved with survivors is the shape that forces the
;; compactor to actually move things.

(defun gch/fragmentation (rounds)
  (let ((bad 0) (r 0) (keep (vec)) (big nil) (i 0))
    (while (< r rounds)
      ;; a big short-lived block
      (set big (vec))
      (set i 0)
      (while (< i 500) (push big i) (set i (+ i 1)))
      ;; a tiny long-lived survivor, allocated in the middle of it
      (push keep (vec (concat "surv-" r) (list r)))
      (set i 0)
      (while (< i 500) (push big (+ i 1000)) (set i (+ i 1)))
      (set big nil)                     ; big block dies, holes everywhere
      (gch/churn 60)
      (if (> (len keep) 50)
          (progn
            (set i 0)
            (while (< i (len keep))
              (unless (= (car (get (get keep i) 1))
                         (- (+ r 1) (- (len keep) i)))
                (set bad (+ bad 1)))
              (set i (+ i 1)))
            (set keep (vec))))
      (set r (+ r 1)))
    bad))

(test gch-survivors-outlive-a-fragmenting-heap
      (= 0 (gch/fragmentation 150)))


;; ====================================================================
;; long cons chains built and dropped
;; ====================================================================

(defun gch/cons-chain (rounds len)
  (let ((bad 0) (r 0) (c nil) (n 0) (p nil))
    (while (< r rounds)
      (set c nil)
      (set n 0)
      (while (< n len)
        (set c (cons (vec n (concat "c" n)) c))
        (set n (+ n 1)))
      (gch/churn 80)
      ;; walk the whole chain; every cell and every payload must be intact
      (set p c)
      (set n (- len 1))
      (while p
        (unless (= (get (car p) 0) n) (set bad (+ bad 1)))
        (set p (cdr p))
        (set n (- n 1)))
      (unless (= n -1) (set bad (+ bad 1)))
      (set c nil)
      (set r (+ r 1)))
    bad))

(test gch-long-cons-chain-stays-intact
      (= 0 (gch/cons-chain 60 500)))


;; ====================================================================
;; append at scale - APN rebuilding a growing list every iteration
;; ====================================================================
;; The barrier test above checks APN on a short list. Here the list
;; grows, so each `append` copies a longer spine and the old spine
;; becomes garbage while the new one is still being built.

(defun gch/append-growth (rounds)
  (let ((bad 0) (r 0) (box (vec nil)) (n 0) (p nil))
    (while (< r rounds)
      (set (get box 0) nil)
      (set n 0)
      (while (< n 60)
        (set (get box 0) (append (get box 0) (list (vec n (concat "g" n)))))
        (set n (+ n 1)))
      (gch/churn 40)
      (set p (get box 0))
      (set n 0)
      (while p
        (unless (= (get (car p) 0) n) (set bad (+ bad 1)))
        (set p (cdr p))
        (set n (+ n 1)))
      (unless (= n 60) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-append-growth-discards-only-the-old-spine
      (= 0 (gch/append-growth 100)))


;; ====================================================================
;; stdlib list builders - map/filter/zip allocate deep cons trees
;; ====================================================================

(defun gch/list-builders (rounds)
  (let ((bad 0) (r 0) (xs nil) (ys nil) (zs nil))
    (while (< r rounds)
      (set xs (range-list 0 60))
      (set ys (map (lambda (x) (vec x (concat "m" x))) xs))
      (gch/churn 60)
      (set zs (zip xs ys))
      (gch/churn 60)
      (unless (= (len xs) 60) (set bad (+ bad 1)))
      (unless (= (get (car ys) 1) "m0") (set bad (+ bad 1)))
      (unless (= (car (car zs)) 0) (set bad (+ bad 1)))
      (unless (= (get (cdr (car zs)) 1) "m0") (set bad (+ bad 1)))
      (unless (= (len (filter (lambda (x) (< x 10)) xs)) 10) (set bad (+ bad 1)))
      (set xs nil) (set ys nil) (set zs nil)
      (set r (+ r 1)))
    bad))

(test gch-stdlib-list-builders-under-pressure
      (= 0 (gch/list-builders 150)))


;; ====================================================================
;; explicit (gc) at adversarial points
;; ====================================================================
;; Everywhere else in this file avoids (gc) so as not to heal the hole
;; under test. Here it IS the test: force a full collection in the
;; narrowest possible window around each mutating write.

(defun gch/explicit-gc (rounds)
  (let ((bad 0) (r 0) (v (vec)) (tb (make-table)) (tmp nil) (idx 0))
    (while (< r rounds)
      (set tmp (vec (concat "x-" r) (list r)))
      (gc)
      (set idx (len v))
      (push v tmp)
      (gc)
      (set tmp nil)
      (gc)
      (set (get tb (% r 16)) (get v idx))
      (gc)
      (unless (= (get (get v idx) 0) (concat "x-" r)) (set bad (+ bad 1)))
      (unless (= (get (get tb (% r 16)) 0) (concat "x-" r)) (set bad (+ bad 1)))
      (if (> (len v) 200) (set v (vec)))
      (set r (+ r 1)))
    bad))

(test gch-full-collection-in-the-narrowest-window
      (= 0 (gch/explicit-gc 100)))


;; ====================================================================
;; by-reference capture - closure and outer scope share one vec
;; ====================================================================
;; Lambdas capture by reference, so a vec mutated through the closure
;; and read from outside must be the same object across a collection.

(defun gch/capture-aliasing (rounds)
  (let ((bad 0) (r 0) (shared nil) (writer nil) (reader nil))
    (while (< r rounds)
      (set shared (vec))
      (set writer (lambda (x) (push shared x)))
      (set reader (lambda (i) (get shared i)))
      (writer (vec (concat "w-" r) (list r)))
      (gch/churn 80)
      (writer (vec (concat "w2-" r) (list r)))
      (gch/churn 80)
      (unless (= (get (reader 0) 0) (concat "w-" r)) (set bad (+ bad 1)))
      (unless (= (get (reader 1) 0) (concat "w2-" r)) (set bad (+ bad 1)))
      (unless (= (get (get shared 0) 0) (concat "w-" r)) (set bad (+ bad 1)))
      (unless (= (len shared) 2) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-closure-and-scope-alias-one-vec
      (= 0 (gch/capture-aliasing 300)))


;; ====================================================================
;; recursion holding live references at every level
;; ====================================================================
;; Each frame owns a fresh compound; the collector must treat every
;; frame's locals as roots, not just the innermost.

(define gch/rec-bad 0)

(defun gch/rec-descend (depth)
  (let ((mine (vec (concat "d-" depth) (list depth))))
    (gch/churn 6)
    (if (< depth 1)
        0
        (let ((below (gch/rec-descend (- depth 1))))
          ;; after the recursive call has churned the heap hard, `mine`
          ;; must still be intact
          (unless (= (get mine 0) (concat "d-" depth))
            (set gch/rec-bad (+ gch/rec-bad 1)))
          (unless (= (car (get mine 1)) depth)
            (set gch/rec-bad (+ gch/rec-bad 1)))
          (+ below 1)))))

(defun gch/recursive-roots (rounds depth)
  (let ((r 0))
    (set gch/rec-bad 0)
    (while (< r rounds)
      (unless (= (gch/rec-descend depth) depth)
        (set gch/rec-bad (+ gch/rec-bad 1)))
      (set r (+ r 1)))
    gch/rec-bad))

(test gch-every-frames-locals-are-roots
      (= 0 (gch/recursive-roots 40 60)))


;; ====================================================================
;; deep recursion across a forced collection
;; ====================================================================
;; The companion to the test above at depth rather than at churn: the
;; heap is compacted underneath 2000 live frames, and the returned sum
;; proves each frame's object was still intact on the way back out.

(defun gch/deep-sum (n)
  (let ((mine (list n n n)))
    (if (< n 1)
        (progn (gc) (car mine))
        (let ((below (gch/deep-sum (- n 1))))
          (if (= 0 (% n 50)) (gc))
          (+ (car mine) below)))))

;; 2001000 is the sum of 0..2000 - one term per surviving frame.
(test gch-deep-recursion-across-a-collection
      (= 2001000 (gch/deep-sum 2000)))


;; ====================================================================
;; three-level nesting with deletion at the middle level
;; ====================================================================

(defun gch/three-level (rounds)
  (let ((bad 0) (r 0) (root nil) (i 0) (j 0) (mid nil))
    (while (< r rounds)
      (set root (make-table))
      (set i 0)
      (while (< i 10)
        (set mid (vec))
        (set j 0)
        (while (< j 8)
          (push mid (let ((leaf (make-table)))
                      (set (get leaf :tag) (concat "l-" r "-" i "-" j))
                      leaf))
          (set j (+ j 1)))
        (set (get root i) mid)
        (set i (+ i 1)))
      (gch/churn 70)
      ;; drop half the middles; the rest must be untouched
      (set i 0)
      (while (< i 10)
        (del root i)
        (set i (+ i 2)))
      (gch/churn 70)
      (set i 1)
      (while (< i 10)
        (set j 0)
        (while (< j 8)
          (unless (= (get (get (get root i) j) :tag) (concat "l-" r "-" i "-" j))
            (set bad (+ bad 1)))
          (set j (+ j 1)))
        (set i (+ i 2)))
      (set root nil)
      (set r (+ r 1)))
    bad))

(test gch-deleting-a-middle-level-spares-its-siblings
      (= 0 (gch/three-level 100)))


;; ====================================================================
;; closures stored in a table, called long after the fact
;; ====================================================================

(defun gch/closures-in-table (rounds)
  (let ((bad 0) (r 0) (tb (make-table)) (k 0) (i 0))
    (while (< r rounds)
      (set k (% r 24))
      (set (get tb k)
           (let ((cell (vec (concat "f-" r) (list r))))
             (lambda () cell)))
      (gch/churn 70)
      ;; call every closure the table currently holds
      (set i 0)
      (while (< i 24)
        (when (< i (+ r 1))
          (let ((got ((get tb i))))
            (unless (= (type-of got) 'vec) (set bad (+ bad 1)))
            (unless (= (len got) 2) (set bad (+ bad 1)))))
        (set i (+ i 1)))
      ;; the one just installed must be exactly what we put there
      (unless (= (get ((get tb k)) 0) (concat "f-" r)) (set bad (+ bad 1)))
      (set r (+ r 1)))
    bad))

(test gch-closures-stored-in-a-table-stay-callable
      (= 0 (gch/closures-in-table 200)))


;; ====================================================================
;; clone of a deep structure
;; ====================================================================

(defun gch/clone-deep (rounds)
  (let ((bad 0) (r 0) (orig nil) (copy nil) (i 0))
    (while (< r rounds)
      (set orig (vec))
      (set i 0)
      (while (< i 30)
        (push orig (vec i (concat "c-" r "-" i) (list i i)))
        (set i (+ i 1)))
      (gch/churn 50)
      (set copy (clone orig))
      (gch/churn 50)
      ;; mutate the original; the copy must not follow
      (set (get orig 0) (vec 999 "mutated" (list 999 999)))
      (gch/churn 50)
      (unless (= (get (get copy 0) 1) (concat "c-" r "-0")) (set bad (+ bad 1)))
      (unless (= (get (get orig 0) 1) "mutated") (set bad (+ bad 1)))
      (unless (= (len copy) 30) (set bad (+ bad 1)))
      (set orig nil) (set copy nil)
      (set r (+ r 1)))
    bad))

(test gch-clone-is-independent-of-its-original
      (= 0 (gch/clone-deep 150)))


;; ====================================================================
;; a registry that never lets anything die
;; ====================================================================
;; Long-lived survivors are the worst case for a generational or
;; incremental collector: they are re-traced on every cycle.

(define gch/registry (vec))

(defun gch/long-lived (rounds)
  (let ((bad 0) (r 0) (i 0))
    (set gch/registry (vec))
    (while (< r rounds)
      (push gch/registry (vec (concat "L-" r) (list r) (make-table)))
      (set (get (get gch/registry r) 2) :n r)
      (gch/churn 40)
      (set r (+ r 1)))
    ;; everything ever registered must still be intact and correct
    (set i 0)
    (while (< i rounds)
      (unless (= (get (get gch/registry i) 0) (concat "L-" i)) (set bad (+ bad 1)))
      (unless (= (car (get (get gch/registry i) 1)) i) (set bad (+ bad 1)))
      (set i (+ i 1)))
    (set gch/registry (vec))
    bad))

(test gch-long-lived-survivors-are-re-traced-intact
      (= 0 (gch/long-lived 400)))


;; ====================================================================
;; growth and release - fill the heap, drop it, collect, repeat
;; ====================================================================
;; Exercises grow / sweep-compact / reuse rather than any single
;; allocation: each round's working set is dropped whole before (gc).

(defun gch/growth-release (cycles per)
  (let ((bad 0) (live nil) (round 0))
    (while (< round cycles)
      (set live (vec))
      (range (i (0 per)) (push live (list i (list i i) (vec i))))
      (unless (= (len live) per) (set bad (+ bad 1)))
      (set live nil)
      (gc)
      (set round (+ round 1)))
    bad))

(test gch-heap-grows-and-is-released-repeatedly
      (= 0 (gch/growth-release 5 6000)))


;; ====================================================================
;; closures captured across a forced collection
;; ====================================================================

(defun gch/mk-counter (n) (let ((x (list n n n))) (lambda () (len x))))

(defun gch/closures-across-gc (n)
  (let ((fns (vec)) (total 0))
    (range (i (0 n)) (push fns (gch/mk-counter i)))
    (gc)
    (gc)
    (dolist (f fns) (set total (+ total (f))))
    (if (= total (* 3 n)) 0 1)))

(test gch-closures-captured-across-two-collections
      (= 0 (gch/closures-across-gc 400)))


;; ====================================================================
;; unwinding a heap payload through many frames
;; ====================================================================
;; A freshly allocated payload thrown out through 20 frames, with
;; collections on both sides of the unwind. The catch is the tail of
;; its own helper for the same reason as the other unwind tests here.

(defun gch/thrower (n payload)
  (let ((mine (list n n)))
    (if (< n 1)
        (throw 'gch-deep payload)
        (+ (car mine) (gch/thrower (- n 1) payload)))))

(defun gch/catch-thrown (i)
  (catch 'gch-deep (gch/thrower 20 (list i i i i))))

(defun gch/unwind-payload (rounds)
  (let ((kept (vec)) (total 0))
    (range (i (0 rounds)) (push kept (gch/catch-thrown i)))
    (gc)
    (dolist (p kept) (set total (+ total (car p) (len p))))
    ;; sum of i for i in 0..rounds-1, plus 4 elements per entry
    (if (= total (+ (/ (* (- rounds 1) rounds) 2) (* 4 rounds))) 0 1)))

(test gch-payloads-thrown-through-many-frames-survive
      (= 0 (gch/unwind-payload 400)))


;; ====================================================================
;; suspended continuations abandoned across a collection
;; ====================================================================
;; A continuation is saved VM stack living on the heap; it has to be
;; traced and relocated like anything else. These are captured and
;; abandoned, so they are also garbage the collector must reclaim.

(defun gch/gen () (yield (list 1 2 3)) (yield (list 4 5)) 'fin)

(defun gch/gen-first () (catch 'yield (gch/gen)))

(defun gch/continuations-across-gc (n)
  (let ((bad 0) (total 0))
    (range (i (0 n))
      (let ((r (gch/gen-first)))
        (set total (+ total (len (car r))))
        (if (= 0 (% i 100)) (gc))))
    (gc)
    (unless (= total (* 3 n)) (set bad (+ bad 1)))
    bad))

(test gch-abandoned-continuations-are-reclaimed
      (= 0 (gch/continuations-across-gc 800)))


;; ====================================================================
;; sole-owner barrier with a forced collection
;; ====================================================================
;; Make a container old and black under allocation pressure, then make
;; it the SOLE owner of a fresh value, drop every other path, and
;; collect. If the store did not re-shade the container the value is
;; reclaimed under it.

(defun gch/sole-owner-barrier (rounds)
  (let ((bad 0) (old (make-table)) (tmp nil) (round 0) (i 0))
    (while (< round rounds)
      (set tmp (vec (concat "victim-" round)))
      (set i 0)
      (while (< i 200) (set (get old i) (make-table)) (set i (+ i 1)))
      (set (get old :victim) (get tmp 0))
      (set tmp nil)
      (gc)
      (unless (= (get old :victim) (concat "victim-" round)) (set bad (+ bad 1)))
      (set round (+ round 1)))
    bad))

(test gch-sole-owner-keeps-its-victim-across-gc
      (= 0 (gch/sole-owner-barrier 30)))


;; ====================================================================
;; iterator driven the whole way with collections mid-walk
;; ====================================================================
;; The live-iterator test above grows the sequence underneath a cursor;
;; this one walks a long sequence end to end, collecting every 200
;; steps, and checks both the count and the sum of what came out.

(defun gch/iterator-across-gc (n)
  (let ((bad 0) (v (vec)) (it nil) (seen 0) (sum 0) (x nil))
    (range (i (0 n)) (push v (list i)))
    (set it (iter v))
    (loop
      (set x (next it))
      (if (iter-end? x) (break))
      (set seen (+ seen 1))
      (set sum (+ sum (car x)))
      (range (j (0 8)) (list j j))
      (if (= 0 (% seen 200)) (gc)))
    (unless (= seen n) (set bad (+ bad 1)))
    (unless (= sum (/ (* (- n 1) n) 2)) (set bad (+ bad 1)))
    bad))

(test gch-iterator-walks-a-long-sequence-across-collections
      (= 0 (gch/iterator-across-gc 3000)))


;; ====================================================================
;; chaos - PRNG-driven mix of every mutating operation
;; ====================================================================
;; Everything above tests one shape in isolation. This runs them
;; interleaved, so barriers fire in orders the individual tests never
;; produce.

(defun gch/chaos (rounds)
  (let ((bad 0) (r 0) (v (vec)) (tb (make-table)) (lst nil) (op 0) (k 0))
    (while (< r rounds)
      (set op (gch/rand 10))
      (set k (% r 16))
      (if (= op 0) (push v (vec r (concat "x" r))))
      (if (= op 1) (when (> (len v) 0) (set (get v (% r (len v))) (list r))))
      (if (= op 2) (set (get tb k) (vec r (list r))))
      (if (= op 3) (when (> (len tb) 0) (del tb k)))
      (if (= op 4) (set lst (cons (vec r) lst)))
      (if (= op 5) (set lst (append lst (list r))))
      (if (= op 6) (when (> (len v) 0) (pop v)))
      (if (= op 7) (set v (clone v)))
      (if (= op 8) (gch/churn 30))
      (if (= op 9) (when (> (len v) 1) (reverse! v)))
      ;; invariants that must hold no matter which ops ran
      (unless (= (type-of v) 'vec) (set bad (+ bad 1)))
      (unless (= (type-of tb) 'table) (set bad (+ bad 1)))
      (when (> (len v) 0)
        (unless (get v 0) (set bad (+ bad 1))))
      (if (> (len v) 300) (set v (vec)))
      (if (> (len tb) 300) (set tb (make-table)))
      (set r (+ r 1)))
    bad))

(test gch-interleaved-mutation-chaos
      (= 0 (gch/chaos 3000)))
