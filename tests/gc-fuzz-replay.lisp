;;; A fixed-seed replay of the randomised collector fuzzer, so the
;;; suite covers the interleaved schedule as well as the one-shape-at-
;;; a-time cases. Seed is hardcoded: this must never be random.

;; The fuzzer proper draws its seed from `(sysrand)` and prints it, so
;; a failing run can be replayed by pasting the seed in. That is the
;; right thing there and the wrong thing here - a test that explores a
;; different schedule every run is a test that fails on someone else's
;; machine and passes on yours. So this file fixes the seed and keeps
;; the operation mix.
(define gfr/state 20259)

;; Under 2^16 so state*25173 stays inside i32; overflow is a checked
;; error in this dialect, not a wrap.
(defun gfr/rand (n)
  (set gfr/state (% (+ (* gfr/state 25173) 13849) 65536))
  (% gfr/state n))

;; ====================================================================
;; nodes
;; ====================================================================
;; (vec :node id payload kids), payload derived from id. A collector
;; that frees a live object or moves one without fixing the pointer to
;; it shows up as a node whose payload no longer matches its own id -
;; a wrong value, which is the only kind of collector failure a program
;; can detect from inside the language.

(define gfr/next-id 0)

(defun gfr/node ()
  (set gfr/next-id (+ gfr/next-id 1))
  (vec :node gfr/next-id (concat "p" gfr/next-id) (vec)))

(defun gfr/node? (x)
  (and (vec? x) (> (len x) 3) (eq? :node (get x 0))))

;; Depth-budgeted rather than visited-set: cycles are built on purpose
;; and often, and a visited set would be a table allocated during the
;; walk, which is the one thing the walk should not do.
(defun gfr/verify (x depth)
  (if (< depth 1)
      0
    (if (gfr/node? x)
        (let ((bad (if (= (get x 2) (concat "p" (get x 1))) 0 1)))
          (dolist (k (get x 3)) (set bad (+ bad (gfr/verify k (- depth 1)))))
          bad)
      (if (vec? x)
          (let ((bad 0))
            (dolist (k x) (set bad (+ bad (gfr/verify k (- depth 1)))))
            bad)
        (if (cons? x)
            (let ((bad 0))
              (dolist (k x) (set bad (+ bad (gfr/verify k (- depth 1)))))
              bad)
          0)))))

;; ====================================================================
;; shapes
;; ====================================================================

(defun gfr/flat (w)
  (let ((n (gfr/node)) (i 0))
    (while (< i w) (push (get n 3) (gfr/node)) (set i (+ i 1)))
    n))

(defun gfr/chain (d)
  (let ((head (gfr/node)) (cur nil) (i 0))
    (set cur head)
    (while (< i d)
      (let ((nx (gfr/node))) (push (get cur 3) nx) (set cur nx))
      (set i (+ i 1)))
    head))

(defun gfr/self-cycle ()
  (let ((n (gfr/node))) (push (get n 3) n) n))

(defun gfr/ring (k)
  (let ((head (gfr/node)) (cur nil) (i 0))
    (set cur head)
    (while (< i k)
      (let ((nx (gfr/node))) (push (get cur 3) nx) (set cur nx))
      (set i (+ i 1)))
    (push (get cur 3) head)
    head))

;; One node under many paths - the shape that makes an unmemoised deep
;; walk exponential rather than linear.
(defun gfr/dag (w)
  (let ((root (gfr/node)) (shared (gfr/node)) (i 0))
    (while (< i w)
      (let ((mid (gfr/node)))
        (push (get mid 3) shared)
        (push (get root 3) mid))
      (set i (+ i 1)))
    root))

;; Reachable only through a closure's captured environment.
(defun gfr/closure ()
  (let ((n (gfr/node)))
    (let ((f (lambda () n)))
      (let ((holder (gfr/node)))
        (push (get holder 3) (vec f))
        holder))))

;; Reachable only through a table value, with the table also under its
;; own key.
(defun gfr/table ()
  (let ((n (gfr/node)) (tb (make-table)) (holder (gfr/node)))
    (set (get tb :child) n)
    (set (get tb :self) tb)
    (push (get holder 3) (vec tb))
    holder))

;; Matrices and short vectors are heap objects with their own layout.
(defun gfr/matrix ()
  (let ((n (gfr/node)))
    (push (get n 3) (vec (mat (vec2 1 2) (vec2 3 4)) (vec4 1 2 3 4) (vec3 5 6 7)))
    n))

;; A cons spine, so the marker walks cdrs rather than vec slots.
(defun gfr/cons-spine (d)
  (let ((c nil) (i 0))
    (while (< i d) (set c (cons (gfr/node) c)) (set i (+ i 1)))
    (let ((holder (gfr/node))) (push (get holder 3) c) holder)))

;; A continuation is saved VM stack living on the heap - a root of a
;; kind no other shape here produces. Captured and never resumed.
(defun gfr/continuation ()
  (let ((n (gfr/node)) (holder (gfr/node)))
    (push (get holder 3) (vec (call/cc (lambda (k) k)) n))
    holder))

;; A large block among small survivors, which is what makes the
;; compactor move things rather than refill holes in place.
(defun gfr/big (w)
  (let ((n (gfr/node)) (big (vec)) (i 0))
    (while (< i w) (push big i) (set i (+ i 1)))
    (push (get n 3) (vec big))
    n))

(defun gfr/make-shape ()
  (let ((w (gfr/rand 11)))
    (if (= w 0) (gfr/flat (+ 1 (gfr/rand 12)))
      (if (= w 1) (gfr/chain (+ 1 (gfr/rand 30)))
        (if (= w 2) (gfr/self-cycle)
          (if (= w 3) (gfr/ring (+ 2 (gfr/rand 8)))
            (if (= w 4) (gfr/dag (+ 2 (gfr/rand 10)))
              (if (= w 5) (gfr/closure)
                (if (= w 6) (gfr/table)
                  (if (= w 7) (gfr/matrix)
                    (if (= w 8) (gfr/cons-spine (+ 1 (gfr/rand 20)))
                      (if (= w 9) (gfr/continuation)
                        (gfr/big (+ 50 (gfr/rand 300)))))))))))))))

(defun gfr/churn (n)
  (let ((s (vec)) (i 0))
    (while (< i n)
      (push s (make-table))
      (push s (vec i (+ i 1)))
      (push s (concat "c-" i))
      (push s (cons i nil))
      (if (> (len s) 300) (set s (vec)))
      (set i (+ i 1)))
    (len s)))

;; ====================================================================
;; the driver
;; ====================================================================
;; A pool of slots, each holding one shape or nothing. Cross-linking
;; two slots is where the interesting cycles come from: the loops that
;; close through two independently-allocated graphs are the ones a
;; single-shape test cannot build.

(define gfr/slots-n 16)

;; A global, so part of the root set is a global slot rather than a
;; stack frame - the two are traced by different code.
(define gfr/parked nil)

(defun gfr/run (rounds)
  (let ((slots (vec)) (bad 0) (r 0) (op 0) (a 0) (b 0))
    (range (i (0 gfr/slots-n)) (push slots nil))
    (while (< r rounds)
      (set op (gfr/rand 100))
      (set a (gfr/rand gfr/slots-n))
      (set b (gfr/rand gfr/slots-n))

      (when (< op 30)
        (set (get slots a) (gfr/make-shape)))

      (when (and (>= op 30) (< op 50))
        (let ((x (get slots a)) (y (get slots b)))
          (when (and (gfr/node? x) (gfr/node? y)) (push (get x 3) y))))

      ;; mutate a payload and put it back. By now the container is old
      ;; and black, so it is the write barrier that has to notice.
      (when (and (>= op 50) (< op 60))
        (let ((x (get slots a)))
          (when (gfr/node? x)
            (set (get x 2) (concat "tmp" (get x 1)))
            (set (get x 2) (concat "p" (get x 1))))))

      (when (and (>= op 60) (< op 70))
        (set (get slots a) nil))

      (when (and (>= op 70) (< op 73))
        (let ((x (get slots a)))
          (when (and (gfr/node? x) (> (len (get x 3)) 1))
            (reverse! (get x 3)))))

      (when (and (>= op 73) (< op 76))
        (set gfr/parked (get slots a))
        (gfr/churn 20)
        (set gfr/parked nil))

      (when (and (>= op 76) (< op 85))
        (gfr/churn (+ 10 (gfr/rand 40))))

      (when (and (>= op 85) (< op 93))
        (gc))

      (when (>= op 93)
        (dolist (s slots) (set bad (+ bad (gfr/verify s 20)))))

      (set r (+ r 1)))

    (gc)
    (gc)
    (dolist (s slots) (set bad (+ bad (gfr/verify s 20))))
    bad))

(test gfr-fixed-seed-fuzz-replay
      (= 0 (gfr/run 1200)))
