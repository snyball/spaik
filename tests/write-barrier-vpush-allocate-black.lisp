;;; Regression test for the VPUSH/VSET write-barrier

(defun wb-vpush-allocate-black-mismatches (rounds)
  (let ((a (vec))
        (tmp (vec))
        (wrapper nil)
        (wrapper-idx 0)
        (mismatches 0)
        (round 0)
        (i 0))
    (while (< round rounds)
      ;; Give the victim payload a life of its own, reachable only via
      ;; `tmp` for now.
      (set tmp (vec (concat "victim-payload-" round)))

      ;; Allocation pressure so `a` (a persistent, already-on-stack
      ;; root for the whole function call) gets fully traced/Black
      ;; before the interesting write below.
      (set i 0)
      (while (< i 300)
        (push a (make-table))
        (set i (+ i 1)))

      ;; A brand-new compound ("wrapper") whose only child is the
      ;; victim payload - allocated fresh, born Black, never
      ;; independently traced at allocation time.
      (set wrapper (vec (get tmp 0)))

      ;; Drop the old path - the ONLY remaining reference to the victim
      ;; payload is now inside `wrapper`.
      (set tmp (vec))

      ;; The write under test: VPUSH `wrapper` (Black-at-birth,
      ;; untraced) into `a` (with high probability already Black this
      ;; cycle, given the allocation pressure above).
      (set wrapper-idx (len a))
      (push a wrapper)

      ;; More allocation pressure to drive the cycle on toward
      ;; sweep/compact - deliberately no (gc) call anywhere in this
      ;; file: Arena::full_collection, invoked mid-cycle, forces an
      ;; extra fresh mark_begin() that would legitimately re-scan `a`
      ;; from scratch and incidentally "heal" the exact hole under
      ;; test, independent of whether VPUSH's own barrier works. Rely
      ;; purely on the ordinary per-instruction incremental collect()
      ;; tick instead.
      (set i 0)
      (while (< i 300)
        (push a (make-table))
        (set i (+ i 1)))

      (unless (= (get (get a wrapper-idx) 0)
                 (concat "victim-payload-" round))
        (set mismatches (+ mismatches 1)))

      (set round (+ round 1)))
    mismatches))

(test write-barrier-vpush-allocate-black
      (= 0 (wb-vpush-allocate-black-mismatches 300)))
