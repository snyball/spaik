;;; Regression test for the SET(var) write barrier.
;;;

(define wb-set-var-x nil)

(defun wb-set-var-hole-mismatches (rounds)
  (let ((filler (vec))
        (mismatches 0)
        (round 0)
        (i 0))
    (while (< round rounds)
      ;; Allocation pressure to be certain we're inside an active Mark
      ;; cycle (mark_begin already ran this cycle) before the write
      ;; under test.
      (set i 0)
      (while (< i 300)
        (push filler (make-table))
        (set i (+ i 1)))

      ;; The write under test: install a brand new compound value into
      ;; the global `wb-set-var-x`.
      (set wb-set-var-x (list (concat "victim-set-" round) "marker"))

      ;; More allocation pressure to drive the cycle through toward
      ;; sweep/compact - see file header for why no (gc) call here.
      (set i 0)
      (while (< i 600)
        (push filler (make-table))
        (set i (+ i 1)))

      (unless (= (car wb-set-var-x) (concat "victim-set-" round))
        (set mismatches (+ mismatches 1)))

      (set round (+ round 1)))
    mismatches))

(test write-barrier-set-var-mark-hole
      (= 0 (wb-set-var-hole-mismatches 100)))
