;;; Regression test for the APN opcode's (`append`) write barrier.
;;;

(defun wb-apn-hole-mismatches (rounds)
  (let ((box (vec (list "seed")))
        (junk (vec))
        (mismatches 0)
        (round 0)
        (phase 0)
        (p 0))
    (while (< round rounds)
      ;; Victim built and consumed entirely within this `let` - out of
      ;; scope (off self.stack) the instant it returns.
      (let ((expect (concat "v-" round)))
        (set (get box 0) (append (get box 0) (list expect))))

      ;; Burst of varied fresh allocations, AFTER the mutating write,
      ;; BEFORE the check - see file header.
      (set p 0)
      (while (< p phase)
        (push junk (make-table))
        (push junk (concat "noise-" p "-" round))
        (push junk (vec p round phase))
        (set p (+ p 1)))
      (if (> (len junk) 2000) (set junk (vec)))
      (set phase (+ phase 1))
      (if (> phase 40) (set phase 0))

      (unless (= (car (cdr (get box 0))) (concat "v-" round))
        (set mismatches (+ mismatches 1)))

      (set (get box 0) (list "seed"))
      (set round (+ round 1)))
    mismatches))

(test write-barrier-apn-append-mark-hole
      (= 0 (wb-apn-hole-mismatches 5000)))
