;;; A value-position `eval` does not leak a VM stack slot per call.
;;; Pins the loop shape that used to displace a later call frame and
;;; make the VM read a NaN-boxed datum as a code index.

;; A second call frame pushed inside the loop body is half of what the
;; old crash needed: the leaked slots were inert until something else
;; landed on them. It does not have to allocate.
(defun evs/side (n) (+ n 1))

;; `(set got (eval ...))` is the other half - the eval's value has to be
;; USED. A discarded `(eval 1)` proves nothing, because a form in
;; statement position is compiled away and never runs.
(defun evs/leak (n)
  (let ((got nil)
        (r 0))
    (while (< r n)
      (evs/side 7)
      (set got (eval (list 'vec r)))
      (set r (+ r 1)))
    got))

;; A counted loop with no second frame - the old shape that leaked
;; without ever crashing, kept as the control.
(defun evs/leak-alone (n)
  (let ((got nil)
        (r 0))
    (while (< r n)
      (set got (eval (list 'vec r)))
      (set r (+ r 1)))
    got))

;; Anything the loop leaves behind shows up in the NEXT call, so this
;; runs one afterwards and checks it still computes.
(defun evs/leak-then-call (n)
  (let ((v (evs/leak n)))
    (evs/side (len v))))

;; 500 iterations is well past the 139 at which the displaced frame
;; used to fault, and past the 211 of the top-level variant.
(test evs-value-position-eval-survives-a-loop
      (eq? (evs/leak 500) (vec 499))
      (eq? (evs/leak-alone 500) (vec 499))
      (= 2 (evs/leak-then-call 500))
      ;; still correct at the exact old thresholds
      (eq? (evs/leak 139) (vec 138))
      (eq? (evs/leak 211) (vec 210)))

;; The VM stack is sound afterwards: an ordinary call made after the
;; loop returns its own value rather than something left on the stack.
(test evs-stack-is-sound-after-the-loop
      (= 8 (evs/side 7))
      (= 3 (len (list 1 2 3))))
