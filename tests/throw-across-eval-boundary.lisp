;;; A `throw` that unwinds across an `eval` boundary, in tail and first
;;; argument position. Used to leave the VM stack one element short.
;;; Companion to tests/throw-past-catch-stack-pointer-leak.lisp.

;; The bare shape. `(catch 'k (progn (throw 'k 1)))` was always clean;
;; putting an `eval` between the throw and the catch was not, and the
;; damage showed up later as re-executed top-level forms and a
;; "Stack Error: expected 1 stack elements, but got 0".
(defun tae/one () (catch 'tae-k (eval '(throw 'tae-k 1))))

;; Reference arguments on the frame that unwinds: these are the slots
;; that were stranded, so the arity of the helper mattered.
(defun tae/one-ref (s)    (catch 'tae-k (eval '(throw 'tae-k 7))))
(defun tae/two-refs (a b) (catch 'tae-k (eval '(throw 'tae-k 7))))

;; Slot reuse after the unwind. A counter landing on a stranded slot
;; used to be compared against whatever string was left there.
(defun tae/sum-after ()
  (tae/one)
  (let ((i 0) (n 0))
    (loop (if (not (< i 5)) (break))
          (set n (+ n i))
          (inc! i))
    n))

;; `dolist` binds two slots, so a one-slot displacement handed `next`
;; the wrong binding.
(defun tae/dolist-after ()
  (tae/one)
  (let ((n 0))
    (dolist (x '(1 2 3))
      (set n (+ n x)))
    n))

;; The leak accumulated one region per call: 200 rounds of all three
;; arities, then check an ordinary loop still computes the right sum.
(defun tae/many (rounds)
  (let ((r 0))
    (loop (if (not (< r rounds)) (break))
          (tae/one)
          (tae/one-ref "stranded-string")
          (tae/two-refs "stranded-a" "stranded-b")
          (inc! r)))
  (tae/sum-after))

;; Recursive higher-order consumer, the shape that aborted on an
;; out-of-bounds stack index for the non-`eval` version of this bug.
(defun tae/filter-count (n)
  (len (filter tae/one-ref (range-list 0 n))))

;; FIRST argument position is correct too - the throw's value arrives
;; and the arguments after it are still evaluated. A LATER argument
;; position is NOT correct in this build: the earlier slots come back
;; as raw untyped memory, which is a separate open bug and deliberately
;; not asserted here.
(defun tae/first-arg ()
  (catch 'tae-k (list (eval '(throw 'tae-k 3)) :b)))

(test throw-across-eval-boundary
      ;; the value the throw carries
      (= 1 (tae/one))
      (= 7 (tae/one-ref "stranded-string"))
      (= 7 (tae/two-refs "stranded-a" "stranded-b"))
      ;; slot reuse after the unwind
      (= 10 (tae/sum-after))
      (= 6 (tae/dolist-after))
      ;; accumulation across many calls
      (= 10 (tae/many 200))
      ;; recursive consumer
      (= 300 (tae/filter-count 300))
      ;; first argument position
      (eq? 3 (tae/first-arg)))
