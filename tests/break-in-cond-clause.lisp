;;; `break` inside a `cond`/`case` clause breaks the enclosing loop.
;;; Those macros expand to a hidden `loop` of their own, which used to
;;; swallow it. Companion to tests/macro-expansion-errors.lisp.

;; The hidden loop inside `cond` once captured this `break`, so the
;; outer loop ran on to its own unrelated exit and answered
;; `bic-outer`. It must answer `bic-cond`: the clause breaks the loop
;; the programmer can see, not the one the macro generated.
(defun bic/cond-in-loop ()
  (let ((i 0))
    (loop
      (cond
       ((= i 3) (break 'bic-cond))
       (true nil))
      (inc! i)
      (if (> i 6) (break 'bic-outer)))))

;; `case` expands the same way and had the same defect.
(defun bic/case-in-loop ()
  (let ((i 0))
    (loop
      (case i
        (3 (break 'bic-case))
        (true nil))
      (inc! i)
      (if (> i 6) (break 'bic-outer)))))

;; A `cond` whose clauses do NOT break still yields its clause value,
;; and the enclosing loop keeps control - the fix must not turn every
;; cond into a loop exit.
(defun bic/cond-without-break ()
  (let ((i 0) (hits 0))
    (while (< i 10)
      (cond ((= 0 (% i 3)) (set hits (+ hits 1)))
            (true nil))
      (inc! i))
    hits))

;; `cond` used for its VALUE inside a loop, with no break involved.
(defun bic/cond-value-in-loop ()
  (let ((i 0) (total 0))
    (loop
      (set total (+ total (cond ((= 0 (% i 2)) 10) (true 1))))
      (inc! i)
      (if (> i 5) (break total)))))

(test bic-break-reaches-the-visible-loop
      (= 'bic-cond (bic/cond-in-loop))
      (= 'bic-case (bic/case-in-loop)))

(test bic-cond-still-behaves-as-a-conditional
      ;; i = 0,3,6,9 over 0..9
      (= 4 (bic/cond-without-break))
      ;; i counts 0..5 before the break: evens 0,2,4 give 10 each,
      ;; odds 1,3,5 give 1 each -> 33
      (= 33 (bic/cond-value-in-loop)))
