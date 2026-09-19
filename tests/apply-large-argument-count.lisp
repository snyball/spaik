;;; `apply` accepts argument counts at and past 2^16. The exact boundary
;;; used to raise a raw "out of range integral type conversion attempted".
;;; The sums are asserted too, so a silent u16 truncation still fails here.

(defun apc/ones (n)
  (let ((v (vec)) (i 0))
    (while (< i n)
      (push v 1)
      (set i (+ i 1)))
    v))

(defun apc/sum-ones (n) (apply + (apc/ones n)))

;; 65535 always worked; 65536 is the count that raised; 65537 rules out the
;; limit having merely moved by one rather than gone.
(test apc-apply-at-the-u16-boundary
      (= 65535 (apc/sum-ones 65535))
      (= 65536 (apc/sum-ones 65536))
      (= 65537 (apc/sum-ones 65537)))

;; Well past the boundary. A count truncated to u16 would not just raise -
;; it could also sum the wrong number of arguments, which this would catch:
;; 100000 truncated to 16 bits is 34464.
(test apc-apply-well-past-the-u16-boundary
      (= 100000 (apc/sum-ones 100000)))
