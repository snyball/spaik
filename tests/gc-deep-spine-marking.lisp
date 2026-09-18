;;; How deep a structure the COLLECTOR can walk, as against the other
;;; deep walks in the system. The marker is iterative; several of the
;;; others are not, and that contrast is the point of this file.

;; A vec-in-vec spine one million levels deep, marked twice. The
;; collector's own tests elsewhere stop at a few hundred levels; this
;; is here to pin that the limit is not a few hundred, so that a
;; regression to a recursive marker is a failing test rather than a
;; crash in some unrelated program that happened to nest deeply.
(defun gds/vec-spine (d)
  (let ((s (vec "bottom")) (i 0))
    (while (< i d) (set s (vec s i)) (set i (+ i 1)))
    s))

(defun gds/mark-vec-spine (d)
  (let ((s (gds/vec-spine d)))
    (gc)
    (gc)
    ;; walk back down far enough to prove the pointers are still real
    (let ((p s) (i 0))
      (while (< i d) (set p (get p 0)) (set i (+ i 1)))
      (get p 0))))

;; The same claim for a cons spine, in both directions: a cdr chain and
;; a car chain reach the marker through different fields.
(defun gds/cdr-spine (d)
  (let ((c nil) (i 0))
    (while (< i d) (set c (cons i c)) (set i (+ i 1)))
    c))

(defun gds/car-spine (d)
  (let ((c 0) (i 0))
    (while (< i d) (set c (cons c nil)) (set i (+ i 1)))
    c))

(defun gds/mark-cdr-spine (d)
  (let ((c (gds/cdr-spine d)))
    (gc)
    (let ((p c) (n 0))
      (while p (set p (cdr p)) (set n (+ n 1)))
      n)))

(defun gds/mark-car-spine (d)
  (let ((c (gds/car-spine d)))
    (gc)
    (let ((p c) (n 0))
      (while (cons? p) (set p (car p)) (set n (+ n 1)))
      n)))

;; 200k rather than the million that also works: the suite has to stay
;; quick, and the shape of the claim does not change with the number.
(test gds-collector-walks-a-deep-spine
      (= "bottom" (gds/mark-vec-spine 200000))
      (= 200000 (gds/mark-cdr-spine 200000))
      (= 200000 (gds/mark-car-spine 200000)))

;; The contrast. `clone` and the printer walk the SAME structures
;; recursively and die on a fraction of this depth, which is why the
;; numbers here are so much smaller. Those are open bugs, pinned
;; elsewhere as crashes; what is asserted here is only that the
;; collector is not one of them - a depth both walks survive, marked,
;; is still intact afterwards.
(defun gds/shallow-both-survive (d)
  (let ((s (gds/vec-spine d)))
    (let ((c (clone s)))
      (gc)
      (let ((p c) (i 0))
        (while (< i d) (set p (get p 0)) (set i (+ i 1)))
        (get p 0)))))

(test gds-a-depth-clone-survives-is-marked-too
      (= "bottom" (gds/shallow-both-survive 100)))
