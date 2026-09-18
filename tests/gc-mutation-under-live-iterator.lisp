;;; Collections while an iterator's cursor is live and the sequence
;;; underneath it is growing, shrinking or losing keys.
;;; Pins what the cursor does, not what it ought to do.

;; ====================================================================
;; a table that grows while it is being iterated
;; ====================================================================
;; New keys are added every fifth step, with a collection right after,
;; so the rehash and the collection both happen under the cursor. The
;; walk still visits each of the ORIGINAL keys exactly once and stops;
;; the keys added during the walk are in the table but are not visited.

(defun gmi/table-grows (n)
  (let ((tb (make-table)) (seen 0) (x nil))
    (range (i (0 n)) (set (get tb i) (vec i (concat "t" i))))
    (let ((it (iter tb)))
      (loop
        (set x (next it))
        (if (iter-end? x) (break))
        (set seen (+ seen 1))
        (when (= 0 (% seen 5))
          (set (get tb (+ n seen)) (vec seen))
          (gc))))
    (list seen (len tb))))

;; ====================================================================
;; a table losing the key that was just yielded
;; ====================================================================
;; Every third key is deleted as soon as it comes out, then collected.
;; All n keys are still visited, and n/3 of them are gone afterwards.

(defun gmi/table-deletes (n)
  (let ((tb (make-table)) (seen 0) (x nil))
    (range (i (0 n)) (set (get tb i) (vec i)))
    (let ((it (iter tb)))
      (loop
        (set x (next it))
        (if (iter-end? x) (break))
        (set seen (+ seen 1))
        (when (= 0 (% seen 3)) (del tb x) (gc))))
    (list seen (len tb))))

;; ====================================================================
;; a vec shrinking under the cursor
;; ====================================================================
;; Popping the tail while walking from the front makes the two meet in
;; the middle: 20 elements, one popped every second step, walk ends
;; after 14 with 13 left. The interest is that it ENDS - a cursor
;; compared against a stale length would run off the end.

(defun gmi/vec-shrinks (n)
  (let ((v (vec)) (seen 0) (x nil))
    (range (i (0 n)) (push v (vec i)))
    (let ((it (iter v)))
      (loop
        (set x (next it))
        (if (iter-end? x) (break))
        (set seen (+ seen 1))
        (when (= 0 (% seen 2)) (pop v) (gc))))
    (list seen (len v))))

;; The whole sequence emptied at once, mid-walk, and collected. The
;; walk stops at the step after, rather than reading freed storage.
(defun gmi/vec-emptied (n)
  (let ((v (vec)) (seen 0) (x nil))
    (range (i (0 n)) (push v (vec i)))
    (let ((it (iter v)))
      (loop
        (set x (next it))
        (if (iter-end? x) (break))
        (set seen (+ seen 1))
        (when (= seen 3)
          (range (j (0 n)) (pop v))
          (gc))))
    (list seen (len v))))

(test gmi-sequences-mutated-under-a-live-cursor
      (eq? '(40 48) (gmi/table-grows 40))
      (eq? '(30 20) (gmi/table-deletes 30))
      (eq? '(14 13) (gmi/vec-shrinks 20))
      (eq? '(3 0) (gmi/vec-emptied 20)))
