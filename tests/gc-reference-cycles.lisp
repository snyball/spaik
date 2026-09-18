;;; A reference cycle that is live when a collection runs is collectable.
;;; Cycles closing through vec and cons used to spin `(gc)` forever and
;;; pinned `total_frees` at 0 for the rest of the process.

;; Every helper drops its cycle before returning. Test files share one
;; global environment, so a cycle left in a global would be reachable
;; from every later collection in the suite.


(defun gcy/vec-self-cycle ()
  (let ((v (vec)))
    (push v v)
    (gc)
    (set v nil)
    :collected))

(defun gcy/vec-cons-cycle ()
  (let ((v (vec))
        (c (cons 1 nil)))
    (push v c)
    (push v v)
    (gc)
    (set v nil)
    (set c nil)
    :collected))

(defun gcy/table-cycle ()
  (let ((tb (make-table)))
    (set (get tb :self) tb)
    (gc)
    (set tb nil)
    :collected))

;; The symptom was a non-terminating collection, so the assertion that
;; matters is only that the call RETURNS. A regression hangs the suite
;; rather than failing it - there is no way to time-box a call from
;; inside the language.
(test gcy-cycle-through-vec-collects
      (eq? :collected (gcy/vec-self-cycle)))

(test gcy-cycle-through-vec-and-cons-collects
      (eq? :collected (gcy/vec-cons-cycle)))

;; A cycle closing through a table always terminated: tables descend by
;; calling the mark routine, which has an already-marked guard, while
;; vec and cons went through a worklist that had none.
(test gcy-cycle-through-table-collects
      (eq? :collected (gcy/table-cycle)))
