;;; A chain of generators drained repeatedly with NO explicit collection,
;;; so the collector runs automatically while the whole chain is suspended.
;;; Pins both that it survives and that the values come back intact.

;; Every stage below is a generator resuming the stage under it, so at the
;; moment a collection fires, each one is suspended holding a continuation
;; and the only reference to the stage beneath it. A collection landing
;; there used to follow a pointer that compaction had already moved, and
;; die in the mark phase; the values it walked past are checked too,
;; because a root that is merely mis-marked corrupts rather than crashes.

(defun gac/drain (co)
  (let ((out (vec)))
    (catch 'done (loop (push out (co nil))))
    out))

(defun gac/naturals ()
  (gen (lambda (yi) (let ((i 0)) (loop (yi i) (inc! i))))))

(defun gac/take (co n)
  (gen (lambda (yi) (range (i (0 n)) (yi (co nil))) :end)))

(defun gac/gmap (f co)
  (gen (lambda (yi) (catch 'done (loop (yi (f (co nil))))))))

;; d stages of pass-through stacked on top of the source.
(defun gac/stack (co d)
  (if (= d 0) co (gac/stack (gac/gmap (lambda (x) x) co) (- d 1))))

(defun gac/pipeline (d n)
  (gac/stack (gac/take (gac/naturals) n) d))

;;; ---[ repeated drains with no explicit collection ]-----------------------

;; The count must hold on EVERY drain, not just the first: the fault
;; needed a collection to land mid-drain, which took a few rounds of
;; allocation pressure to happen on its own.

(defun gac/drain-lengths (d n rounds)
  (let ((out (vec)))
    (range (r (0 rounds))
      (push out (len (gac/drain (gac/pipeline d n)))))
    out))

(defun gac/every-drain-full? (d n rounds)
  (let ((ok true))
    (dolist (l (gac/drain-lengths d n rounds))
      (unless (= l n) (set ok nil)))
    ok))

;; Values, not just the count: a stale root that gets marked but not
;; relocated shows up as garbage payloads long before it shows up as a
;; segfault. 0..n-1 passed through d identity stages still sums to
;; n*(n-1)/2.
(defun gac/drain-sum (d n)
  (let ((s 0))
    (dolist (x (gac/drain (gac/pipeline d n))) (set s (+ s x)))
    s))

(defun gac/sums-stay-exact? (d n rounds)
  (let ((ok true)
        (want (/ (* n (- n 1)) 2)))
    (range (r (0 rounds))
      (unless (= want (gac/drain-sum d n)) (set ok nil)))
    ok))

(test gac-repeated-drains-across-automatic-collection
      ;; the filed shape: depth 5, 200 elements, drained 12 times over
      (gac/every-drain-full? 5 200 12)
      (gac/sums-stay-exact? 5 200 12)
      ;; deeper and wider, which used to fail sooner rather than later
      (gac/every-drain-full? 12 400 4)
      (gac/sums-stay-exact? 12 400 4))

;;; ---[ the contrast that identified it ]-----------------------------------

;; Collecting at a point where nothing is suspended was always safe; the
;; bug was only ever about a collection firing DURING a drain. Both
;; orders are pinned so that a regression cannot be mistaken for the
;; explicit-gc path breaking.

(defun gac/drain-with-explicit-gc (d n rounds)
  (let ((ok true))
    (range (r (0 rounds))
      (gc)
      (unless (= n (len (gac/drain (gac/pipeline d n)))) (set ok nil)))
    ok))

;; A collection requested while the chain is halfway through, from the
;; driver, with every stage parked on a yielder call.
(defun gac/gc-mid-drain (d n)
  (let ((co (gac/pipeline d n))
        (out (vec)))
    (range (i (0 10)) (push out (co nil)))
    (gc)
    (range (i (0 10)) (push out (co nil)))
    out))

(test gac-collection-while-suspended
      (gac/drain-with-explicit-gc 5 200 4)
      ;; 20 consecutive naturals, uninterrupted by the collection in the
      ;; middle - the chain resumes where it was parked
      (eq? (vec 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19)
           (gac/gc-mid-drain 5 200)))
