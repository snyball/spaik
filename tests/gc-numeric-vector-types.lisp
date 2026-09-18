;;; mat2/3/4 and vec2/3/4 are heap objects too. Same barrier and
;;; survival shapes the general collector tests use, on the one family
;;; of reference types they never touch.

(defun gnv/churn (n)
  (let ((s (vec)) (i 0))
    (while (< i n)
      (push s (vec i))
      (push s (make-table))
      (if (> (len s) 200) (set s (vec)))
      (set i (+ i 1)))
    (len s)))

;; Components come back as floats whatever went in, so every comparison
;; here is against a float. `=` is type-strict: (= 7.0 7) is false.
(defun gnv/build (i)
  (vec (mat (vec2 i 1) (vec2 2 3))
       (vec4 i 1 2 3)
       (vec3 i 5 6)
       (mat (vec4 i 0 0 0) (vec4 0 1 0 0) (vec4 0 0 1 0) (vec4 0 0 0 1))))

(defun gnv/check (e i)
  (let ((bad 0))
    (unless (eq? 'mat2 (type-of (get e 0))) (set bad (+ bad 1)))
    (unless (eq? 'vec4 (type-of (get e 1))) (set bad (+ bad 1)))
    (unless (eq? 'mat4 (type-of (get e 3))) (set bad (+ bad 1)))
    (unless (= (get (get e 2) 0) (* 1.0 i)) (set bad (+ bad 1)))
    (unless (= (get (get e 2) 1) 5.0) (set bad (+ bad 1)))
    bad))

;; ====================================================================
;; held in a container across two forced collections
;; ====================================================================

(defun gnv/survive (n)
  (let ((keep (vec)) (bad 0) (i 0))
    (while (< i n) (push keep (gnv/build i)) (set i (+ i 1)))
    (gc)
    (gc)
    (set i 0)
    (while (< i n)
      (set bad (+ bad (gnv/check (get keep i) i)))
      (set i (+ i 1)))
    bad))

(test gnv-matrices-and-short-vectors-survive-collection
      (= 0 (gnv/survive 1500)))


;; ====================================================================
;; installed into an already-Black container - the write barrier
;; ====================================================================
;; Same shape as the general barrier tests: build the victim through a
;; temporary, allocate hard so the destination is old, store, drop
;; every other path, allocate hard again, read it back. No (gc) here
;; on purpose - a forced collection re-scans roots and would heal the
;; hole under test.

(defun gnv/barrier (rounds)
  (let ((bad 0) (r 0) (slots (vec 0 0 0 0 0 0 0 0)) (tmp nil) (k 0))
    (while (< r rounds)
      (set tmp (gnv/build r))
      (gnv/churn 80)
      (set k (% r 8))
      (set (get slots k) tmp)
      (set tmp nil)
      (gnv/churn 80)
      (set bad (+ bad (gnv/check (get slots k) r)))
      (set r (+ r 1)))
    bad))

(test gnv-barrier-installs-a-matrix-into-a-black-vec
      (= 0 (gnv/barrier 200)))


;; ====================================================================
;; garbage of this family is actually reclaimed
;; ====================================================================
;; Twenty thousand short-lived matrices, all dropped, then collected.
;; A collector that never freed them would still pass the survival test
;; above; this one fails if the heap only grows. The claim is deliberately
;; weak - that a later identical burst still works - because the exact
;; residency is not something a test should pin.

(defun gnv/reclaimed (n)
  (let ((keep (vec)) (i 0))
    (while (< i n) (push keep (gnv/build i)) (set i (+ i 1)))
    (set keep nil)
    (gc)
    (set keep (vec))
    (set i 0)
    (while (< i n) (push keep (gnv/build i)) (set i (+ i 1)))
    (let ((bad (gnv/check (get keep (- n 1)) (- n 1))))
      (set keep nil)
      (gc)
      bad)))

(test gnv-matrix-garbage-is-reclaimed
      (= 0 (gnv/reclaimed 10000)))
