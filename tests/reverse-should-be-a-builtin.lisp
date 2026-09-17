(defun rev-via-value (xs)      (let ((f reverse))  (f xs)))
(defun rev-bang-via-value (xs) (let ((f reverse!)) (f xs)))

(test reverse-handles-every-sequence-type
      ;; cons lists: the case that always worked
      (eq? (reverse (list 1 2 3)) (list 3 2 1))
      (eq? (reverse (reverse (list 1 2 3))) (list 1 2 3))
      (nil? (reverse nil))
      ;; vec: the case that used to raise a Type Error
      (eq? (reverse (vec 1 2 3)) (vec 3 2 1))
      (eq? (reverse (reverse (vec 1 2 3))) (vec 1 2 3))
      (eq? (reverse (vec)) (vec))
      ;; `collect` results are always a vec - the idiom that was broken
      (eq? (reverse (collect (iter (vec 10 20 30)))) (vec 30 20 10))
      ;; strings too
      (eq? (reverse "abc") "cba")
      ;; usable as a first-class value
      (eq? (rev-via-value (vec 1 2)) (vec 2 1)))

(define rev-v (vec 1 2 3))
(define rev-v-ret (reverse! rev-v))

(test reverse-bang-reverses-a-vec-in-place
      ;; `reverse!` exists at all (it was `Undefined Variable: reverse!`)
      (eq? rev-v (vec 3 2 1))
      ;; and it is genuinely in place - the return value IS the input
      (= rev-v-ret rev-v)
      (eq? (reverse! (list 1 2 3)) (list 3 2 1))
      (eq? (rev-bang-via-value (vec 1 2)) (vec 2 1)))
