(eval-when :compile
  (sys::load 'stdlib))

(defun sieve (n)
  (let ((field (vec))
        (primes (vec)))
    (range (i (0 (+ n 1)))
           (push field (or)))
    (range (f (2 (+ n 1)))
           (unless (get field f)
             (push primes f)
             (let ((j f))
               (while (<= j n)
                 (set (get field j) (and))
                 (set j (+ j f))))))
    primes))

(println (sieve 100000))
