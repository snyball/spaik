(let ((x 1000000))
  (loop (if (= x 0)
            (break))
        (set x (- x 1))))
