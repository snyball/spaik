(test filter
      (eq? (filter (lambda (x) (= x 2))
                   '(1 2 3))
           '(2))
      (eq? (filter (lambda (x) (and (>= x 30)
                                    (< x 60)))
                   (range-list 0 100))
           (range-list 30 60)))

(test reverse
      (eq? (reverse '(1 2 3 4 5))
           '(5 4 3 2 1))
      (eq? (reverse (reverse (range-list 0 100)))
           (range-list 0 100)))

(test elem?
      (elem? 5 (range-list 0 10))
      (nil? (elem? 5 (range-list 0 3))))

(test all?
      (all? (lambda (x) (<= 1 x)) (range-list 1 10))
      (not (all? (lambda (x) (< x 10)) (range-list 1 11))))

(test any?
      (any? (lambda (x) (= x 9)) (range-list 0 10))
      (not (any? (lambda (x) (= x 9)) (range-list 0 9))))
