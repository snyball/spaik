;;; Every `c[ad]+r` accessor against the `car`/`cdr` chain it abbreviates.
;;; The tree is a full binary cons tree four levels deep, so all 28
;;; compound accessors are in range.

;; Read an accessor's letters right to left: `cadr` is `(car (cdr x))`.
;; The fixture is built once so `=` (reference equality) can be used -
;; two routes to the same node must return the SAME object, which is a
;; stricter check than `eq?` would give.
(define cxr-tree
  (cons (cons (cons (cons 1 2) (cons 3 4)) (cons (cons 5 6) (cons 7 8)))
        (cons (cons (cons 9 10) (cons 11 12)) (cons (cons 13 14) (cons 15 16)))))

(test cxr-two-letter-accessors
      (= (caar cxr-tree) (car (car cxr-tree)))
      (= (cadr cxr-tree) (car (cdr cxr-tree)))
      (= (cdar cxr-tree) (cdr (car cxr-tree)))
      (= (cddr cxr-tree) (cdr (cdr cxr-tree))))

(test cxr-three-letter-accessors
      (= (caaar cxr-tree) (car (car (car cxr-tree))))
      (= (caadr cxr-tree) (car (car (cdr cxr-tree))))
      (= (cadar cxr-tree) (car (cdr (car cxr-tree))))
      (= (caddr cxr-tree) (car (cdr (cdr cxr-tree))))
      (= (cdaar cxr-tree) (cdr (car (car cxr-tree))))
      (= (cdadr cxr-tree) (cdr (car (cdr cxr-tree))))
      (= (cddar cxr-tree) (cdr (cdr (car cxr-tree))))
      (= (cdddr cxr-tree) (cdr (cdr (cdr cxr-tree)))))

(test cxr-four-letter-accessors
      (= (caaaar cxr-tree) (car (car (car (car cxr-tree)))))
      (= (caaadr cxr-tree) (car (car (car (cdr cxr-tree)))))
      (= (caadar cxr-tree) (car (car (cdr (car cxr-tree)))))
      (= (caaddr cxr-tree) (car (car (cdr (cdr cxr-tree)))))
      (= (cadaar cxr-tree) (car (cdr (car (car cxr-tree)))))
      (= (cadadr cxr-tree) (car (cdr (car (cdr cxr-tree)))))
      (= (caddar cxr-tree) (car (cdr (cdr (car cxr-tree)))))
      (= (cadddr cxr-tree) (car (cdr (cdr (cdr cxr-tree)))))
      (= (cdaaar cxr-tree) (cdr (car (car (car cxr-tree)))))
      (= (cdaadr cxr-tree) (cdr (car (car (cdr cxr-tree)))))
      (= (cdadar cxr-tree) (cdr (car (cdr (car cxr-tree)))))
      (= (cdaddr cxr-tree) (cdr (car (cdr (cdr cxr-tree)))))
      (= (cddaar cxr-tree) (cdr (cdr (car (car cxr-tree)))))
      (= (cddadr cxr-tree) (cdr (cdr (car (cdr cxr-tree)))))
      (= (cdddar cxr-tree) (cdr (cdr (cdr (car cxr-tree)))))
      (= (cddddr cxr-tree) (cdr (cdr (cdr (cdr cxr-tree)))))
      (= 1 (caaaar cxr-tree)))
