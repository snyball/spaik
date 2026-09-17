;; A `,` one level in stays unevaluated.
(defun nqd-depth2-comma () `(a `(b ,(+ 1 2))))

;; `,@` one level in behaves the same way.
(defun nqd-depth2-splice () `(a `(b ,@(list 1 2))))

;; The inner marker is a proper `quasiquote`, not a bare backquote symbol.
(defun nqd-inner-marker () (car (cadr `(a `(b 1)))))

;; Single-level quasiquote still evaluates normally (the controls).
(define nqd-n 3)
(defun nqd-level1-unquote () `(a ,nqd-n))
(defun nqd-level1-splice  () `(a ,@(list 1 2 3)))

(defmacro nqd-mk (name) `(defmacro ,name (x) `(+ ,x 1)))
(nqd-mk nqd-addone)

;; Two levels of generated macro, to check depth tracking holds when
;; the outer expansion itself produces another quasiquote.
(defmacro nqd-mk2 (name) `(defmacro ,name (y) `(* ,y 2)))
(nqd-mk2 nqd-double)

(test nested-quasiquote-depth
      ;; depth 2: suppressed, and the inner backquote survives as a marker
      (eq? (nqd-depth2-comma)
           (list 'a (list 'quasiquote (list 'b (list 'unquote (list '+ 1 2))))))
      (eq? (nqd-depth2-splice)
           (list 'a (list 'quasiquote
                          (list 'b (list 'unquote-splicing (list 'list 1 2))))))
      ;; the regression was this coming back as a bare backquote symbol
      ;; rather than the `quasiquote` marker
      (eq? (nqd-inner-marker) 'quasiquote)
      (eq? (type-of (nqd-inner-marker)) 'symbol)
      ;; level 1 still evaluates
      (eq? (nqd-level1-unquote) (list 'a 3))
      (eq? (nqd-level1-splice) (list 'a 1 2 3))
      ;; macro-defining macros work
      (= (nqd-addone 4) 5)
      (= (nqd-addone 0) 1)
      (= (nqd-double 21) 42))
