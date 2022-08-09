(define (<ξ>::defun name args &body body)
  `(define (,name ,@args) ,@body))
(eval-when :compile
  (set-macro 'defun '<ξ>::defun))

(defun <ξ>::defmacro (name args &body body)
  (let ((mac-fn-name (make-symbol (concat '<ξ>:: name))))
    `(progn
       (define (,mac-fn-name ,@args)
         ,@body)
       (eval-when :compile
         (set-macro ',name ',mac-fn-name)))))
(eval-when :compile
  (set-macro 'defmacro '<ξ>::defmacro))

(defun head (x)
  (car x))
(defun tail (x)
  (cdr x))
(defun caar (x)
  (car (car x)))
(defun cadr (x)
  (car (cdr x)))
(defun cdar (x)
  (cdr (car x)))
(defun cddr (x)
  (cdr (cdr x)))
(defun caaar (x)
  (car (car (car x))))
(defun caadr (x)
  (car (car (cdr x))))
(defun cadar (x)
  (car (cdr (car x))))
(defun caddr (x)
  (car (cdr (cdr x))))
(defun cdaar (x)
  (cdr (car (car x))))
(defun cdadr (x)
  (cdr (car (cdr x))))
(defun cddar (x)
  (cdr (cdr (car x))))
(defun cdddr (x)
  (cdr (cdr (cdr x))))
(defun caaaar (x)
  (car (car (car (car x)))))
(defun caaadr (x)
  (car (car (car (cdr x)))))
(defun caadar (x)
  (car (car (cdr (car x)))))
(defun caaddr (x)
  (car (car (cdr (cdr x)))))
(defun cadaar (x)
  (car (cdr (car (car x)))))
(defun cadadr (x)
  (car (cdr (car (cdr x)))))
(defun caddar (x)
  (car (cdr (cdr (car x)))))
(defun cadddr (x)
  (car (cdr (cdr (cdr x)))))
(defun cdaaar (x)
  (cdr (car (car (car x)))))
(defun cdaadr (x)
  (cdr (car (car (cdr x)))))
(defun cdadar (x)
  (cdr (car (cdr (car x)))))
(defun cdaddr (x)
  (cdr (car (cdr (cdr x)))))
(defun cddaar (x)
  (cdr (cdr (car (car x)))))
(defun cddadr (x)
  (cdr (cdr (car (cdr x)))))
(defun cdddar (x)
  (cdr (cdr (cdr (car x)))))
(defun cddddr (x)
  (cdr (cdr (cdr (cdr x)))))

(defmacro while (cnd &body body)
  `(loop
    (if (not ,cnd)
        (break))
    ,@body))

(defmacro until (cnd &body body)
  `(loop
    (if ,cnd (break))
    ,@body))

(defmacro inc! (var &? n)
  (let ((num (or n 1)))
    `(set ,var (+ ,var ,num))))

(defmacro dec! (var &? n)
  (let ((num (or n 1)))
    `(set ,var (- ,var ,num))))

(defmacro defvar (name value)
  `(intr::define-static ,name ,value))

(defun gensym ()
  (defvar num-syms 0)
  (let ((sym (make-symbol (concat "<β>::#" num-syms))))
    (inc! num-syms)
    sym))

(defmacro when (cnd &body if-true)
  `(if ,cnd
       (progn
         ,@if-true)))

(defmacro unless (cnd &body if-false)
  `(if (not ,cnd)
       (progn
         ,@if-false)))

(defmacro set* (to from)
  (let ((let-set nil)
        (set-set nil))
    (while to
      (let ((tmp-sym (gensym)))
        (set let-set (cons `(,tmp-sym ,(car from)) let-set))
        (set set-set (cons `(set ,(car to) ,tmp-sym) set-set)))
      (set to (cdr to))
      (set from (cdr from)))
    `(let ,let-set
       ,@set-set)))

(defun let*/helper (pairs body)
  (if pairs
      `(let (,(car pairs))
         ,(let*/helper (cdr pairs) body))
    `(progn ,@body)))

(defmacro let* (pairs &body body)
  (let*/helper pairs body))

(defun math/fibonacci (n)
  (let ((a 0) (b 1))
    (while (> n 0)
      (set* (a b) (b (+ a b)))
      (dec! n))
    a))

(defun math/factorial (n)
  (let ((x 1))
    (while (> n 0)
      (set* (x n) ((* x n) (- n 1))))
    x))

(defmacro ++ (var)
  (let ((val (gensym)))
    `(let ((,val ,var))
       (inc! ,var)
       ,val)))

(defmacro -- (var)
  (let ((val (gensym)))
    `(let ((,val ,var))
       (dec! ,var)
       ,val)))

(defun count! ()
  (defvar cnt 0)
  (++ cnt))

(defmacro alias (alias-name name)
  `(defmacro ,alias-name (&rest r)
     (cons ',name r)))

(defmacro fn-alias (alias-name args name)
  `(defun ,alias-name ,args
     (,name ,@args)))

;; Turn (f a b c d) into (f a (f b (f c d)))
(defun <ξ>::2-ary-to-n-ary/helper (fn args)
  (if (and args (cdr args))
      `(,fn ,(car args)
            ,(<ξ>::2-ary-to-n-ary/helper
              fn
              (cdr args)))
      (car args)))

(defmacro 2-ary-to-n-ary (fn alias)
  `(defmacro ,alias (&rest args)
     (<ξ>::2-ary-to-n-ary/helper ',fn
                                 args)))

(defun _load (lib)
  (load lib))

(defmacro load (lib)
  `(eval-when :compile
     (_load ,lib)))

;;; FIXME: (next)/(break) don't work inside dolist/range,
;;;        a compiler built-in is needed to fix it.

(defmacro dolist (cnd &body body)
  (let ((name (car cnd))
        (init (car (cdr cnd)))
        (xs (gensym)))
    `(let ((,name nil)
           (,xs ,init))
       (while ,xs
         (set ,name (car ,xs))
         ,@body
         (set ,xs (cdr ,xs))))))

(defmacro for (cnd &body body)
  (let ((name (car cnd))
        (init (car (cdr cnd)))
        (sentinel '<ζ>::iter-stop)
        (it (gensym)))
    `(let ((,name nil)
           (,it (iter ,init)))
       (loop (set ,name (next ,it))
             (if (= ,name ',sentinel) (break))
             ,@body))))

(defmacro range (cnd &body body)
  (let ((loop-var (car cnd))
        (min (caadr cnd))
        (max (cadadr cnd)))
    `(let ((,loop-var ,min))
       (while (< ,loop-var ,max)
              ,@body
              (inc! ,loop-var)))))

(defun range-list (a b)
  (let ((xs nil))
    (range (x (a b))
      (set xs (cons x xs)))
    (reverse xs)))

(defmacro ignore (&body code)
  `(progn ,@code nil))

(defmacro take! (var)
  (let ((head (gensym)))
    `(let ((,head (car ,var)))
       (set ,var (cdr ,var))
       ,head)))

(defun map (f xs)
  (when xs
    (cons (f (car xs))
          (map f (cdr xs)))))

(defun filter (f xs)
  (when xs
    (let ((x (car xs)))
      (if (f x)
          (cons x (filter f (cdr xs)))
        (filter f (cdr xs))))))

(defun zip (xs ys)
  (when (and xs ys)
    (cons (cons (car xs)
                (car ys))
          (zip (cdr xs)
               (cdr ys)))))

(defun reverse (xs)
  (let ((ys nil))
    (dolist (x xs)
      (set ys (cons x ys)))
    ys))

(defun all? (f xs)
  (not
   (dolist (x xs)
     (unless (f x)
       (break (and))))))

(defun any? (f xs)
  (dolist (x xs)
    (when (f x)
      (break (and)))))

(defun elem? (x ys)
  (dolist (y ys)
    (when (= x y)
      (break (and)))))

(defmacro extreme-value (ord src)
  (let ((m (gensym)) (xs (gensym)) (x (gensym)))
    `(let ((,m (car ,src))
           (,xs (cdr ,src)))
       (dolist (,x ,xs)
         (when (,ord ,x ,m)
           (set ,m ,x)))
       ,m)))

(defun min (xs)
  (extreme-value < xs))

(defun max (xs)
  (extreme-value > xs))

(defun sum (xs)
  (let ((s 0))
    (dolist (x xs)
      (inc! s x))
    s))

(define (pow a b)
  (let ((s 1))
    (range (_ (0 b))
      (set s (* s a)))
    s))

(defun abs (x)
  (if (< x 0)
      (- x)
    x))

(defun mean (xs)
  (/ (sum xs) (len xs)))

(defun id (x)
  x)

(defmacro m-map (m xs)
  (let ((p '()))
    (dolist (x xs)
      (set p (cons `(,m ,x) p)))
    `(progn ,@(reverse p))))

(defmacro make-tcheck (type)
  (let ((name (make-symbol (concat type '?))))
    `(defun ,name (x)
       (= (type-of x) ',type))))

(m-map make-tcheck (integer symbol
                    unsigned-integer
                    float bool
                    string cons))

(defun number? (x)
  (or (integer? x)
      (float? x)))

(defun nil? (x)
  (= x nil))


(defun equal-cons? (as bs)
  (loop (when (or (= as nil)
                  (= bs nil))
          (break (= as bs)))
   (unless (equal? (car as) (car bs))
     (break false))
   (set as (cdr as))
   (set bs (cdr bs))))

(defun equal? (a b)
  (if (and (cons? a) (cons? b))
      (equal-cons? a b)
    (= a b)))

(defun dot-node-label (node)
  (make-symbol (or (and (string? node)
                        (concat "'" node "'"))
                   (string
                    (if (cons? node)
                        (car node)
                      node)))))

(defun dot-node-name (idx)
  (make-symbol (concat 'N_ idx)))

(defun print-ast-dot-rec (tree idx)
  (let ((root-idx (dot-node-name idx))
        (root-label (dot-node-label tree)))
    (println "    " root-idx " [label=\"" root-label "\"]")
    (when (cons? tree)
      (dolist (node (cdr tree))
        (println "    " root-idx " -> " (dot-node-name (inc! idx)))
        (set idx (print-ast-dot-rec node idx)))))
  idx)

(defun print-ast-dot (ast)
  (println "digraph {")
  (print-ast-dot-rec ast 0)
  (println "}"))

(defmacro show-ast (&body body)
  ;; (print-ast-dot `(progn ,@(macroexpand body)))
  (print-ast-dot (macroexpand `(progn ,@body)))
  `(progn ,@body))

(defmacro cond (&rest cnds)
  `(loop
    ,@(map (lambda (cnd)
             `(if ,(car cnd)
                  (break ,@(cdr cnd))))
           cnds)
    (break nil)))

(defmacro case (this &rest is)
  `(loop
    ,@(map (lambda (x)
             (if (= (car x) '_)
                 `(break ,@(cdr x))
                 `(if (= ,this ,(car x))
                      (break ,@(cdr x)))))
           is)
    (break nil)))
