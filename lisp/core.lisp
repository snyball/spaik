(define sys/load-path (vec))

(define (<ξ>::defun name args &body body)
  `(define (,name ,@args) ,@body))
(set-macro! defun <ξ>::defun)

(defun <ξ>::defmacro (name args &body body)
  ((lambda (mac-fn-name)
     `(progn
        (define (,mac-fn-name ,@args)
          ,@body)
        (set-macro! ,name ,mac-fn-name)))
   (make-symbol (concat '<ξ>:: name))))
(set-macro! defmacro <ξ>::defmacro)

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

(defun map (f xs)
  (if xs (cons (f (car xs))
               (map f (cdr xs)))))

(defmacro let (defs &rest body)
  `((lambda ,(map (lambda (x) (car x)) defs)
      ,@body)
    ,@(map (lambda (x) (car (cdr x))) defs)))

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

(define <β>::num 0)
(defun gensym ()
  (let ((sym (make-symbol (concat "<β>::" <β>::num))))
    (inc! <β>::num)
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

(defmacro iter-end? (res)
  `(= ,res '<ζ>::iter-stop))

;;; FIXME: (next)/(break) don't work inside dolist/range,
;;;        a compiler built-in is needed to fix it.
(defmacro dolist (cnd &body body)
  (let ((name (car cnd))
        (init (car (cdr cnd)))
        (sentinel '<ζ>::iter-stop)
        (it (gensym)))
    `(let ((,name nil)
           (,it (iter ,init)))
       (loop (if (iter-end? (set ,name (next ,it)))
               (break))
             ,@body))))

(defun member? (x xs)
  (dolist (y xs)
    (when (eq? x y)
      (break true))))

;; FIXME: (next) doesn't work in range. In order for (next) to work there needs
;; to be a special loop constrct like (s-loop (a..) (b..)) where (next) in (a..)
;; jumps to (b..) rather than the start of the next loop. Alternatively...
;; There could be a
(defmacro defexample (name &body body))
(defexample range-impl
    `(with-labels
       :loop-start
       (if (not (< ,loop-var ,max))
           (jmp :loop-end))
       (with-macros ((next (&? x)
                        (if x '(next x)
                            '(jmp :loop-next)))
                     (break () '(jmp :loop-end)))
         ,@body)
       :loop-next
       (inc! ,loop-var)
       (jmp :loop-start)
       :loop-end))
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

(defun abs (x)
  (if (< x 0)
      (- x)
    x))

(defun sqrt (x)
  (pow x 0.5))

(defun mean (xs)
  (/ (sum xs) (len xs)))

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
                 `(if (eq? ,this ,(car x))
                      (break ,@(cdr x)))))
           is)
    (break nil)))

(defmacro fmt (w &rest in)
  (let* ((begin (next (iter "{")))
         (end (next (iter "}")))
         (in-sub false)
         (span (vec))
         (out '(concat)))
    (dolist (c w)
      (when (= c begin)
        (set out (cons (join span) out))
        (set span (vec))
        (set in-sub true)
        (next))
      (when (= c end)
        (unless in-sub
          (error 'trailing-delimiter))
        (set out (cons (make-symbol (join span)) out))
        (set span (vec))
        (set in-sub false)
        (next))
      (push span c))
    (when in-sub
      (error 'unclosed-delimiter))
    (set out (cons (join span) out))
    (reverse out)))

(defun _println (x)
  (println x))

(defmacro println (w &rest in)
  (if (string? w)
      `(_println (fmt ,w ,@in))
      `(_println ,w ,@in)))

(defun _print (x)
  (print x))

(defmacro print (w &rest in)
  (if (string? w)
      `(_print (fmt ,w ,@in))
      `(_print ,w ,@in)))

(defun find-first-duplicate (xs)
  (when xs
    (let ((x (car xs))
          (ys (cdr xs)))
      (if (member? x ys)
          x
          (find-first-duplicate ys)))))

(defmacro if-let (decl &body b)
  (let ((name (car decl))
        (init (cadr decl)))
    `(let ((,name ,init))
       (if ,name (progn ,@b)))))

(defmacro eval-when-compile (&body b)
  (eval `(progn ,@b)))

(defun _load (lib)
  (load lib))

(defmacro load (lib)
  (_load lib)
  nil)

(defmacro dbg (obj)
  `(_println (concat ',obj ": " ,obj)))

(defun collect (it)
  (let ((elem nil)
        (out (vec)))
    (loop (if (iter-end? (set elem (next it)))
            (break))
          (push out elem))
    out))

(defmacro yield (expr)
  (let ((k (gensym)))
    `(call/cc (lambda (,k)
                (throw (cons ,expr ,k))))))

(defmacro await (expr)
  (let ((k (gensym)))
    `(call/cc (lambda (,k)
                (<ζ>::send-message ,expr ,k)
                (throw '<ζ>::yield-await)))))

(defmacro send (expr)
  `(<ζ>::send-message ,expr))
