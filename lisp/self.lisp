(defun atom? (x)
  (or (number? x)
      (bool? x)
      (string? x)
      (nil? x)))

(defun product (xs)
  (let ((p 1))
    (dolist (x xs)
      (set p (* p x)))
    p))

(defun evil-r (expr env)
  (let ((rec (lambda (e)
               (evil-r e env))))
    (cond ((atom? expr)
           expr)
          ((symbol? expr)
           (env expr))
          ((cons? expr)
           (let ((op (car expr))
                 (args (cdr expr)))
             (case op
               ('= (= (evil-r (car args) env)
                      (evil-r (cadr args) env)))
               ('+ (sum (map rec args)))
               ('- (- (evil-r (car args) env)
                      (sum (map rec (cdr args)))))
               ('* (product (map rec args)))
               ('/ (/ (evil-r (car args) env)
                      (product (map rec (cdr args)))))
               ('cons (cons (evil-r (car args) env)
                            (evil-r (cadr args) env)))
               ('car (car (evil-r (car args) env)))
               ('cdr (cdr (evil-r (car args) env)))
               ('quote (car args))
               ('if (if (evil-r (car args) env)
                        (evil-r (cadr args) env)
                        (and (cddr args)
                             (evil-r (caddr args) env))))
               ('progn (let ((res nil))
                         (dolist (arg args)
                           (set res (evil-r arg env)))
                         res))
               ('println (println (apply concat args)))
               ('lambda (let ((x (caar args))
                              (body `(progn ,@(cdr args))))
                          (lambda (arg)
                            (evil-r body (lambda (sym)
                                           (if (= sym x)
                                               arg
                                               (env sym)))))))
               (_ ((evil-r op env)
                   (evil-r (car args) env))))))
          (true (progn
                  (println "Undefined pattern: {expr}")
                  (error 'undefined-pattern))))))

(defun evil (expr)
  (evil-r expr (lambda (x)
                 (println "Undefined variable: {x}")
                 (error 'undefined-variable))))

(defun evil-examples ()
  (println (evil '((lambda (x) (+ x 1330)) 7)))

  (println (evil '((((lambda (x)
                       (lambda (y)
                         (lambda (z)
                           (+ (* x (* 2 y)) z))))
                     4) 5) 6)))

  (println (evil '((lambda (f) (f 2))
                   (lambda (x) (+ 10 x)))))

  (println (evil '((lambda (f)
                     ((f f) 20))
                   (lambda (f)
                     (lambda (n)
                       (if (= n 0)
                           1
                           (* n ((f f) (- n 1)))))))))

  (println (evil '((((lambda (f)
                       (f f))
                     (lambda (f)
                       (lambda (g)
                         (lambda (xs)
                           (if xs
                               (cons (g (car xs))
                                     (((f f) g) (cdr xs))))))))
                    (lambda (x)
                      (* x 2)))
                   '(2 4 6 8 10 12))))

  (println (evil '(((lambda (map)
                      (lambda (factorial)
                        ((map factorial) '(1 2 3 4 5 6 7 8 9 10))))
                    ((lambda (f)
                       (f f))
                     (lambda (f)
                       (lambda (g)
                         (lambda (xs)
                           (if xs
                               (cons (g (car xs))
                                     (((f f) g) (cdr xs)))))))))
                   ((lambda (f)
                      (f f))
                    (lambda (f)
                      (lambda (n)
                        (if (= n 0)
                            1
                            (* n ((f f) (- n 1)))))))))))

(defun do-factorial ()
  (evil '(((lambda (map)
             (lambda (factorial)
               ((map factorial) '(1 2 3 4 5 6 7 8 9 10))))
           ((lambda (f)
              (f f))
            (lambda (f)
              (lambda (g)
                (lambda (xs)
                  (if xs
                      (cons (g (car xs))
                            (((f f) g) (cdr xs)))))))))
          ((lambda (f)
             (f f))
           (lambda (f)
             (lambda (n)
               (if (= n 0)
                   1
                   (* n ((f f) (- n 1))))))))))

(defun do-factorial-d ()
  (((lambda (map)
      (lambda (factorial)
        ((map factorial) '(1 2 3 4 5 6 7 8 9 10))))
    ((lambda (f)
       (f f))
     (lambda (f)
       (lambda (g)
         (lambda (xs)
           (if xs
               (cons (g (car xs))
                     (((f f) g) (cdr xs)))))))))
   ((lambda (f)
      (f f))
    (lambda (f)
      (lambda (n)
        (if (= n 0)
            1
            (* n ((f f) (- n 1)))))))))

