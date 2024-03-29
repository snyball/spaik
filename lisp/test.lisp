(defmacro test (name &body tests)
  (let ((check (lambda (test)
                 (let* ((op (car test))
                        (args (cdr test))
                        (defs (map (lambda (x)
                                     `(,(gensym) ,x))
                                   args))
                        (vars (map head defs)))
                   `(let ,defs
                      (unless (,op ,@vars)
                        (list :fail ',test (list ',op ,@vars))))))))
    `(defun ,(intern (concat 'tests/ name)) ()
       (or (or ,@(map check tests))
           '(:pass)))))
