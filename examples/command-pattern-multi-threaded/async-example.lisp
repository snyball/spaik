(define *global* 0)

(defun init ())

(defun add (x)
  (let ((res (await '(test :id 1337))))
    (set *global* (+ *global* res x 1))))
