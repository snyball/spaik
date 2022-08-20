(defmacro await (expr)
  (let ((k (gensym)))
    `(call/cc (lambda (,k)
                (<ζ>::send-message ,expr ,k)
                (throw '<ζ>::await)))))

(defmacro send (expr)
  `(<ζ>::send-message ,expr))

(defun <ζ>::send-message (msg cb)
  (error 'not-in-async-context))
