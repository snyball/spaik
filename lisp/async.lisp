;; (unless (function? (maybe-defined --message-send))
;;   (error 'not-in-async-context))

(defmacro await (expr)
  (let ((k (gensym)))
    `(call/cc (lambda (,k)
                (--send-message ,expr ,k)
                (throw 'await)))))

(defmacro send (expr)
  `(--send-message ,expr))

(defun --send-message (msg cb)
  (error 'not-in-async-context))
