(defmacro popen (cmd &body handler)
  (let ((proc (gensym)))
    `(let ((,proc (sys::proc-start cmd)))
       (sys::dup-stdout (sys::proc-stdin ,proc))
       ,@handler
       (sys::proc-wait ,proc)
       (sys::reset-stdout))))

(let ((out (popen '(mktemp))))
  (popen `(dot -T svg -o ,out)
     (print-ast-dot)))
