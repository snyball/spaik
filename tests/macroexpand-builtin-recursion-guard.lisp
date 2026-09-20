;;; The `macroexpand` builtin used to skip the compiler's 1000-level
;;; macro-recursion guard and overflow the native stack instead of
;;; raising. It now shares the guard and raises a catchable error.

(defmacro mxg/rec (x) `(mxg/rec ,x))

(defun mxg/catch () (catch 'recursion-limit (eval '(macroexpand '(mxg/rec 1)))))

(defun mxg/starts-with? (prefix s)
  (let ((pit (iter prefix)) (sit (iter s)))
    (loop
     (let ((p (next pit)))
       (if (iter-end? p)
           (break true)
         (let ((c (next sit)))
           (if (iter-end? c)
               (break nil)
             (unless (= p c)
               (break nil)))))))))

(test mxg-macroexpand-builtin-hits-the-recursion-guard
      (string? (mxg/catch))
      (mxg/starts-with? "Macro Recursion Error: Macro expansion was recursive beyond"
                         (mxg/catch)))
