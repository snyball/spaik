;;; `get` with a non-integer index on a vec blames the INDEX, not the
;;; container. The container is only named when `get` really does not
;;; accept that container at all.

;;; ---[ helpers ]-----------------------------------------------------

(defun gix/catch (tag form) (catch tag (eval form)))

(defun gix/starts-with? (prefix s)
  (let ((pit (iter prefix))
        (sit (iter s)))
    (loop
     (let ((p (next pit)))
       (if (iter-end? p)
           (break true)
         (let ((c (next sit)))
           (if (iter-end? c)
               (break nil)
             (unless (= p c)
               (break nil)))))))))

(defun gix/msg? (tag prefix form)
  (let ((v (gix/catch tag form)))
    (and (string? v) (gix/starts-with? prefix v))))

;;; ---[ a bad index on a vec names the index ]--------------------------

;; The message used to read "Expected one of vec, vec2, vec3, table in
;; get, but got vec" - it said it wanted a vec and had been given one,
;; because the vec path fell through to the container-type check
;; instead of reporting the offending index.

(test gix-vec-bad-index-names-the-index-type
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got float"
                '(if (get (vec 1 2 3) 1.5) 1 2))
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got float"
                '(if (get (vec 1 2 3) 0.0) 1 2))
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got symbol"
                '(if (get (vec 1 2 3) :k) 1 2))
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got string"
                '(if (get (vec 1 2 3) "a") 1 2))
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got nil"
                '(if (get (vec 1 2 3) nil) 1 2))
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec, but got bool"
                '(if (get (vec 1 2 3) true) 1 2)))

;; The fixed-width vectors report the same way and name their own type.
(test gix-vec2-bad-index-names-the-index-type
      (gix/msg? 'type-error "Type Error: Expected integer for index on vec2, but got float"
                '(if (get (vec2 1 2) 1.5) 1 2)))

;;; ---[ blaming the container is still right when it is the container ]-

;; `get` accepts neither string nor cons with ANY index, so naming the
;; container is the correct answer for those.

(test gix-unsupported-container-names-the-container
      (gix/msg? 'type-error "Type Error: Expected one of vec, vec2, vec3, table in get, but got string"
                '(if (get "abc" 1) 1 2))
      (gix/msg? 'type-error "Type Error: Expected one of vec, vec2, vec3, table in get, but got cons"
                '(if (get (list 1 2) 1) 1 2)))

;;; ---[ the write path agrees with the read path ]----------------------

;; `set` on a vec element has always named the index; the two paths
;; report the same mistake the same way now.

(defun gix/set-bad-index ()
  (gix/catch 'type-error
             '(if (progn (define gix/gv (vec 1 2)) (set (get gix/gv 0.0) 1)) 1 2)))

(test gix-set-bad-index-names-the-index-type
      (gix/starts-with? "Type Error: Expected integer for index on vec, but got float"
                        (gix/set-bad-index)))

;;; ---[ controls: good indices still work ]-----------------------------

(defun gix/good-vec () (get (vec 1 2 3) 1))
(defun gix/good-vec3 () (get (vec3 1 2 3) 1))
(defun gix/good-table () (get (make-table :a 1) :a))

(test gix-good-indices-are-unaffected
      (= 2 (gix/good-vec))
      (= 2.0 (gix/good-vec3))
      (= 1 (gix/good-table)))
