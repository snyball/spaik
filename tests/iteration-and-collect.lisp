;;; What `iter` accepts, what `collect` gives back for each of them, and
;;; the walkers that are cons-only. Companion to tests/test-stdlib.lisp.

(defun itc/catch (tag form) (catch tag (eval form)))
(defun itc/starts-with? (prefix s)
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
(defun itc/msg? (tag prefix form)
  (let ((v (itc/catch tag form)))
    (and (string? v) (itc/starts-with? prefix v))))

;; `collect` always answers a vec, whatever it was given.
(test itc-collect-always-answers-a-vec
      (eq? (vec 1 2 3) (collect (iter (list 1 2 3))))
      (eq? (vec 1 2 3) (collect (iter (vec 1 2 3))))
      (eq? (vec) (collect (iter nil)))
      (vec? (collect (iter "abc"))))

;; A string iterates over characters, which are their own type and are
;; not one-character strings.
(defun itc/first-char () (next (iter "abc")))

(test itc-a-string-iterates-over-characters
      (= 3 (len (collect (iter "abc"))))
      (not (string? (itc/first-char)))
      (= (itc/first-char) (chr "a")))

;; A table iterates over its KEYS. Order is not pinned - only the set
;; of keys and the count.
(defun itc/table-keys () (collect (iter (make-table :a 1 :b 2))))

(test itc-a-table-iterates-over-its-keys
      (= 2 (len (itc/table-keys)))
      (elem? :a (itc/table-keys))
      (elem? :b (itc/table-keys))
      (not (elem? 1 (itc/table-keys))))

;; An iterator is consumed: collecting the same one twice answers empty
;; the second time. This is the trap behind any helper that walks its
;; argument more than once.
(defun itc/collect-twice ()
  (let ((it (iter (list 1 2))))
    (list (len (collect it)) (len (collect it)))))

(test itc-an-iterator-is-consumed
      (eq? '(2 0) (itc/collect-twice)))

;; `iter`'s type error lists four of the five things it accepts: `nil`
;; is missing from the message and iterates fine as an empty sequence.
;; Pinned as the message currently reads - a correction should be a
;; deliberate change.
(test itc-iter-error-omits-nil-from-the-accepted-list
      (itc/msg? 'type-error
                "Type Error: Expected one of cons, string, vec, table for argument 1 of (iter ...)"
                '(if (iter 5) 1 2))
      (itc/msg? 'type-error
                "Type Error: Expected one of cons, string, vec, table for argument 1 of (iter ...)"
                '(if (iter car) 1 2))
      ;; and yet
      (= 1 (len (collect (iter (make-table :a 1)))))
      (= 0 (len (collect (iter nil)))))

;; The cons-only camp. These walk with `car`/`cdr` instead of `iter`, so
;; a vec reaches `car`'s type error rather than being iterated.
(test itc-find-first-duplicate-is-cons-only
      (= 1 (find-first-duplicate (list 1 2 3 2 1)))
      (nil? (find-first-duplicate (list 1 2 3)))
      (nil? (find-first-duplicate nil))
      (itc/msg? 'type-error "Type Error: Expected cons in car, but got vec"
                '(if (find-first-duplicate (vec 1 2 1)) 1 2)))

(test itc-zip-is-cons-only-and-stops-at-the-shorter
      (= 1 (len (zip (list 1 2 3) (list 'a))))
      (nil? (zip (list 1) nil))
      (itc/msg? 'type-error "Type Error: Expected cons in car, but got vec"
                '(if (zip (vec 1) (vec 2)) 1 2)))

;; `join` takes any sequence and stringifies each element; `concat`
;; takes its arguments directly and never raises on a type.
(test itc-join-and-concat
      (= "1-2-3" (join (vec 1 2 3) "-"))
      (= "(1 2)-3" (join (list (list 1 2) 3) "-"))
      (= "1ab:cnil" (concat 1 "a" 'b :c nil))
      (= "" (concat)))
