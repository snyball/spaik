;;; What the `!` sequence functions actually do to their argument, and
;;; what they hand back. `split!`, `del`, `pop`, `sort`/`sort!`,
;;; `reverse`/`reverse!`, `for-each`.

;; `split!` takes ONE argument. It splits a cons list roughly in half
;; and returns (first-half . second-half); the variable passed in is
;; left holding the first half. It is cons-only.
(defun sqm/split-ret (xs) (split! xs))
(defun sqm/split-left (xs) (split! xs) xs)
(defun sqm/split-cons? (xs) (cons? (split! xs)))

(test sqm-split-returns-both-halves
      (eq? '((1 2) 3 4) (sqm/split-ret (list 1 2 3 4)))
      (eq? '((1 2) 3) (sqm/split-ret (list 1 2 3))))

(test sqm-split-truncates-its-argument
      (eq? '(1 2) (sqm/split-left (list 1 2 3 4)))
      (eq? '(1) (sqm/split-left (list 1))))

(defun sqm/catch (tag form) (catch tag (eval form)))
(defun sqm/starts-with? (prefix s)
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
(defun sqm/msg? (tag prefix form)
  (let ((v (sqm/catch tag form)))
    (and (string? v) (sqm/starts-with? prefix v))))

(test sqm-split-is-cons-only
      (sqm/msg? 'type-error "Type Error: Expected cons but got vec"
                '(if (split! (vec 1 2 3)) 1 2))
      (sqm/msg? 'type-error "Type Error: Expected cons but got nil"
                '(if (split! nil) 1 2)))

;; `del` is table-only - it does not remove from a vec - and answers the
;; value that was stored, or nil for a key that was not there.
(defun sqm/del-ret (k) (del (make-table :a 1 :b 2) k))
(defun sqm/del-len (k) (let ((tb (make-table :a 1 :b 2))) (del tb k) (len tb)))

(test sqm-del-on-a-table
      (= 1 (sqm/del-ret :a))
      (nil? (sqm/del-ret :zz))
      (= 1 (sqm/del-len :a))
      (= 2 (sqm/del-len :zz)))

(test sqm-del-rejects-a-vec
      (sqm/msg? 'type-error "Type Error: Expected table but got vec"
                '(if (del (vec 1 2 3) 1) 1 2)))

;; `pop` is vec-only and answers nil on an empty vec rather than raising.
(defun sqm/pop-empty () (pop (vec)))
(defun sqm/pop-last () (let ((v (vec 1 2))) (list (pop v) (len v))))

(test sqm-pop-is-vec-only
      (nil? (sqm/pop-empty))
      (eq? '(2 1) (sqm/pop-last))
      (sqm/msg? 'type-error "Type Error: Expected vec in pop, but got cons"
                '(if (pop (list 1 2)) 1 2)))

;; The bang/no-bang pairs. `sort!` and `reverse!` return the SAME object
;; and mutate it; `sort` and `reverse` leave the argument alone.
(defun sqm/sort-copies () (let ((v (vec 3 1 2))) (sort v) v))
(defun sqm/sort!-same () (let ((v (vec 3 1 2))) (eq? v (sort! v))))
(defun sqm/reverse!-same () (let ((v (vec 1 2 3))) (eq? v (reverse! v))))
(defun sqm/reverse-copies () (let ((v (vec 1 2 3))) (reverse v) v))

(test sqm-sort-and-reverse-bang-mutate-in-place
      (sqm/sort!-same)
      (sqm/reverse!-same))

(test sqm-sort-and-reverse-without-bang-copy
      (eq? (vec 3 1 2) (sqm/sort-copies))
      (eq? (vec 1 2 3) (sqm/reverse-copies)))

;; `sort` takes no comparator - a second argument is an arity error, not
;; a custom ordering.
(test sqm-sort-takes-no-comparator
      (sqm/msg? 'arg-error "Argument Error: sort expected 1 argument"
                '(if (sort (vec 3 1 2) (lambda (a b) 1)) 1 2)))

;; `for-each` is the odd one out in this file: no `!`, and nothing is
;; mutated. It calls the function for effect, discards every result and
;; answers nil - so neither the mapped values nor the sequence come back.
(defun sqm/for-each-return () (for-each (lambda (x) (* x 10)) (vec 1 2 3)))
(defun sqm/for-each-target () (let ((v (vec 1 2 3))) (for-each (lambda (x) (* x 10)) v) v))
;; The counter is a vec, not an integer: a lambda captures an immediate
;; by copy, so `(set n (+ n 1))` on a `let`-bound integer would leave the
;; caller's `n` at 0 and this helper would answer 0 whether `f` ran or not.
(defun sqm/for-each-calls ()
  (let ((seen (vec)))
    (for-each (lambda (x) (push seen x)) (vec 1 2 3))
    (len seen)))

(test sqm-for-each-runs-f-and-discards-the-results
      (nil? (sqm/for-each-return))
      (eq? (vec 1 2 3) (sqm/for-each-target))
      (= 3 (sqm/for-each-calls)))
