;; The exact shape that aborted: accumulator one scope out from the loop
;; variable, folded accumulate, catch value discarded, form after the loop.
(defun ads-sum (xs)
  (let ((total 0))
    (dolist (x xs)
      (catch 'skip (set total (+ total x))))
    total))

(defun sus-sub (xs)
  (let ((total 100))
    (dolist (x xs)
      (catch 'skip (set total (- total x))))
    total))

;; Operands commuted still hits the fold.
(defun ads-commuted (xs)
  (let ((total 0))
    (dolist (x xs)
      (catch 'skip (set total (+ x total))))
    total))

;; `inc!`/`dec!` are macros over `+`/`-` and fold the same way.
(defun ads-via-inc (xs)
  (let ((total 0))
    (dolist (x xs)
      (catch 'skip (inc! total x)))
    total))

(defun sus-via-dec (xs)
  (let ((total 100))
    (dolist (x xs)
      (catch 'skip (dec! total x)))
    total))

;; Accumulator in the SAME scope as the loop variables. This needs a
;; hand-rolled iterator, since `dolist` always introduces its own scope.
;; Before the fix this did not abort - it raised a clean `Stack Error`,
;; the same over-pop caught one step earlier.
(defun ads-same-scope (xs)
  (let ((name nil)
        (it (iter xs))
        (total 0))
    (loop (if (= (set name (next it)) '<ζ>-iter-stop) (break))
          (catch 'skip (set total (+ total name))))
    total))

;; Two scopes out.
(defun ads-two-scopes-out (xs)
  (let ((total 0))
    (let ((mid 0))
      (dolist (x xs)
        (catch 'skip (set total (+ total x))))
      (set mid total))
    total))

;; Paths that were always correct, kept so a future regression says which
;; one broke: generic arithmetic, a literal addend, and a consumed value.
(defun mul-generic (xs)
  (let ((total 1))
    (dolist (x xs)
      (catch 'skip (set total (* total x))))
    total))

(defun ads-literal-addend (xs)
  (let ((total 0))
    (dolist (x xs)
      (catch 'skip (set total (+ total 1))))
    total))

(defun ads-value-consumed (xs)
  (let ((total 0))
    (dolist (x xs)
      (set total (catch 'skip (+ total x))))
    total))

(test ads-accumulate-in-discarded-catch
      ;; the folded accumulate inside a value-discarding catch
      (= 13 (ads-sum '(1 2 4 6)))
      (= 87 (sus-sub '(1 2 4 6)))
      (= 13 (ads-commuted '(1 2 4 6)))
      (= 13 (ads-via-inc '(1 2 4 6)))
      (= 87 (sus-via-dec '(1 2 4 6)))
      ;; scope depth changed only which check fired, never the defect
      (= 13 (ads-same-scope '(1 2 4 6)))
      (= 13 (ads-two-scopes-out '(1 2 4 6)))
      ;; single-element case - the smallest form that aborted
      (= 42 (ads-sum '(42)))
      ;; paths that were already correct
      (= 24 (mul-generic '(1 2 4 3)))
      (= 4 (ads-literal-addend '(1 2 4 6)))
      (= 13 (ads-value-consumed '(1 2 4 6))))
