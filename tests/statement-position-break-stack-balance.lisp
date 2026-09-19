;;; A `break` whose loop value is DISCARDED must pop the same slots the
;;; fall-through path pops. It used to keep one, so the innermost `let`
;;; binding landed in an enclosing slot. Bindings here defeat folding.

;;; ---[ the plain form: no generator, no continuation ]---------------------

;; The loop is in STATEMENT position - `(list x y)` follows it - so the
;; compiler never pushes the break value. The break path still has to
;; drop `p`, exactly as the fall-through path does. It used to keep `p`
;; and eat the slot below, so `y` came back holding `(vec :p)`.
;;
;; Every binding is a computed value: a constant is folded away, gets no
;; stack slot, and the imbalance disappears with it.
(defun sbk/one-binding ()
  (let ((x (vec :x)) (y (vec :y)))
    (loop (let ((p (vec :p)))
            (break nil)))
    (list x y)))

;; Two and three live bindings in the loop body: the pop counts track
;; the bindings, so each count is its own chance to be off by one.
(defun sbk/two-bindings ()
  (let ((x (vec :x)) (y (vec :y)))
    (loop (let ((p (vec :p)) (q (vec :q)))
            (break nil)))
    (list x y)))

(defun sbk/three-bindings ()
  (let ((x (vec :x)) (y (vec :y)))
    (loop (let ((p (vec :p)) (q (vec :q)) (r (vec :r)))
            (break nil)))
    (list x y)))

;; Nested `let`s in the body, broken out of from the innermost.
(defun sbk/nested-lets ()
  (let ((x (vec :x)) (y (vec :y)))
    (loop (let ((p (vec :p)))
            (let ((q (vec :q)))
              (break nil))))
    (list x y)))

;; A loop that actually iterates before it breaks, and breaks from
;; inside a conditional rather than unconditionally.
(defun sbk/iterates-then-breaks ()
  (let ((x (vec :x)) (y (vec :y)) (n 0))
    (loop (let ((p (vec n)))
            (inc! n)
            (if (> n 3) (break nil) nil)))
    (list x y n)))

;; `while` expands to `loop` with a `break`, and had the same defect.
(defun sbk/while-form ()
  (let ((x (vec :x)) (y (vec :y)) (n 0))
    (while (< n 3)
      (let ((p (vec n)))
        (inc! n)))
    (list x y n)))

;; `dolist` and `range` reach their exits the same way and were never
;; affected; they are here so a regression that "fixes" the pop counts
;; in the wrong direction cannot pass unnoticed.
(defun sbk/dolist-form ()
  (let ((x (vec :x)) (y (vec :y)))
    (dolist (i (list 1 2 3))
      (let ((p (vec i)))
        nil))
    (list x y)))

(defun sbk/range-form ()
  (let ((x (vec :x)) (y (vec :y)))
    (range (i (0 3))
           (let ((p (vec i)))
             nil))
    (list x y)))

;;; ---[ the value-position half, which must keep working ]------------------

;; When the loop's value IS used the break value is pushed and the pop
;; keeps one slot on purpose. The fix must not flatten both paths into
;; the same shape - the break value has to survive, and the outer
;; bindings have to survive with it.
(defun sbk/value-used ()
  (let ((x (vec :x)) (y (vec :y)))
    (let ((v (loop (let ((p (vec :p)))
                     (break p)))))
      (list x y v))))

;; The loop in tail position: value used, nothing after it.
(defun sbk/tail-position ()
  (let ((x (vec :x)))
    (loop (let ((p (vec :p)))
            (break (list x p))))))

;;; ---[ the same loops with a suspension inside them ]----------------------

;; A generator resumed inside the loop body raises the stakes on the
;; same imbalance: the over-kept slot is live across the suspension, so
;; the mismatch aborted the interpreter instead of quietly answering
;; the wrong thing.
(defun sbk/gen-three-outer ()
  (gen (lambda (yi)
         (let ((a :A) (b :B) (c :C))
           (loop (let ((p (yi 0)))
                   (if (eq? p :stop) (break nil) nil)))
           (list a b c)))))

(defun sbk/gen-three-outer-run ()
  (catch 'done
    (let ((co (sbk/gen-three-outer)))
      (co nil)
      (co :stop))))

;; The quiet half of the same bug: the body's value after the loop, not
;; the value handed to the last resume. This answered `:stop`.
(defun sbk/gen-collect ()
  (gen (lambda (yi)
         (let ((out (vec)))
           (loop (let ((v (yi (len out))))
                   (if (eq? v :stop) (break nil) (push out v))))
           out))))

(defun sbk/gen-collect-run ()
  (let ((co (sbk/gen-collect)))
    (co nil)
    (co :a)
    (co :b)
    (catch 'done (co :stop))))

;; Resume count never mattered - one break executes one pop - but drive
;; it further anyway, since the deficit was once thought to accumulate.
(defun sbk/gen-collect-long ()
  (let ((co (sbk/gen-collect)) (n 0))
    (co nil)
    (while (< n 20)
      (co n)
      (inc! n))
    (catch 'done (co :stop))))

(test sbk-discarded-break-keeps-outer-bindings
      (eq? (list (vec :x) (vec :y)) (sbk/one-binding))
      (eq? (list (vec :x) (vec :y)) (sbk/two-bindings))
      (eq? (list (vec :x) (vec :y)) (sbk/three-bindings))
      (eq? (list (vec :x) (vec :y)) (sbk/nested-lets))
      (eq? (list (vec :x) (vec :y) 4) (sbk/iterates-then-breaks)))

(test sbk-other-loop-forms-keep-outer-bindings
      (eq? (list (vec :x) (vec :y) 3) (sbk/while-form))
      (eq? (list (vec :x) (vec :y)) (sbk/dolist-form))
      (eq? (list (vec :x) (vec :y)) (sbk/range-form)))

(test sbk-break-value-still-delivered
      (eq? (list (vec :x) (vec :y) (vec :p)) (sbk/value-used))
      (eq? (list (vec :x) (vec :p)) (sbk/tail-position)))

(test sbk-break-across-a-suspension
      (eq? (list :A :B :C) (sbk/gen-three-outer-run))
      (eq? (vec :a :b) (sbk/gen-collect-run))
      (eq? 20 (len (sbk/gen-collect-long))))
