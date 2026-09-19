;;; A two-operand `or` whose value is DISCARDED must pop exactly what it
;;; pushed. It used to emit two `jt`s for one push, and the extra pop ate
;;; the enclosing frame's saved state - return address included.

;;; The first operand must not be compile-time foldable, or the dead
;;; second operand is eliminated and the imbalance goes with it. A global
;;; read is the cheapest way to keep the compiler honest.
(define osp/z nil)

;;; ---[ statement position under a continuation ]---------------------------

;; This is the shape that died: the damaged slot held the return address
;; of `call/cc`'s lambda, so `ret` resumed at the start of the enclosing
;; function body instead of at its caller. The `cons` pins that the
;; caller's own frame survived too - `1` has to still be there afterwards.
(defun osp/cc-global () (cons 1 (call/cc (lambda (k) (progn (or osp/z 1) 7)))))
(defun osp/cc-nil ()   (cons 1 (call/cc (lambda (k) (progn (or nil 1) 7)))))
(defun osp/cc-false () (cons 1 (call/cc (lambda (k) (progn (or false 1) 7)))))

;; Both operands falsy: the fall-through path, where nothing is truthy
;; and the jumps are never taken.
(defun osp/cc-nil-nil () (cons 1 (call/cc (lambda (k) (progn (or nil nil) 7)))))

;;; ---[ the arities either side of the broken one ]-------------------------

;; Three operands compiled correctly throughout, and a compile-time
;; truthy first operand folded to a single balanced `jt`. Both are here
;; so a fix that re-balances the two-operand case by unbalancing its
;; neighbours cannot pass.
(defun osp/cc-three () (cons 1 (call/cc (lambda (k) (progn (or nil 1 2) 7)))))
(defun osp/cc-fold ()  (cons 1 (call/cc (lambda (k) (progn (or 1 2) 7)))))

;; `and` emits `jn` and was never affected; pinned for the same reason.
(defun osp/cc-and ()     (cons 1 (call/cc (lambda (k) (progn (and nil 1) 7)))))
(defun osp/cc-and-glob () (cons 1 (call/cc (lambda (k) (progn (and osp/z 2) 7)))))

;;; ---[ the same imbalance under other frames ]-----------------------------

;; What the extra pop destroys depends on what sits under it. Without a
;; continuation the clobbered slot was re-entered rather than returned
;; through, and these spun forever instead of dying.
(defun osp/loop ()   (loop (or osp/z 1) (break 7)))
(defun osp/catch ()  (catch 'osp-tag (loop (or nil 1) (break 7))))
(defun osp/lambda () ((lambda (k) (loop (or nil 1) (break 7))) 0))

;;; ---[ value position, which must keep working ]---------------------------

;; When the value IS used, `or` answers its first truthy operand and nil
;; when none is truthy. The push/pop counts differ from the statement
;; case on purpose; the fix must not collapse the two.
(defun osp/val-global () (or osp/z 1))
(defun osp/val-fold ()   (or 5 1))
(defun osp/val-none ()   (or nil nil))
(defun osp/val-three ()  (or nil nil 3))

(test osp-discarded-or-preserves-the-frame
      (eq? (cons 1 7) (osp/cc-global))
      (eq? (cons 1 7) (osp/cc-nil))
      (eq? (cons 1 7) (osp/cc-false))
      (eq? (cons 1 7) (osp/cc-nil-nil)))

(test osp-neighbouring-arities-still-balanced
      (eq? (cons 1 7) (osp/cc-three))
      (eq? (cons 1 7) (osp/cc-fold))
      (eq? (cons 1 7) (osp/cc-and))
      (eq? (cons 1 7) (osp/cc-and-glob)))

(test osp-discarded-or-under-other-frames
      (= 7 (osp/loop))
      (= 7 (osp/catch))
      (= 7 (osp/lambda)))

(test osp-or-in-value-position
      (= 1 (osp/val-global))
      (= 5 (osp/val-fold))
      (eq? nil (osp/val-none))
      (= 3 (osp/val-three)))
