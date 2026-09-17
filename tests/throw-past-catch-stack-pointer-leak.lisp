(defun tpc-fail! () (throw 'tpc-oops 42))

(defun tpc-1 (s)   (catch 'tpc-oops (tpc-fail!)))   ; one reference arg
(defun tpc-2 (a b) (catch 'tpc-oops (tpc-fail!)))   ; two - both leaked
(defun tpc-0 ()    (catch 'tpc-oops (tpc-fail!)))   ; zero - was immune

;; A loop run AFTER a throw-past-catch. Its counter is what used to land
;; on a stranded slot and compare against a string instead of an integer.
(defun tpc-sum-after-throw ()
  (tpc-1 "stranded-string")
  (let ((i 0) (n 0))
    (loop (if (not (< i 5)) (break))
          (set n (+ n i))
          (inc! i))
    n))

;; Same idea through `dolist`, whose expansion binds two slots; the leak
;; used to displace them by one and hand `next` the wrong binding.
(defun tpc-dolist-after-throw ()
  (tpc-1 "stranded-string")
  (let ((n 0))
    (dolist (x '(1 2 3))
      (set n (+ n x)))
    n))

;; The leak accumulated one region per call, so the damage grew without
;; bound. Drive many calls of each arity, then check a loop still works.
(defun tpc-after-many-calls (rounds)
  (let ((r 0))
    (loop (if (not (< r rounds)) (break))
          (tpc-1 "stranded-string")
          (tpc-2 "stranded-a" "stranded-b")
          (tpc-0)
          (inc! r)))
  (tpc-sum-after-throw))

;; Recursive higher-order use. At 400 elements this aborted the old build
;; outright with an out-of-bounds stack index (r8vm.rs:3037).
(defun tpc-filter-count (n)
  (len (filter tpc-1 (range-list 0 n))))

;; The `catch` outside the throwing function rather than inside it. This
;; shape drove the frame base the other way, so offsets went negative.
(defun tpc-thrower (s) (throw 'tpc-oops 42))
(defun tpc-outer-catch ()
  (catch 'tpc-oops (tpc-thrower "stranded-string"))
  (let ((n 0))
    (dolist (x '(7 8))
      (set n (+ n x)))
    n))

(test throw-past-catch-stack-pointer-leak
      ;; the throw itself always worked - these guard the control flow
      (= 42 (tpc-1 "stranded-string"))
      (= 42 (tpc-2 "stranded-a" "stranded-b"))
      (= 42 (tpc-0))
      ;; slot reuse after the unwind
      (= 10 (tpc-sum-after-throw))
      (= 6  (tpc-dolist-after-throw))
      (= 15 (tpc-outer-catch))
      ;; accumulation across many calls
      (= 10 (tpc-after-many-calls 60))
      ;; recursive consumer, the shape that aborted the old build
      (= 400 (tpc-filter-count 400)))
