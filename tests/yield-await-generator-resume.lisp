(defvar y-log nil)
(defvar y-step 0)

(defun y-gen ()
  (yield 1)
  (yield 2)
  'finished)

;; Drives the generator to exhaustion. Returns (entries . yielded-values),
;; most recent value first.
(defun y-drive ()
  (set y-log nil)
  (set y-step 0)
  (let ((r (catch 'yield (y-gen))))
    (set y-step (+ y-step 1))
    ;; On the re-entry, r is 'finished rather than a pair - skip it.
    (when (= y-step 1)
      (set y-log (cons (car r) y-log))
      (let ((k (cdr r)))
        (let ((r2 (catch 'yield (k nil))))
          (set y-log (cons (car r2) y-log))
          (let ((k2 (cdr r2)))
            (k2 nil))))))
  (cons y-step y-log))

(defvar resumed-with nil)

(defun y-echo-gen ()
  (set resumed-with (yield 'first))
  (yield 'second)
  'finished)

;; Resumes once with a known value; reports what the yield site received.
(defun y-resume-value ()
  (set resumed-with nil)
  (let ((r (catch 'yield (y-echo-gen))))
    (let ((k (cdr r)))
      (catch 'yield (k 'sent-in))))
  resumed-with)

;; The yield following a resume must surface through the fresh catch.
(defun y-second-yield ()
  (let ((r (catch 'yield (y-echo-gen))))
    (let ((k (cdr r)))
      (let ((r2 (catch 'yield (k 'sent-in))))
        (car r2)))))

;; Plain call/cc with no catch/throw - correct on both builds, kept so a
;; future regression says which layer broke.
(defvar saved-k nil)

(defun y-plain-callcc ()
  (let ((v (call/cc (lambda (k) (set saved-k k) 1))))
    (when (= v 1)
      (let ((k saved-k))
        (k 99)))
    v))

(test yield-await-generator-resume
      ;; two yields, then the body returns and re-enters the first catch
      (= 2 (car (y-drive)))
      (= 2 (len (cdr (y-drive))))
      (= 2 (car (cdr (y-drive))))
      (= 1 (car (cdr (cdr (y-drive)))))
      ;; the value handed to the continuation is what `yield` returns
      (= 'sent-in (y-resume-value))
      ;; and the body carries on to its next yield
      (= 'second (y-second-yield))
      ;; bare call/cc re-entry
      (= 99 (y-plain-callcc)))
