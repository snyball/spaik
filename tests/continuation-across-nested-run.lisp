;;; Continuations that cross a nested-run boundary: `eval`, `read-compile`,
;;; and the compiler running a macro. These aborted the process until
;;; 2026-09-20; pinned here so a resume across the boundary stays a value.

;; A nested run is opened by `eval`, by a native reached through the VM's
;; native-call path (`read-compile`, `macroexpand`, `_load`), and by the
;; compiler while it expands a macro. A generator is `call/cc` plus a pair
;; of continuations, so driving one either side of such a boundary is the
;; cheapest way to make a continuation cross it.

;; Every helper below builds its own generator and performs the whole
;; sequence of drives, because tests in this tree do not run in file order
;; and a fixture split across two clauses would depend on one.

;; Made and primed INSIDE the nested run, driven after it returned: the
;; continuation outlives the run it was captured in. Answers 78 - the
;; priming drive inside, then the drive outside.
(defvar cnr/in-eval nil)
(defun cnr/made-inside-eval ()
  (let ((a (eval '(progn (set cnr/in-eval (gen (lambda (yi) (yi 7) (yi 8) 9)))
                         (cnr/in-eval nil)))))
    (+ (* 10 a) (cnr/in-eval nil))))

(test cnr-generator-made-inside-eval-drives-after-it-returned
      (= 78 (cnr/made-inside-eval)))

(defvar cnr/in-rc nil)
(defun cnr/made-inside-read-compile ()
  (let ((a (read-compile "(progn (set cnr/in-rc (gen (lambda (yi) (yi 7) (yi 8) 9))) (cnr/in-rc nil))")))
    (+ (* 10 a) (cnr/in-rc nil))))

(test cnr-generator-made-inside-read-compile-drives-after-it-returned
      (= 78 (cnr/made-inside-read-compile)))

;; The other direction: captured OUTSIDE, resumed INSIDE. The drives run
;; outside, inside, then outside again, so the generator's own state has to
;; survive both entering and leaving the nested run. Answers 123.
(defvar cnr/across nil)
(defun cnr/around-eval ()
  (set cnr/across (gen (lambda (yi) (yi 1) (yi 2) (yi 3) 4)))
  (let ((a (cnr/across nil))
        (b (eval '(cnr/across nil)))
        (c (cnr/across nil)))
    (+ (* 100 a) (* 10 b) c)))

(test cnr-generator-driven-outside-then-inside-eval-then-outside
      (= 123 (cnr/around-eval)))

(defvar cnr/across-rc nil)
(defun cnr/around-read-compile ()
  (set cnr/across-rc (gen (lambda (yi) (yi 1) (yi 2) (yi 3) 4)))
  (let ((a (cnr/across-rc nil))
        (b (read-compile "(cnr/across-rc nil)"))
        (c (cnr/across-rc nil)))
    (+ (* 100 a) (* 10 b) c)))

(test cnr-generator-driven-outside-then-inside-read-compile-then-outside
      (= 123 (cnr/around-read-compile)))

;; The compiler is the third source of a nested run: a macro that pulls a
;; value from a generator resumes a continuation at COMPILE time, and the
;; runtime drive afterwards picks up where expansion left off. Neither
;; `eval` nor `read-compile` appears in this shape. Answers 10 then 20.
(defvar cnr/at-expansion (gen (lambda (yi) (yi 10) (yi 20) 30)))
(defmacro cnr/take () (cnr/at-expansion nil))
(defun cnr/expansion-then-runtime ()
  (let ((a (cnr/take)))
    (+ a (cnr/at-expansion nil))))

(test cnr-macro-expansion-drive-and-runtime-drive-are-consecutive
      (= 30 (cnr/expansion-then-runtime)))

;; A continuation captured while the COMPILER was running a macro, then
;; resumed inside a runtime nested run, used to bring the compiler's own
;; working stack back into the program and abort the process. The whole
;; file is expanded before any of it runs, so `cnr/mk` is live by then.
(defvar cnr/mk nil)
(defmacro cnr/grab () (call/cc (lambda (c) (set cnr/mk c) nil)) ''x)
(cnr/grab)
(defun cnr/resume-compiler-capture ()
  (read-compile "(cnr/mk nil)")
  :cnr-survived)

(test cnr-compile-time-capture-resumed-in-a-native-nested-run
      (eq? :cnr-survived (cnr/resume-compiler-capture)))

;; A `throw` leaving a RESUMED continuation and crossing an `eval` used to
;; leave the capture frame of the enclosing closure un-popped, and the
;; handler's return then read live data where a frame record belonged. The
;; closure must capture an upvalue and the `catch` must sit in a real call
;; frame for this to be the shape that broke.
(defvar cnr/rk nil)
(defun cnr/callit (f) (f))
(defun cnr/thrower (a)
  (cnr/callit (lambda ()
                (call/cc (lambda (k2) (set cnr/rk k2) (throw 'cnr-esc nil)))
                (throw 'cnr-tt a))))
(defun cnr/resume-under-catch () (catch 'cnr-tt (eval '(cnr/rk nil))))
(defun cnr/throw-across-eval ()
  (catch 'cnr-esc (cnr/thrower 3))
  (cnr/resume-under-catch)
  :cnr-survived)

(test cnr-throw-out-of-a-resumed-continuation-across-eval
      (eq? :cnr-survived (cnr/throw-across-eval)))
