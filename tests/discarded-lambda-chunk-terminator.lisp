;;; Two lambda literals in statement position, followed by another form,
;;; used to lose the chunk's terminator: execution ran off the end of the
;;; bytecode into whatever followed it in memory.

;;; The damage landed AFTER the program's own output, so the only honest
;;; way to pin it is to run the shape at the top level of a real file and
;;; record that each subsequent top-level form still ran. A regression
;;; here does not fail a clause - it takes the process out - which is the
;;; correct amount of noise for a chunk that executes past its own end.
(define dlt/marks (vec))

;; Two bare lambdas, dropped. The minimal shape.
(lambda (v) 1)
(lambda (v) 2)
(push dlt/marks :bare-two)

;; Three of them: the terminator went missing for any count above one.
(lambda (v) 1)
(lambda (v) 2)
(lambda (v) 3)
(push dlt/marks :bare-three)

;; The reachable form - a table of callbacks built and thrown away.
;; `list`, `cons` and `vec` each reached the fault through a different
;; signal (SIGSEGV, SIGILL, an allocator abort), so all three are here.
(list (lambda (v) 1) (lambda (v) 2))
(push dlt/marks :list)

(cons (lambda (v) 1) (lambda (v) 2))
(push dlt/marks :cons)

(vec (lambda (v) 1) (lambda (v) 2))
(push dlt/marks :vec)

;; Nested one level down, so the statement position is inside `progn`
;; rather than at the top of the chunk.
(progn (lambda (v) 1) (lambda (v) 2) 3)
(push dlt/marks :progn)

;; Controls: one lambda, and two with no trailing form, both always
;; terminated correctly. They are here so a fix cannot work by dropping
;; the terminator everywhere equally.
(lambda (v) 1)
(push dlt/marks :single)

;;; ---[ the same shape inside a function body ]-----------------------------

;; Inside a `defun` the missing terminator reached different garbage and
;; hung instead of dying, so this half never printed anything at all.
(defun dlt/body-two () (lambda (v) 1) (lambda (v) 2) 3)
(defun dlt/body-three () (lambda (v) 1) (lambda (v) 2) (lambda (v) 3) 4)
(defun dlt/body-list () (list (lambda (v) 1) (lambda (v) 2)) 5)
(defun dlt/body-single () (lambda (v) 1) 6)

;;; ---[ and reached through `eval` ]----------------------------------------

;; Each fuzzed form arrives inside a `catch` around an `eval`, which is
;; how this was first hit. Driven repeatedly because the fault depended
;; on heap layout rather than on the form, so one pass could miss it.
(defun dlt/ev (form) (catch 'dlt-tag (eval form)))

(defun dlt/ev-repeat (n)
  (let ((i 0))
    (loop (if (>= i n) (break))
      (dlt/ev '(progn (lambda (v) 1) (lambda (v) 2) 3))
      (set i (+ i 1)))
    i))

(defun dlt/marks-now () dlt/marks)

(test dlt-toplevel-forms-after-discarded-lambdas-all-ran
      (eq? (vec :bare-two :bare-three :list :cons :vec :progn :single)
           (dlt/marks-now)))

(test dlt-discarded-lambdas-in-a-function-body
      (= 3 (dlt/body-two))
      (= 4 (dlt/body-three))
      (= 5 (dlt/body-list))
      (= 6 (dlt/body-single)))

(test dlt-discarded-lambdas-under-eval
      (= 3 (dlt/ev '(progn (lambda (v) 1) (lambda (v) 2) 3)))
      (= 80 (dlt/ev-repeat 80)))
