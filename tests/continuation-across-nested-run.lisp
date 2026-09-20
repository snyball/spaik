;;; Generators primed inside a nested run and driven from outside it.
;;; The priming drive answers the first yield, the outside drive the second.
;;; That second drive aborted the process until 2026-09-20.

;; A nested run is opened by `eval`, by a native reached through `zcall`
;; (`read-compile`, `macroexpand`, `_load`), and by the compiler while it
;; expands a macro. A generator built and primed inside one holds a
;; continuation belonging to that run, so driving it afterwards resumes
;; across the boundary.
;;
;; That crossing used to end the process with a Rust assertion, "Bad access
;; pattern", naming the two stack bases it had compared. It is legitimate:
;; the continuation outlives the run it was captured in, which is what a
;; generator handed back to its caller is FOR. Every generator below yields
;; twice and returns a third value, so the drive from outside is the
;; assertion that matters — it is the one that has to cross.
;;
;; The priming runs at load time on purpose. It is the shape a library has
;; when it hands out an already-started generator, and it keeps each drive
;; to exactly one, so a value here cannot drift by being driven twice.

;;; ---[ eval ]--------------------------------------------------------------

(defvar cnr/eg nil)

;; The `eval`'s VALUE is bound rather than discarded: an `eval` in statement
;; position is compiled away, and then the generator is never built and the
;; variable stays nil — a test that proves nothing.
(defvar cnr/eval-primed
  (eval '(progn (set cnr/eg (gen (lambda (yi) (yi 7) (yi 8) 9)))
                (cnr/eg nil))))
(defvar cnr/eval-driven (cnr/eg nil))

(defun cnr/eval-primed-value () cnr/eval-primed)
(defun cnr/eval-driven-value () cnr/eval-driven)

;;; ---[ read-compile ]------------------------------------------------------

;; `read-compile` compiles and runs a source STRING at runtime. It reaches
;; its nested run by a different route than `eval` does, and the same
;; crossing used to end the run silently at exit 0 before it aborted.

(defvar cnr/rg nil)

(defvar cnr/rc-primed
  (read-compile
   "(progn (set cnr/rg (gen (lambda (yi) (yi 7) (yi 8) 9))) (cnr/rg nil))"))
(defvar cnr/rc-driven (cnr/rg nil))

(defun cnr/rc-primed-value () cnr/rc-primed)
(defun cnr/rc-driven-value () cnr/rc-driven)

;;; ---[ macro expansion ]---------------------------------------------------

;; A macro that hands out a compile-time-unique value by pulling it from a
;; generator. The expansion runs in the compiler's own nested run, so the
;; drive inside `cnr/take` captures a continuation belonging to the
;; compiler; the drive below it is an ordinary runtime one from outside.
;;
;; This is the shape with no `eval` and no `read-compile` written anywhere
;; in it — the boundary is opened by the compiler, and nothing in the
;; source says so.

(defvar cnr/c (gen (lambda (yi) (yi 10) (yi 20) 30)))

(defmacro cnr/take () (cnr/c nil))

(defvar cnr/mac-expanded (cnr/take))
(defvar cnr/mac-driven (cnr/c nil))

(defun cnr/mac-expanded-value () cnr/mac-expanded)
(defun cnr/mac-driven-value () cnr/mac-driven)

;;; ---[ the control: no boundary anywhere ]---------------------------------

;; The same two drives with the generator built at top level. If this one
;; ever fails, the break is in `gen` itself rather than in the crossing,
;; and the three above say nothing about nested runs.

(defvar cnr/plain (gen (lambda (yi) (yi 7) (yi 8) 9)))

(defvar cnr/plain-first (cnr/plain nil))
(defvar cnr/plain-second (cnr/plain nil))

(defun cnr/plain-first-value () cnr/plain-first)
(defun cnr/plain-second-value () cnr/plain-second)

(test cnr-generator-primed-inside-eval-drives-outside
      (= 7 (cnr/eval-primed-value))
      (= 8 (cnr/eval-driven-value)))

(test cnr-generator-primed-inside-read-compile-drives-outside
      (= 7 (cnr/rc-primed-value))
      (= 8 (cnr/rc-driven-value)))

(test cnr-generator-driven-during-macro-expansion-drives-at-runtime
      (= 10 (cnr/mac-expanded-value))
      (= 20 (cnr/mac-driven-value)))

(test cnr-same-two-drives-with-no-nested-run
      (= 7 (cnr/plain-first-value))
      (= 8 (cnr/plain-second-value)))
