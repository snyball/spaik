;;; `read-compile` of machine-generated junk text, run under a deep stack
;;; of `catch` handlers, used to segfault in the code it had just emitted.
;;; Handler DEPTH and heap layout were the variables, not the text.

;;; Depth is load-bearing and the tags are not: the same run completed at
;;; 28 handlers and died at 34, and the six frames that made the
;;; difference were dummy tags that nothing can ever throw. So the stack
;;; below is padded deliberately - do not "tidy" it down.
(defun rcd/deep (form)
  (catch 'rcd-p0 (catch 'rcd-p1 (catch 'rcd-p2 (catch 'rcd-p3 (catch 'rcd-p4
  (catch 'rcd-p5 (catch 'rcd-p6 (catch 'rcd-p7 (catch 'rcd-p8 (catch 'rcd-p9
  (catch 'ft (catch 'tt (catch 'sx (catch 'iter-stop
  (catch 'undefined-variable (catch 'undefined-function
  (catch 'divide-by-zero (catch 'type-error (catch 'arg-error
  (catch 'not-a-proper-list (catch 'unimplemented (catch 'mut-locked
  (catch 'module-load-error (catch 'index-error (catch 'key-error
  (catch 'reference-not-allowed (catch 'missing-feature
  (catch 'cannot-move-shared-reference (catch 'rcd-q0 (catch 'rcd-q1
  (catch 'rcd-q2 (catch 'rcd-q3 (catch 'rcd-q4 (catch 'rcd-q5
  (eval form))))))))))))))))))))))))))))))))))))

;;; ---[ the generator, reproduced exactly ]---------------------------------

;; The two strings that faulted are reachable only from this PRNG at this
;; seed, and hand-written neighbours of them were all handled gracefully.
;; Regenerating rather than hard-coding them keeps the allocation history
;; that preceded the fault, which is the part that could not be replaced.
(define rcd/seed 777)

(defun rcd/rand (n)
  (set rcd/seed (% (+ (* rcd/seed 1103515245) 12345) 2147483647))
  (% (/ rcd/seed 65536) n))

(define rcd/atoms
  (vec "1" "1.5" "a" "-" "&" "@" "$" "%" "!" "?" "nil" "true" "&opt" "&rest"
       "0x10" "1e9" "-1e30" "::" "::a" "1/2" "+" "*" "abc" ":k" "e" "E" "_"
       "~" "^" "lambda" "let" "if" "." ":" "|" "l1" "-0" "+0" "1." ".5"
       "0b1" "1x" "a1" "z" "%%" "->" "<>" "..." "1a" "t"))

(define rcd/mods (vec "'" "`" "," ",@" "#"))

(defun rcd/atom () (get rcd/atoms (rcd/rand (len rcd/atoms))))

(defun rcd/expr (d)
  (if (<= d 0) (rcd/atom)
    (let ((c (rcd/rand 10)))
      (cond
        ((< c 4) (rcd/atom))
        ((= c 4) (concat (get rcd/mods (rcd/rand (len rcd/mods))) (rcd/expr (- d 1))))
        (true (concat "(" (rcd/expr (- d 1)) " " (rcd/expr (- d 1)) ")"))))))

;; Forms 0-19 are generated and DISCARDED: they advance the PRNG and
;; allocate, and reproducing the strings without them was not enough to
;; reproduce the fault. Forms 20 and 21 are the two that were compiled.
;;
;; The `println` is part of the fixture, not debug output. Every
;; hand-written reduction that dropped the per-iteration build-a-list-and
;; -print step exited cleanly on a binary that faulted on the real
;; driver, so it is kept deliberately.
(defun rcd/drive ()
  (let ((seen (vec)) (i 0))
    (loop
      (if (>= i 22) (break))
      (let ((s (rcd/expr 4)))
        (if (>= i 20)
            (progn (println (list :rcd i s))
                   (push seen s)
                   (rcd/deep (list 'read-compile s)))))
      (set i (+ i 1)))
    seen))

(define rcd/result (rcd/drive))

(defun rcd/strings () rcd/result)

;; Pinning the generated text as well as the completion: if the PRNG or
;; the atom table ever drifts, this file stops exercising the shape it
;; was written for, and that should fail loudly rather than pass quietly.
(test rcd-deep-catch-read-compile-completes
      (= 2 (len (rcd/strings)))
      (eq? "((((% if) ?) ((if t) (| if))) &rest)" (get (rcd/strings) 0))
      (eq? "(,@((% let) (0b1 1x)) $)" (get (rcd/strings) 1)))

;;; ---[ the second witness, a different seed and different text ]-----------

;; An independent run reached the same fault on `(1a (+0 -0))`, which in
;; isolation is caught cleanly as a type error. Both are compiled here
;; through the same deep stack. `read-compile` EVALUATES what it reads,
;; so a well-formed string answers its value and a broken one answers
;; whatever the matching handler was given.
(defun rcd/compile (s) (rcd/deep (list 'read-compile s)))

(defun rcd/starts-with? (prefix s)
  (let ((pit (iter prefix)) (sit (iter s)))
    (loop
     (let ((p (next pit)))
       (if (iter-end? p)
           (break true)
         (let ((c (next sit)))
           (if (iter-end? c)
               (break nil)
             (unless (= p c)
               (break nil)))))))))

(defun rcd/msg? (prefix s)
  (let ((v (rcd/compile s)))
    (and (string? v) (rcd/starts-with? prefix v))))

(test rcd-deep-catch-junk-text-is-caught-not-fatal
      (rcd/msg? "Type Error: Expected lambda for argument 0 of (apply ...)"
                "(1a (+0 -0))")
      (rcd/msg? "Argument Error: if expected from 2 to 3 arguments"
                "((((% if) ?) ((if t) (| if))) &rest)")
      (eq? 'let (rcd/compile "(,@((% let) (0b1 1x)) $)")))

(test rcd-deep-catch-good-text-still-evaluates
      (= 3 (rcd/compile "(+ 1 2)"))
      (= 7 (rcd/compile "(if true 7 8)")))
