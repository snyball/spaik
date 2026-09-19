;;; Which `catch` handlers a resumed continuation can reach: the ones
;;; that were live when it was CAPTURED, not the ones the resuming code
;;; set up around the resume. Plain call/cc re-entry is the control.

(defvar cst/k nil)
(defvar cst/inner-ran nil)
(defvar cst/saved nil)

;;; ---[ a handler set up around the resume is not in scope ]----------------

;; `cst/gen` captures a continuation, throws `cst-tag` to get out, and -
;; when resumed - throws `cst-other`. Resuming reinstates the stack that
;; was live at the capture, so the handler that decides where
;; `cst-other` lands is whichever one was on THAT stack.

(defun cst/gen ()
  (call/cc (lambda (kk) (set cst/k kk) (throw 'cst-tag 1)))
  (throw 'cst-other 2))

;; The resuming helper wraps the resume in its own `cst-other` handler.
;; That handler is established after the capture, is not on the
;; reinstated stack, and must not see the throw. `cst/inner-ran` is the
;; witness: the helper never gets to run its own tail.
(defun cst/step (kk)
  (let ((v (catch 'cst-other (kk nil))))
    (set cst/inner-ran true)
    v))

;; The outer handler IS established before the capture, so it is the one
;; that catches. A stale handler used to be selected here instead, and
;; the return out of it popped a frame that was not its own - which hung
;; the program rather than answering anything.
(defun cst/drive ()
  (set cst/inner-ran false)
  (catch 'cst-other
    (let ((r (catch 'cst-tag (cst/gen))))
      (cst/step cst/k))))

(defun cst/outer-catches ()   (cst/drive))
(defun cst/inner-did-run? ()  (progn (cst/drive) cst/inner-ran))

;; Without a resume there is nothing to reinstate: the `cst-tag` throw is
;; caught where it is written and `cst-other` is never reached.
(defun cst/no-resume ()
  (catch 'cst-other
    (catch 'cst-tag (cst/gen))))

;; And with no continuation anywhere near it, a helper's own handler
;; catches its own throw - the property the case above is contrasted
;; against, so that a regression cannot pass by breaking `catch` itself.
(defun cst/plain-catch ()
  (catch 'cst-other (throw 'cst-other 7)))

;;; ---[ the control: call/cc with no catch and no throw ]-------------------

;; Re-entering a continuation with a new value makes `call/cc` answer
;; that value. If this line ever changes, the break is in `call/cc`
;; itself rather than in the handler scoping above.
(defun cst/plain-callcc ()
  (let ((v (call/cc (lambda (k) (set cst/saved k) 1))))
    (when (= v 1)
      (let ((k cst/saved))
        (k 99)))
    v))

(test cst-resume-reaches-only-capture-time-handlers
      (= 2 (cst/outer-catches))
      (not (cst/inner-did-run?)))

(test cst-handlers-are-unaffected-without-a-resume
      (= 1 (cst/no-resume))
      (= 7 (cst/plain-catch)))

(test cst-plain-callcc-re-entry
      (= 99 (cst/plain-callcc)))
