;; Stage 0 of the SPAIK bootup process, this has to be a separate compilation
;; unit from core.lisp because the set-macro function must run so that
;; set-macro! becomes available by the time core.lisp is compiled.

(define (<ξ>-set-macro! macro fn)
  (sys/set-macro macro fn)
  nil)

(define (<ξ>-set-macro-character! macro fn)
  (sys/set-macro-character macro fn)
  nil)

(sys/set-macro 'set-macro! '<ξ>-set-macro!)

(sys/set-macro 'set-macro-character! '<ξ>-set-macro-character!)
