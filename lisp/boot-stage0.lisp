;; Stage 0 of the SPAIK bootup process, this has to be a separate compilation
;; unit from core.lisp because the set-macro function must run so that
;; set-macro! becomes available by the time core.lisp is compiled.

(define (<ξ>::set-macro! macro fn)
  (set-macro macro fn)
  nil)

(set-macro 'set-macro! '<ξ>::set-macro!)
