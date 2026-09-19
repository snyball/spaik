;;; What each tag's payload IS, as a type: a symbol, a message string, or
;;; nil. A handler has only the payload to work with, so its shape is
;;; part of the contract. Companion to tests/error-throw-conversion.lisp.

(defun shp/catch (tag form) (catch tag (eval form)))

;;; ---[ symbol payloads ]-----------------------------------------------

(test shp-symbol-payloads
      ;; the two name-resolution tags hand back the offending SYMBOL, not
      ;; a message - so a handler can act on the name directly
      (symbol? (shp/catch 'undefined-variable 'shp-no-such-global))
      (symbol? (shp/catch 'undefined-function '(shp-no-such-fn)))
      (eq? 'shp-no-such-global (shp/catch 'undefined-variable 'shp-no-such-global))
      (eq? 'shp-no-such-fn (shp/catch 'undefined-function '(shp-no-such-fn)))
      ;; not a string, which is what every other VM-raised tag gives
      (not (string? (shp/catch 'undefined-variable 'shp-no-such-global))))

;;; ---[ string payloads ]-------------------------------------------------

(test shp-string-payloads
      ;; everything the VM raises with a message hands back that message
      (string? (shp/catch 'type-error '(car 5)))
      (string? (shp/catch 'arg-error '(car)))
      (string? (shp/catch 'index-error '(get (vec) 0)))
      (string? (shp/catch 'unimplemented '(read "1")))
      (string? (shp/catch 'module-not-found '(require shp-no-such-module)))
      (string? (shp/catch 'reference-not-allowed '(error 'shp-k (list 1))))
      ;; and the message is non-empty, so a handler can print it
      (< 0 (len (shp/catch 'type-error '(car 5))))
      (< 0 (len (shp/catch 'module-not-found '(require shp-no-such-module)))))

;;; ---[ nil payloads ]----------------------------------------------------

(test shp-nil-payloads
      ;; divide-by-zero carries no message object at all; the tag is the
      ;; whole of the information
      (nil? (shp/catch 'divide-by-zero '(/ 1 0)))
      (nil? (shp/catch 'divide-by-zero '(% 1 0)))
      ;; so do fmt's four, which are `(error 'tag)` with no payload
      (nil? (shp/catch 'trailing-delimiter '(fmt "a}b")))
      (nil? (shp/catch 'unclosed-delimiter '(fmt "a{b")))
      (nil? (shp/catch 'not-enough-format-arguments '(fmt "{}")))
      (nil? (shp/catch 'unused-format-parameters '(fmt "x" 1)))
      ;; ... and so does `(error 'tag)` written by hand
      (nil? (shp/catch 'shp-k '(error 'shp-k))))

;;; ---[ one tag, two payload shapes ]--------------------------------------

;; The hazard worth pinning: the SAME tag arrives with a message string
;; when the VM raised it and with a bare type SYMBOL when
;; `lisp/core.lisp` raised it by hand. A handler that assumes a string
;; will break on the stdlib path.

(test shp-same-tag-two-shapes
      ;; type-error: a message from `car` ...
      (string? (shp/catch 'type-error '(car 5)))
      ;; ... and the container type as a symbol from `nth`'s own check,
      ;; whose sequence argument is the SECOND one
      (symbol? (shp/catch 'type-error '(nth 0 5)))
      (eq? 'integer (shp/catch 'type-error '(nth 0 5)))
      (not (string? (shp/catch 'type-error '(nth 0 5))))
      ;; `empty` is the same shape: the container type of whatever was
      ;; found to be empty
      (eq? 'vec (shp/catch 'empty '(min (vec))))
      (eq? 'list (shp/catch 'empty '(min nil)))
      ;; index-error has only the VM shape left: `nth` answers `alt` for
      ;; a missing index instead of raising, so `get` is the only source
      (string? (shp/catch 'index-error '(get (vec 1 2) 9)))
      (eq? :shp-else (shp/catch 'index-error '(if (nth 9 (vec 1 2)) :shp-then :shp-else)))
      (eq? :shp-else (shp/catch 'index-error '(if (nth 9 (list 1 2)) :shp-then :shp-else)))
      (eq? :shp-else (shp/catch 'index-error '(if (nth 0 nil) :shp-then :shp-else)))
      ;; `negative-index` is a third shape again: a bare integer, the
      ;; index that was out of range
      (= -1 (shp/catch 'negative-index '(if (nth -1 (vec 1 2)) :shp-then :shp-else)))
      (not (string? (shp/catch 'negative-index '(if (nth -1 (vec 1 2)) :shp-then :shp-else)))))

;;; ---[ user payloads round-trip unchanged ]--------------------------------

(test shp-user-payloads
      ;; whatever immediate `(error 'tag x)` was given comes back as-is,
      ;; with its type intact
      (= 42 (shp/catch 'shp-k '(error 'shp-k 42)))
      (= 1.5 (shp/catch 'shp-k '(error 'shp-k 1.5)))
      (eq? :kw (shp/catch 'shp-k '(error 'shp-k :kw)))
      (eq? 'sym (shp/catch 'shp-k '(error 'shp-k 'sym)))
      (= true (shp/catch 'shp-k '(error 'shp-k true)))
      (= false (shp/catch 'shp-k '(error 'shp-k false)))
      ;; the types really are distinct, not all coerced to one
      (integer? (shp/catch 'shp-k '(error 'shp-k 42)))
      (not (integer? (shp/catch 'shp-k '(error 'shp-k 1.5))))
      (symbol? (shp/catch 'shp-k '(error 'shp-k 'sym)))
      (not (string? (shp/catch 'shp-k '(error 'shp-k 'sym)))))
