;;; The `error` builtin and the stdlib diagnostics built on it, as
;;; catchable throws - including `fmt`'s four, raised at macroexpansion.
;;; Catch outside, eval inside, eval in tail position.

;;; ---[ helpers ]-----------------------------------------------------

(defun errb/catch (tag form)
  (catch tag (eval form)))

(defun errb/starts-with? (prefix s)
  (let ((pit (iter prefix))
        (sit (iter s)))
    (loop
     (let ((p (next pit)))
       (if (iter-end? p)
           (break true)
         (let ((c (next sit)))
           (if (iter-end? c)
               (break nil)
             (unless (= p c)
               (break nil)))))))))

;;; ---[ tag and payload ]----------------------------------------------

(defun errb/keyword-payload () (errb/catch 'errb-my-error '(error 'errb-my-error :thing)))
(defun errb/no-payload ()      (errb/catch 'errb-my-error '(error 'errb-my-error)))
(defun errb/int-payload ()     (errb/catch 'errb-my-error '(error 'errb-my-error 42)))
(defun errb/float-payload ()   (errb/catch 'errb-my-error '(error 'errb-my-error 1.5)))
(defun errb/symbol-payload ()  (errb/catch 'errb-my-error '(error 'errb-my-error 'sym)))
(defun errb/true-payload ()    (errb/catch 'errb-my-error '(error 'errb-my-error true)))
(defun errb/false-payload ()   (errb/catch 'errb-my-error '(error 'errb-my-error false)))
(defun errb/nil-payload ()     (errb/catch 'errb-my-error '(error 'errb-my-error nil)))

(test errb-error-payload-round-trips
      ;; the example from the feature description
      (eq? :thing (errb/keyword-payload))
      ;; one argument means a `nil` payload
      (nil? (errb/no-payload))
      ;; every immediate type survives the round trip unchanged
      (= 42 (errb/int-payload))
      (= 1.5 (errb/float-payload))
      (eq? 'sym (errb/symbol-payload))
      (= true (errb/true-payload))
      (= false (errb/false-payload))
      (nil? (errb/nil-payload))
      ;; `false` and a missing payload are distinguishable
      (not (= (errb/false-payload) (errb/no-payload))))

;;; ---[ the tag is matched, and only the tag ]---------------------------

(defun errb/wrong-tag-falls-through ()
  ;; inner tag does not match, so the enclosing one takes it
  (catch 'errb-outer (errb/catch 'errb-inner '(error 'errb-outer :v))))

(defun errb/computed-tag ()
  (errb/catch 'errb-my-error '(error (intern "errb-my-error") 5)))

(defun errb/tag-shaped-like-a-builtin-error ()
  ;; a user tag that collides with one of the interpreter's own error
  ;; names is still just a tag, and carries the user's payload
  (errb/catch 'type-error '(error 'type-error :mine)))

(defun errb/tag-shaped-like-a-special-form ()
  (errb/catch 'catch '(error 'catch 1)))

(defun errb/from-a-nested-frame () (errb/catch 'errb-boom '(errb/raiser)))
(defun errb/raiser () (error 'errb-boom :deep))

(test errb-error-tag-matching
      (eq? :v (errb/wrong-tag-falls-through))
      (= 5 (errb/computed-tag))
      (eq? :mine (errb/tag-shaped-like-a-builtin-error))
      (= 1 (errb/tag-shaped-like-a-special-form))
      ;; the raise can be arbitrarily deep inside the evaluated form
      (eq? :deep (errb/from-a-nested-frame)))

;;; ---[ what `error` refuses ]--------------------------------------------

(defun errb/non-symbol-tag ()
  (let ((v (errb/catch 'type-error '(error "not-a-symbol"))))
    (and (string? v) (errb/starts-with? "Type Error: " v))))

(defun errb/list-payload ()
  (let ((v (errb/catch 'reference-not-allowed '(error 'errb-my-error (list 1 2)))))
    (and (string? v) (errb/starts-with? "Reference types are not allowed" v))))

(defun errb/string-payload () (errb/catch 'reference-not-allowed '(error 'errb-my-error "s")))
(defun errb/vec-payload ()    (errb/catch 'reference-not-allowed '(error 'errb-my-error (vec 1))))

(test errb-error-argument-rules
      ;; the tag must be a symbol
      (errb/non-symbol-tag)
      ;; the payload must be an IMMEDIATE - an integer, float, symbol,
      ;; keyword, true, false or nil. Anything heap-allocated raises
      ;; `reference-not-allowed` in place of the tag you asked for. That
      ;; is intended behaviour, not a defect; `throw` has no such
      ;; restriction. What is pinned here is the diagnostic produced.
      (errb/list-payload)
      (string? (errb/string-payload))
      (string? (errb/vec-payload)))

;;; ---[ fmt: the four diagnostics ]-----------------------------------------

;; `fmt`'s scanner has two states and no escape for a literal brace.
;; `{` always opens a span; `}` closes it - an EMPTY span consumes one
;; positional argument, a non-empty one is interned as a variable name.

(defun errb/fmt-trailing ()   (errb/catch 'trailing-delimiter '(fmt "a}b")))
(defun errb/fmt-unclosed ()   (errb/catch 'unclosed-delimiter '(fmt "a{b")))
(defun errb/fmt-not-enough () (errb/catch 'not-enough-format-arguments '(fmt "{}")))
(defun errb/fmt-unused ()     (errb/catch 'unused-format-parameters '(fmt "x" 1)))

(defun errb/fmt-not-enough-partial () (errb/catch 'not-enough-format-arguments '(fmt "{} {}" 1)))
(defun errb/fmt-unused-extra ()       (errb/catch 'unused-format-parameters '(fmt "{}" 1 2)))

(test errb-fmt-diagnostics
      ;; All four were previously "verified by hand" only. The payload is
      ;; `nil` for each - `fmt` calls `(error 'tag)` with no second
      ;; argument - so the tag is the whole of the assertion, which is
      ;; exactly what needed pinning: each malformed string must pick the
      ;; RIGHT diagnostic.
      (nil? (errb/fmt-trailing))
      (nil? (errb/fmt-unclosed))
      (nil? (errb/fmt-not-enough))
      (nil? (errb/fmt-unused))
      (nil? (errb/fmt-not-enough-partial))
      (nil? (errb/fmt-unused-extra)))

(defun errb/fmt-wrong-tag-falls-through ()
  ;; `(fmt "a}b")` is a trailing-delimiter and NOT an unclosed-delimiter:
  ;; catching the wrong one lets it through to the enclosing catch
  (catch 'trailing-delimiter (errb/catch 'unclosed-delimiter '(fmt "a}b"))))

(defun errb/fmt-unclosed-wrong-tag-falls-through ()
  (catch 'unclosed-delimiter (errb/catch 'trailing-delimiter '(fmt "a{b"))))

(test errb-fmt-diagnostics-are-distinct
      ;; each of the four is its own tag, not interchangeable
      (nil? (errb/fmt-wrong-tag-falls-through))
      (nil? (errb/fmt-unclosed-wrong-tag-falls-through)))

;;; ---[ fmt: the brace-scanner rules, now assertable ]------------------------

;; `{{}}` is not an escaped brace - it is two openers and two closers.
;; The first `}` closes an empty span (so it reads as a positional `{}`),
;; and the second has nothing left open.
(defun errb/fmt-double-brace-no-args () (errb/catch 'not-enough-format-arguments '(fmt "{{}}")))
(defun errb/fmt-double-brace-one-arg () (errb/catch 'trailing-delimiter '(fmt "{{}}" 1)))
(defun errb/fmt-double-brace-two-args () (errb/catch 'trailing-delimiter '(fmt "{{}}" 1 2)))
(defun errb/fmt-double-open ()  (errb/catch 'unclosed-delimiter '(fmt "{{")))
(defun errb/fmt-double-close () (errb/catch 'trailing-delimiter '(fmt "}}")))
(defun errb/fmt-percent-close () (errb/catch 'trailing-delimiter '(fmt "100%}")))

(test errb-fmt-has-no-brace-escape
      ;; `fmt` has NO escape for a literal brace, so each of these is a
      ;; diagnostic rather than output. Every one of them used to be
      ;; unassertable: raising killed the whole file.
      (nil? (errb/fmt-double-brace-no-args))
      (nil? (errb/fmt-double-brace-one-arg))
      (nil? (errb/fmt-double-brace-two-args))
      (nil? (errb/fmt-double-open))
      (nil? (errb/fmt-double-close))
      (nil? (errb/fmt-percent-close)))

;; A non-empty span is interned as a VARIABLE NAME, so brace-bearing text
;; usually fails as an undefined variable naming text nobody meant as a
;; name. The payload of `undefined-variable` is that symbol, so the exact
;; name the scanner invented can be pinned.
(defun errb/fmt-json-name () (errb/catch 'undefined-variable '(fmt "{\"json\": 1}")))
(defun errb/fmt-css-name ()  (errb/catch 'undefined-variable '(fmt "body { margin: 0 }")))

(test errb-fmt-interns-braced-text-as-a-variable-name
      (eq? (intern "\"json\": 1") (errb/fmt-json-name))
      (eq? (intern " margin: 0 ") (errb/fmt-css-name))
      (symbol? (errb/fmt-json-name)))

;; The one genuinely silent corner of the scanner: a stray `{` inside an
;; open span flushes the partial name as LITERAL text and reopens, with
;; no diagnostic at all. No error to catch here - this is the
;; value-producing half, and it is pinned so the silent path cannot drift
;; unnoticed while the loud ones are covered above.
(define errb/b 5)
(defun errb/fmt-reopen ()          (fmt "{a{errb/b}"))
(defun errb/fmt-reopen-positional () (fmt "A{junk{}" 9))

(test errb-fmt-stray-open-brace-reopens-silently
      (eq? "a5" (errb/fmt-reopen))
      (eq? "Ajunk9" (errb/fmt-reopen-positional)))

;;; ---[ println/print inherit fmt's diagnostics ]-----------------------------

(defun errb/println-unused ()   (errb/catch 'unused-format-parameters '(println "x" 1)))
(defun errb/println-trailing () (errb/catch 'trailing-delimiter '(println "100%}")))
(defun errb/print-unclosed ()   (errb/catch 'unclosed-delimiter '(print "a{b")))

(test errb-println-inherits-fmt-diagnostics
      ;; `println`/`print` route through `fmt` when the first argument is
      ;; a string literal, so they raise the same four.
      (nil? (errb/println-unused))
      (nil? (errb/println-trailing))
      (nil? (errb/print-unclosed)))

;;; ---[ the documented workarounds still do not raise ]-----------------------

(define errb/lb "{")
(define errb/rb "}")
(define errb/name "spaik")
(define errb/blob "{a} {} }{")

(defun errb/wa-concat ()     (concat "{" "\"json\": 1" "}"))
(defun errb/wa-named ()      (fmt "{errb/lb}\"name\": \"{errb/name}\"{errb/rb}"))
(defun errb/wa-positional () (fmt "{}\"n\": 1{}" errb/lb errb/rb))
(defun errb/wa-value-not-rescanned () (fmt "{}" errb/blob))

(test errb-fmt-workarounds-do-not-raise
      ;; Substituted VALUES are never rescanned, so braces inside one are
      ;; safe; only the format string itself is parsed.
      (eq? "{\"json\": 1}" (errb/wa-concat))
      (eq? "{\"name\": \"spaik\"}" (errb/wa-named))
      (eq? "{\"n\": 1}" (errb/wa-positional))
      (eq? "{a} {} }{" (errb/wa-value-not-rescanned)))
