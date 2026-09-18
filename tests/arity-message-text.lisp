;;; The exact wording of Argument Error, including the two spellings of
;;; "argument". Every other error test in this tree compares prefixes,
;;; which stops short of the word.

(defun amt/catch (tag form) (catch tag (eval form)))
(defun amt/starts-with? (prefix s)
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
(defun amt/msg? (tag prefix form)
  (let ((v (amt/catch tag form)))
    (and (string? v) (amt/starts-with? prefix v))))

;; The plural agrees with the number RECEIVED, not with the number the
;; sentence attaches it to. Got exactly 1 gives "argument"; got 0, or 2
;; or more, gives "arguments". Both readings are therefore wrong
;; whenever the two counts differ in plurality.
;;
;; `apply` shows it on its own: one expected count, two spellings,
;; chosen by how badly it was called.
(test amt-plural-follows-the-received-count
      (amt/msg? 'arg-error "Argument Error: apply expected 2 argument, but got 1"
                '(if (apply +) 1 2))
      (amt/msg? 'arg-error "Argument Error: apply expected 2 arguments, but got 4"
                '(if (apply + 1 2 (list 3)) 1 2)))

;; The same rule on a function that expects 1, where it reads plural for
;; a singular expectation.
(test amt-expected-one-still-reads-plural
      (amt/msg? 'arg-error "Argument Error: car expected 1 arguments, but got 0"
                '(if (car) 1 2))
      (amt/msg? 'arg-error "Argument Error: cons expected 2 argument, but got 1"
                '(if (cons 1) 1 2)))

;; A range of accepted counts takes the same suffix, where no reading is
;; singular.
(test amt-a-range-of-counts-pluralises-the-same-way
      (amt/msg? 'arg-error "Argument Error: nth expected from 2 to 3 argument, but got 1"
                '(if (nth (vec 1)) 1 2)))

;; Six builtins name their internal Rust function instead of themselves
;; (`%` reports as `modulo`, pinned further down with its type error).
;; The name in the message is not callable and is not in `(functions)`.
(test amt-some-builtins-report-an-internal-name
      (amt/msg? 'arg-error "Argument Error: is_void expected"
                '(if (void?) 1 2))
      (amt/msg? 'arg-error "Argument Error: split_list expected"
                '(if (split!) 1 2))
      (amt/msg? 'arg-error "Argument Error: sort_inplace expected"
                '(if (sort!) 1 2))
      (amt/msg? 'arg-error "Argument Error: reverse_inplace expected"
                '(if (reverse!) 1 2))
      (not (elem? 'split_list (functions)))
      (elem? 'split! (functions)))

;; The neighbouring predicates name themselves, which is what makes the
;; six above look like omissions rather than a convention.
(test amt-most-builtins-report-their-own-name
      (amt/msg? 'arg-error "Argument Error: nil? expected 1 arguments, but got 0"
                '(if (nil?) 1 2))
      (amt/msg? 'arg-error "Argument Error: unsigned-integer? expected 1 arguments, but got 0"
                '(if (unsigned-integer?) 1 2))
      (amt/msg? 'arg-error "Argument Error: keyword-name expected 1 arguments, but got 0"
                '(if (keyword-name) 1 2)))

;; The "at least N" path loses the received count: it reports 0 however
;; many arguments were passed. Pinned as what it says. `-` and `/` are
;; in the same family but have a minimum of 1, so 0 is the only way to
;; under-call them and their count is right by construction.
(test amt-at-least-n-always-reports-zero-received
      (amt/msg? 'arg-error "Argument Error: < expected at least 2 arguments, but got 0"
                '(if (< 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: >= expected at least 2 arguments, but got 0"
                '(if (>= 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: = expected at least 2 arguments, but got 0"
                '(if (= 1) 1 2))
      (amt/msg? 'arg-error "Argument Error: - expected at least 1 arguments, but got 0"
                '(if (-) 1 2)))

;; `%` answers to `modulo` when the arity is wrong and to `%` when the
;; types are. The type message asks for `(number number)` and then
;; refuses a float, which `number?` accepts.
;;
;; Its two failures also arrive under different TAGS while both messages
;; begin "Argument Error": the arity one is `arg-error`, the type one is
;; `type-error`. The message prefix is not a guide to the tag.
(test amt-percent-has-two-names-and-refuses-floats
      (amt/msg? 'arg-error "Argument Error: modulo expected 2 argument, but got 1"
                '(if (% 1) 1 2))
      (amt/msg? 'type-error "Argument Error: % expected (number number) but got (float integer)"
                '(if (% 7.5 2) 1 2))
      (number? 7.5)
      (= 1 (% 7 3))
      (= -1 (% -7 3)))
