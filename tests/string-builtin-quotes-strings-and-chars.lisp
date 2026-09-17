(test string-builtin-plain-for-every-type
      ;; The two cases that were broken: no added syntax in the content.
      (= (len (string "hi")) 2)
      (eq? (string "hi") "hi")
      (= (len (string (%chr "A"))) 1)
      (eq? (string (%chr "A")) "A")
      ;; `string` agrees with the `(concat "" x)` route callers used to
      ;; have to take to dodge the repr form (lisp/html.lisp did this).
      (eq? (string "hi") (concat "" "hi"))
      (eq? (string (%chr "A")) (concat "" (%chr "A")))
      ;; Idempotent on strings.
      (eq? (string (string "hi")) "hi")
      ;; The types that were always fine stay fine.
      (eq? (string 42) "42")
      (eq? (string true) "true")
      (eq? (string 'sym) "sym"))
