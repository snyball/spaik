(println "Yay! I'm being loaded! I EXIIIIIIIIIIIST")

;; You can also modify the load-path from lisp, it is just a variable, although
;; since load runs during compilation, you have to modify sys/load-path during
;; compilation too!
(eval-when-compile
  (push sys/load-path "examples/resources"))
(load friends)
(friend)
(println ":^D")
