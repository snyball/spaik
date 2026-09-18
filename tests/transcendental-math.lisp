;;; The float math builtins: trig, inverse trig, hyperbolics, logs.
;;; Checked by identity and round-trip rather than by literal values -
;;; these are f32, so a literal would pin the rounding, not the function.

;; Every comparison here goes through this: the results are f32 and
;; `(ln 2.718281828459045)` is 0.99999994, not 1.
(defun tcm/close? (a b) (< (abs (- a b)) 0.0001))

;;; ---[ the named-pair mix-ups these would catch ]-----------------------

;; `sin` and `cos` were once the same function, so the exact values at 0
;; are pinned: they are the only two arguments where sin and cos differ
;; by a whole unit and no rounding is involved.
(test tcm-sin-and-cos-are-not-each-other
      (tcm/close? 0.0 (sin 0.0))
      (tcm/close? 1.0 (cos 0.0))
      (tcm/close? 0.0 (tan 0.0))
      (tcm/close? 1.0 (sin 1.5707964))
      (tcm/close? 0.0 (cos 1.5707964)))

(test tcm-pythagorean-identity
      (tcm/close? 1.0 (+ (* (sin 0.7) (sin 0.7)) (* (cos 0.7) (cos 0.7))))
      (tcm/close? 1.0 (+ (* (sin 2.4) (sin 2.4)) (* (cos 2.4) (cos 2.4))))
      ;; tan is sin/cos, not something else with the same shape
      (tcm/close? (tan 0.7) (/ (sin 0.7) (cos 0.7))))

;;; ---[ inverses ]-------------------------------------------------------

;; Each inverse is checked against its own forward function rather than
;; against a constant, so a swapped pair (asin answering acos, say) fails
;; even though both would still be "a plausible angle".
(test tcm-inverse-trig-round-trips
      (tcm/close? 0.5 (asin (sin 0.5)))
      (tcm/close? 0.5 (acos (cos 0.5)))
      (tcm/close? 0.5 (atan (tan 0.5)))
      ;; and the standard values, which separate asin from acos
      (tcm/close? 0.0 (asin 0.0))
      (tcm/close? 1.5707964 (acos 0.0)))

;; `atan2` takes y first, then x - the quadrant-aware form. The three
;; cases below are exactly the ones that go wrong when the arguments are
;; swapped: (1,1) is symmetric and survives a swap, (0,1) and (1,0) do not.
(test tcm-atan2-takes-y-then-x
      (tcm/close? 0.7853982 (atan2 1.0 1.0))
      (tcm/close? 0.0 (atan2 0.0 1.0))
      (tcm/close? 1.5707964 (atan2 1.0 0.0))
      (tcm/close? -0.7853982 (atan2 -1.0 1.0)))

;;; ---[ hyperbolics ]----------------------------------------------------

(test tcm-hyperbolic-round-trips
      (tcm/close? 0.5 (asinh (sinh 0.5)))
      (tcm/close? 0.5 (acosh (cosh 0.5)))
      (tcm/close? 0.5 (atanh (tanh 0.5)))
      ;; cosh^2 - sinh^2 = 1, the hyperbolic identity
      (tcm/close? 1.0 (- (* (cosh 1.3) (cosh 1.3)) (* (sinh 1.3) (sinh 1.3))))
      ;; and they are not the circular functions wearing a different name
      (tcm/close? 1.0 (cosh 0.0))
      (tcm/close? 0.0 (sinh 0.0)))

;;; ---[ logs and roots ]-------------------------------------------------

;; `logn` is (logn x base), not (logn base x): the two disagree here, and
;; log10 fixes the base at 10.
(test tcm-logs-agree-on-their-base
      (tcm/close? 3.0 (logn 8.0 2.0))
      (tcm/close? 3.0 (log10 1000.0))
      (tcm/close? 1.0 (ln 2.718281828459045))
      (tcm/close? (ln 7.0) (logn 7.0 2.718281828459045))
      (tcm/close? (log10 7.0) (logn 7.0 10.0)))

(test tcm-sqrt-and-pow-agree
      (tcm/close? 2.0 (sqrt 4.0))
      (tcm/close? 1.4142135 (sqrt 2.0))
      (tcm/close? (sqrt 7.0) (pow 7.0 0.5))
      (tcm/close? 8.0 (pow 2.0 3.0)))
