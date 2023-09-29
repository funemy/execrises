;; apply the simplifier
(declare-const a Int)
(assert (and (> a 0) (> a 1)))
(apply ctx-solver-simplify)
