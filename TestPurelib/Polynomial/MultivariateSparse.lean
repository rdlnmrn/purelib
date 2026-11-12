module

import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Data.Gaussian.Basic

/-!
# Finite sparse normalization regressions

Closed coefficient checks exercise cancellation, complete convolution, arity
zero and non-real Gaussian coefficients. The scalar evaluation laws quantify
over arbitrary environments rather than sampled numerical values.
-/

namespace TestPurelib.Polynomial.MultivariateSparse

open Purelib.Polynomial.Multivariate
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The first original variable in the two-variable coefficient tests. -/
private def x : Sparse Canonical 2 := Sparse.atom ⟨0, by decide⟩

/-- The second original variable in the two-variable coefficient tests. -/
private def y : Sparse Canonical 2 := Sparse.atom ⟨1, by decide⟩

/-- The retained canonical constant polynomial with coefficient one. -/
private def one : Sparse Canonical 2 := Sparse.constant 1

/-- The expanded polynomial identity whose cancellation leaves the constant one. -/
private def expanded : Sparse Canonical 2 :=
  Sparse.sub (Sparse.sub (Sparse.mul (Sparse.add x one) (Sparse.add x one)) (Sparse.mul x x))
    (Sparse.mul (Sparse.constant 2) x)

example : expanded.terms = one.terms := by decide

example : (Sparse.sub (Sparse.add x y) (Sparse.add y x)).terms = [] := by decide

example : (Sparse.sub (Sparse.mul x (Sparse.add x y))
    (Sparse.add (Sparse.mul x x) (Sparse.mul x y))).terms = [] := by decide

example : (Sparse.mul (Sparse.constant (⟨0, 1⟩ : Canonical) : Sparse Canonical 0)
    (Sparse.constant ⟨0, 1⟩)).terms = (Sparse.constant (-1 : Canonical) : Sparse Canonical 0).terms := by decide

example : (Sparse.constant (0 : Canonical) : Sparse Canonical 0).terms = [] := by decide

example (environment : Fin 2 → Canonical) :
    Sparse.eval environment (Sparse.sub (Sparse.add x y) (Sparse.add y x)) = 0 := by
  rewrite [Sparse.eval_sub, Sparse.eval_add, Sparse.eval_add, add_comm (Sparse.eval environment x)]
  exact sub_self _

example (environment : Fin 2 → Canonical) : Sparse.eval environment expanded = 1 := by
  have normalized : expanded.terms = one.terms := by decide
  change Terms.eval environment expanded.terms = _
  rewrite [normalized]
  exact Sparse.eval_constant environment 1

end TestPurelib.Polynomial.MultivariateSparse
