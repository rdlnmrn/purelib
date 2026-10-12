module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Specialization
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-! ## Finite specialization and outer normalization -/

/-- Evaluate every inner coefficient, leaving a dense polynomial in the outer
variable. -/
def atInner (inner : K) (p :
  Dense.Bivariate.Basic.DenseBivariate K) : Polynomial.Dense.Basic.CoefficientPolynomial K :=
  ⟨p.coeffs.map (fun coefficient => coefficient.eval inner)⟩

omit [DecidableEq K] in
/-- Evaluating the specialized outer polynomial agrees with bivariate evaluation at the retained inner argument. -/
@[simp] theorem eval_atInner (p :
  Dense.Bivariate.Basic.DenseBivariate K) (outer inner : K) :
    (atInner inner p).eval outer = Dense.Bivariate.Basic.eval p outer inner := by
  have mapped : ∀ (coefficients : List (Polynomial.Dense.Basic.CoefficientPolynomial K))
      (accumulator : K),
      (coefficients.map (fun coefficient => coefficient.eval inner)).foldl
          (fun value coefficient => value * outer + coefficient) accumulator =
        coefficients.foldl
          (fun value coefficient => value * outer + coefficient.eval inner)
          accumulator := by
    intro coefficients accumulator
    induction coefficients generalizing accumulator with
    | nil => rfl
    | cons coefficient remaining inductionHypothesis =>
        simp only [List.map_cons, List.foldl_cons]
        exact inductionHypothesis _
  exact mapped p.coeffs 0
end Purelib.Polynomial.Dense.Bivariate.Specialization

end
