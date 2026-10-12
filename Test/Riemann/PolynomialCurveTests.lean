module
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic

open Purelib.Curves.Hyperelliptic.Preparation

open Purelib.Polynomial.Dense.Gaussian

@[expose] public section

/-!
Small kernel-checked regressions for raw polynomial preparation.  These test
the new input algorithm, not generated Legendre observations or their runtime.
-/

namespace Test.Riemann.PolynomialCurveTests

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Curves.Hyperelliptic.Preparation.Polynomial

/-- Read the raw polynomial preparation outcome, square-factor degree, reduced radicand degree and genus. -/
public def profile (polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Nat × Nat × Nat × Nat :=
  match Polynomial.prepare polynomial with
  | .zero _ => (0, 0, 0, 0)
  | .constantInput _ _ reduction _ =>
      (1, reduction.squareFactor.natDegree, reduction.radicand.natDegree, 0)
  | .squareTimesConstant _ _ reduction _ =>
      (2, reduction.squareFactor.natDegree, reduction.radicand.natDegree, 0)
  | .regular _ prepared =>
      (3, prepared.reduction.squareFactor.natDegree,
        prepared.reduction.radicand.natDegree, prepared.genus)

/-- Leading-zero normalization preserves the distinct zero and nonzero constant preparation outcomes. -/
theorem zero_and_constant :
    profile ⟨[0, 0]⟩ = (0, 0, 0, 0) ∧
      profile ⟨[0, 0, 2]⟩ = (1, 0, 0, 0) := by
  decide +kernel

/-- The displayed linear and quadratic radicands prepare as regular genus-zero inputs. -/
theorem genus_zero_degrees :
    profile ⟨[0, 1, 1]⟩ = (3, 0, 1, 0) ∧
      profile ⟨[1, 0, 1]⟩ = (3, 0, 2, 0) := by
  decide +kernel

/-- `(x-1)^2` is square-times-constant, not a genus-zero positive-degree hyperelliptic input. -/
theorem square_times_constant :
    profile ⟨[1, -2, 1]⟩ = (2, 1, 0, 0) := by
  decide +kernel

/-- `(x-1)^2*(x+1)` loses the even-multiplicity factor entirely. Taking the radical would incorrectly leave a degree-two
reduced radicand. -/
theorem repeated_factor_parity :
    profile ⟨[1, -1, -1, 1]⟩ = (3, 1, 1, 0) := by
  decide +kernel

/-- `2*(x-1)^2*(x^3-x-1)` has a genus-one reduced radicand, not genus two from the unreduced degree-five equation. The
scalar requires no square root. -/
theorem reduced_genus_and_scalar :
    profile ⟨[2, -4, 0, 2, 2, -2]⟩ = (3, 1, 3, 1) := by
  decide +kernel

/-- Read the exact computed reduced radicand from a regular polynomial preparation. -/
public def retainedRadicand (polynomial :
  Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : Option GaussianPolynomial :=
  match Polynomial.prepare polynomial with
  | .regular _ prepared => some prepared.reduction.radicand
  | .zero _ | .constantInput .. | .squareTimesConstant .. => none

/-- Already squarefree odd/even-degree inputs retain their actual normalized coefficients, including a scalar which must
not be discarded. -/
theorem squarefree_coefficients_preserved :
    retainedRadicand ⟨[0, 2, 0, -2, -2]⟩ = some ⟨[2, 0, -2, -2]⟩ ∧
      retainedRadicand ⟨[1, 0, 0, 0, 1]⟩ = some ⟨[1, 0, 0, 0, 1]⟩ ∧
      profile ⟨[1, 0, 0, 0, 1]⟩ = (3, 0, 4, 1) := by
  decide +kernel

end Test.Riemann.PolynomialCurveTests
