module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Curves.Legendre.Paths
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Extensionality
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Legendre

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Linear

open Purelib.Polynomial.Dense.Gaussian.Linear.Translated

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Curves.Legendre.Polynomial

/-- Multiply the three exact affine factors with roots zero, the parameter and one. -/
def factorsAt (lambda : Data.Gaussian.Basic.Canonical) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  (Translated.translatedCoordinate 0 *
    Translated.translatedCoordinate lambda) *
      Translated.translatedCoordinate 1

/-- The displayed three affine factors are coefficientwise the Legendre cubic, uniformly in the rational parameter. -/
theorem polynomial_eq_factorsAt (lambda : Data.Gaussian.Basic.Canonical) :
    Paths.polynomial lambda = factorsAt lambda := by
  apply Extensionality.normalized_eq_of_sub_isZero
  · apply DensePolynomial.ext
    rfl
  · exact DensePolynomial.normalize_mul _ _
  · apply NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro point _member
    rw [Paths.polynomial_eval, factorsAt,
      DensePolynomial.eval_mul,
      DensePolynomial.eval_mul]
    simp only [Translated.translatedCoordinate_eval]
    ring1

/-! ## One finite coefficient overlap -/

/-- Coefficient perturbation for moving the Legendre root between any two displayed Gaussian-rational parameters. -/
def perturbationAt (source target : Data.Gaussian.Basic.Canonical) :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  Paths.polynomial target - Paths.polynomial source

/-- Changing the displayed Legendre parameter is exactly addition of the finite coefficient perturbation, uniformly in
both rational endpoints. -/
theorem target_eq_source_add_perturbationAt (source target :
  Data.Gaussian.Basic.Canonical) :
    Paths.polynomial target = Paths.polynomial source + perturbationAt source target := by
  apply Extensionality.normalized_eq_of_sub_isZero
  · apply DensePolynomial.ext
    rfl
  · exact DensePolynomial.normalize_add _ _
  · apply NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro point _member
    rw [DensePolynomial.eval_add,
      perturbationAt, DensePolynomial.eval_sub]
    ring1

/-- The Legendre polynomial evaluates to the product of its three exact affine factor values. -/
theorem polynomial_eval_factorsAt (lambda point :
  Data.Gaussian.Basic.Canonical) :
    (Paths.polynomial lambda).eval point =
      (Purelib.Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate 0).eval point *
        (Purelib.Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate lambda).eval point *
        (Purelib.Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate 1).eval point := by
  rw [Paths.polynomial_eval]
  simp only [Translated.translatedCoordinate_eval]
  ring1

/-- The parameter perturbation evaluates to the fixed zero-one factor product times source minus target. -/
theorem perturbationAt_eval (source target point :
  Data.Gaussian.Basic.Canonical) :
    (perturbationAt source target).eval point =
      (Purelib.Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate 0).eval point *
        (Purelib.Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate 1).eval point *
        (source - target) := by
  rw [perturbationAt, DensePolynomial.eval_sub,
    Paths.polynomial_eval, Paths.polynomial_eval]
  simp only [Translated.translatedCoordinate_eval]
  ring1
end Purelib.Curves.Legendre.Polynomial

end
