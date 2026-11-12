module

public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic.Canonical (normSq normSq_mul normSq_nonneg)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

public section

namespace Purelib.Polynomial.Clearance.Box.Dominance.Scale

/-- Rational scaling in the closed unit interval does not increase a polynomial value's quadrance. -/
theorem eval_normSq_le (polynomial : CoefficientPolynomial) (time : Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) (value : Canonical) :
    normSq ((DensePolynomial.scale (⟨time, 0⟩ : Canonical) polynomial).eval value) ≤
      normSq (polynomial.eval value) := by
  have scalarNorm : normSq (⟨time, 0⟩ : Canonical) = time * time := by
    change time * time + 0 * 0 = time * time
    rw [Fraction.zero_mul, add_zero]
  have squareBound : time * time ≤ 1 := by
    calc
      time * time ≤ 1 * time := Arithmetic.mul_le_mul_of_nonneg_right_direct inside.2 inside.1
      _ = time := Fraction.one_mul time
      _ ≤ 1 := inside.2
  rw [DensePolynomial.eval_scale, normSq_mul, scalarNorm]
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct squareBound
    (normSq_nonneg _)).trans_eq (Fraction.one_mul _)

end Purelib.Polynomial.Clearance.Box.Dominance.Scale

namespace Purelib.Polynomial.Clearance.Box.Dominance.Basic.BoundaryNormDominance

/-- Scale the actual perturbation while retaining its original positive boundary-dominance margin.

Every rational parameter in the closed unit interval decreases the perturbation
quadrance. The original pointwise dominance certificate therefore supplies the
same margin on the same displayed box.
-/
@[expose] def scale {base perturbation : CoefficientPolynomial} {box : Box}
    (dominance : Basic.BoundaryNormDominance base perturbation box)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    Basic.BoundaryNormDominance base (DensePolynomial.scale (⟨time, 0⟩ : Canonical) perturbation) box where
  margin := dominance.margin
  positive := dominance.positive
  lower := by
    intro value boundary
    exact (dominance.lower value boundary).trans
      (Arithmetic.sub_le_sub_left_direct (Scale.eval_normSq_le perturbation time inside value) _)

/-- Scaling the perturbation retains exactly the original dominance margin. -/
theorem scale_margin {base perturbation : CoefficientPolynomial} {box : Box}
    (dominance : Basic.BoundaryNormDominance base perturbation box)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    (dominance.scale time inside).margin = dominance.margin := rfl

end Purelib.Polynomial.Clearance.Box.Dominance.Basic.BoundaryNormDominance

end
