module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Basic
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace Purelib.Polynomial.Clearance.Box.Dominance.Majorant

/-- Turn norm dominance into a boundary clearance with a deliberately
displayed bound.  `majorant` is any positive upper bound for the dominant
summand on the boundary; retaining it in the result makes later coefficient
precision requests predictable before the next polynomial is read. -/
def boundaryClearance_add_of_dominance_with_majorant
    (base error : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance base error box)
    (majorant : Fraction.Rational) (majorantPositive : 0 < majorant)
    (baseUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary box z →
        Canonical.normSq (base.eval z) ≤ majorant) :
    Clearance.Box.Boundary.Basic.BoundaryClearance (base + error) box where
  bound := dominance.margin ^ 2 / (4 * majorant)
  positive := Purelib.Data.Rat.Fraction.Order.Field.div_pos_direct
    (Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct dominance.positive 2)
    (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive)
  lower := by
    intro z boundary
    let left := base.eval z
    let right := error.eval z
    let sum := (base + error).eval z
    let dot := left.re * sum.re + left.im * sum.im
    have sumIdentity : sum = left + right := by
      dsimp only [sum, left, right]
      exact Dense.Basic.DensePolynomial.eval_add _ _ _
    have sumNonnegative : 0 ≤ Canonical.normSq sum := Canonical.normSq_nonneg sum
    have doubledDot : 2 * dot =
        (Canonical.normSq left - Canonical.normSq right) + Canonical.normSq
          sum := by
      dsimp only [dot]
      rw [sumIdentity]
      simp only [Canonical.normSq, Gaussian.Basic.add_re, Gaussian.Basic.add_im]
      ring1
    have marginLeDoubledDot : dominance.margin ≤ 2 * dot := by
      rw [doubledDot]
      exact (dominance.lower z boundary).trans
        (le_add_of_nonneg_right sumNonnegative)
    have squaredMargin : dominance.margin ^ 2 ≤ (2 * dot) ^ 2 :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_le_pow_direct dominance.positive.le
        marginLeDoubledDot 2
    have dotCauchy : dot ^ 2 ≤ Canonical.normSq left * Canonical.normSq sum := by
      dsimp only [dot]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
        Purelib.Data.Gaussian.Norm.Bounds.gaussian_dot_sq_le_product_normSq left sum
    have scaledCauchy : (2 * dot) ^ 2 ≤
        (4 * majorant) * Canonical.normSq sum := by
      calc
        (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
        _ ≤ 4 * (Canonical.normSq left * Canonical.normSq sum) :=
          Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            dotCauchy (by decide)
        _ ≤ 4 * (majorant * Canonical.normSq sum) :=
          Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (baseUpper z boundary) sumNonnegative) (by decide)
        _ = (4 * majorant) * Canonical.normSq sum := by ring1
    apply (Purelib.Data.Rat.Fraction.Order.Field.div_le_iff_pos
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_pos_direct
        (by decide) majorantPositive)).2
    rw [Fraction.Field.mul_comm (Canonical.normSq sum)]
    exact squaredMargin.trans scaledCauchy

/-- The constructed sum clearance is exactly the squared dominance margin divided by four times the supplied positive
majorant. -/
@[simp] theorem
  boundaryClearance_add_of_dominance_with_majorant_bound
    (base error : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance base error box)
    (majorant : Fraction.Rational) (majorantPositive : 0 < majorant)
    (baseUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary box z →
        Canonical.normSq (base.eval z) ≤ majorant) :
    (boundaryClearance_add_of_dominance_with_majorant base error box
      dominance majorant majorantPositive baseUpper).bound =
        dominance.margin ^ 2 / (4 * majorant) := rfl
end Purelib.Polynomial.Clearance.Box.Dominance.Majorant

end
