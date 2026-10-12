module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.GaussianInt.Floor
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Region.Gaussian.UnitSquare

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Constructive coordinate-floor complex continued fractions

The coordinate-floor return map and its digit cone, stated entirely in the
explicit finite rational and Gaussian representations used by CCL-1.
-/

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Geometry.Region.Gaussian
open Purelib.Algebra
open Purelib.Algebra.Ring

-- Retain the original subtraction parent's negation with its direct zero law.
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Return

/-- Take the coordinatewise fractional part of gamma times a Gaussian reciprocal.

The original gamma quotient is computed once as the input to coordinate floor.
Subtracting its exact embedded integer floor retains the same half-open
fractional coordinates. -/
@[expose] public def step (u : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical := GaussianInt.Floor.fract
  (Gaussian.Basic.Canonical.gamma * u⁻¹)

/-- Every coordinate-floor return lies in the half-open unit square.

The original Gaussian fractional-part bounds apply to the same gamma quotient.
Each coordinate is nonnegative and strictly below one, including when the
original reciprocal is zero. -/
public theorem step_sq (u : Gaussian.Basic.Canonical) : UnitSquare.Sq (step u) := GaussianInt.Floor.fract_sq _

/-- The integer floor plus the return reconstructs the original gamma quotient.

The fractional-part subtraction removes exactly the same embedded integer
floor that is added back. Coordinatewise additive cancellation recovers both
rational coordinates of the original quotient. -/
public theorem floor_add_step (u : Gaussian.Basic.Canonical) :
    GaussianInt.toGaussian (GaussianInt.Floor.floor (Gaussian.Basic.Canonical.gamma * u⁻¹)) + step u =
      Gaussian.Basic.Canonical.gamma * u⁻¹ := by
  apply Gaussian.Basic.ext <;>
    simp only [step, GaussianInt.Floor.fract, Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im] <;>
    ring1

/-- A nonzero unit-square Gaussian has real gamma-quotient coordinate above one.

Its positive squared norm is strictly below the sum of its coordinates: at
least one coordinate is positive, and both are strictly below one. The original
quotient formula then transports this strict bound through its positive norm. -/
private theorem quotient_real_gt_one (u : Gaussian.Basic.Canonical) (nonzero : u ≠ 0)
    (inside : UnitSquare.Sq u) : 1 < (Gaussian.Basic.Canonical.gamma * u⁻¹).re := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have normPositive : 0 < Gaussian.Norm.Basic.normSq u := (by
      simpa only [Norm.Basic.normSq_eq_canonical]
        using Norm.Basic.normSq_pos nonzero)
  have realProductNonnegative :=
    Fraction.Order.Arithmetic.coordinate_product_nonnegative realNonnegative realSmall
  have imagProductNonnegative :=
    Fraction.Order.Arithmetic.coordinate_product_nonnegative imagNonnegative imagSmall
  have productSumPositive :
      0 < u.re * (1 - u.re) + u.im * (1 - u.im) := by
    by_cases realZero : u.re = 0
    · have imagNonzero : u.im ≠ 0 := by
        intro imagZero
        apply nonzero
        apply Gaussian.Basic.ext <;> assumption
      have imagPositive : 0 < u.im :=
        lt_of_le_of_ne imagNonnegative (Ne.symm imagNonzero)
      have imagProductPositive :=
        Fraction.Order.Arithmetic.coordinate_product_positive imagPositive imagSmall
      calc
        (0 : Fraction.Rational) = 0 + 0 := (Fraction.Field.zero_add 0).symm
        _ ≤ u.re * (1 - u.re) + 0 :=
          Fraction.Order.Arithmetic.add_le_add_direct
            realProductNonnegative (Fraction.Order.Basic.le_refl 0)
        _ < u.re * (1 - u.re) + u.im * (1 - u.im) :=
          Fraction.Order.Arithmetic.add_lt_add_left_direct imagProductPositive _
    · have realPositive : 0 < u.re :=
        lt_of_le_of_ne realNonnegative (Ne.symm realZero)
      have realProductPositive :=
        Fraction.Order.Arithmetic.coordinate_product_positive realPositive realSmall
      calc
        (0 : Fraction.Rational) = 0 + 0 := (Fraction.Field.zero_add 0).symm
        _ < u.re * (1 - u.re) + 0 :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct realProductPositive 0
        _ ≤ u.re * (1 - u.re) + u.im * (1 - u.im) :=
          Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl _) imagProductNonnegative
  have normLess : Gaussian.Norm.Basic.normSq u < u.re + u.im := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      (u.re + u.im) - Gaussian.Norm.Basic.normSq u =
          u.re * (1 - u.re) + u.im * (1 - u.im) := by
        simp only [Gaussian.Norm.Basic.normSq]
        ring1
      _ > 0 := productSumPositive
  rw [(Constants.quotient_coordinates u).1]
  apply (Fraction.Order.Field.lt_div_iff_pos normPositive).2
  calc
    (1 : Fraction.Rational) * Gaussian.Norm.Basic.normSq u = Gaussian.Norm.Basic.normSq u :=
      Fraction.Field.one_mul _
    _ < u.re + u.im := normLess

/-- A unit-square gamma quotient has imaginary coordinate between its signed real endpoints.

Both original coordinates are nonnegative. The exact quotient formulas share
the same positive squared norm for nonzero inputs; their signed numerators
give both weak bounds. The zero input retains its direct zero quotient. -/
private theorem quotient_abs_im_le_real (u : Gaussian.Basic.Canonical)
    (inside : UnitSquare.Sq u) :
    -(Gaussian.Basic.Canonical.gamma * u⁻¹).re ≤ (Gaussian.Basic.Canonical.gamma * u⁻¹).im ∧
      (Gaussian.Basic.Canonical.gamma * u⁻¹).im ≤ (Gaussian.Basic.Canonical.gamma * u⁻¹).re := by
  rcases inside with ⟨realNonnegative, _, imagNonnegative, _⟩
  rcases Constants.quotient_coordinates u with ⟨realFormula, imagFormula⟩
  have normNonnegative := Norm.Basic.normSq_nonneg u
  by_cases zero : u = 0
  · subst u
    decide
  · have normPositive := Norm.Basic.normSq_pos zero
    rw [realFormula, imagFormula]
    constructor
    · have negSum : -(u.re + u.im) = -u.re - u.im := by
        calc
          -(u.re + u.im) = -u.im + -u.re := neg_add_rev _ _
          _ = -u.re + -u.im := _root_.add_comm _ _
          _ = -u.re - u.im := (_root_.sub_eq_add_neg _ _).symm
      rw [show -((u.re + u.im) / Gaussian.Norm.Basic.normSq u) =
          (-u.re - u.im) / Gaussian.Norm.Basic.normSq u by
          simp only [Purelib.Algebra.Field.ExplicitField.div_eq_mul_inv]
          calc
            -((u.re + u.im) * (Gaussian.Norm.Basic.normSq u)⁻¹) =
                (-(u.re + u.im)) * (Gaussian.Norm.Basic.normSq u)⁻¹ :=
              (_root_.neg_mul _ _).symm
            _ = (-u.re - u.im) * (Gaussian.Norm.Basic.normSq u)⁻¹ :=
              congrArg (fun value => value * (Gaussian.Norm.Basic.normSq u)⁻¹) negSum]
      apply (Fraction.Order.Field.div_le_iff_pos normPositive).2
      calc
        -u.re - u.im ≤ u.re - u.im :=
          Fraction.Order.Arithmetic.add_le_add_right_direct
            (Fraction.Order.Arithmetic.neg_le_self_of_nonnegative realNonnegative) (-u.im)
        _ = ((u.re - u.im) / Gaussian.Norm.Basic.normSq u) * Gaussian.Norm.Basic.normSq u :=
          (Fraction.Field.div_mul_cancel_of_ne _ _
            normPositive.ne').symm
    · apply (Fraction.Order.Field.div_le_iff_pos normPositive).2
      calc
        u.re - u.im = -u.im + u.re := by ring1
        _ ≤ u.im + u.re :=
          Fraction.Order.Arithmetic.add_le_add_right_direct
            (Fraction.Order.Arithmetic.neg_le_self_of_nonnegative imagNonnegative) u.re
        _ = u.re + u.im := by ring1
        _ = ((u.re + u.im) / Gaussian.Norm.Basic.normSq u) * Gaussian.Norm.Basic.normSq u :=
          (Fraction.Field.div_mul_cancel_of_ne _ _
            normPositive.ne').symm

/-- The coordinate floor of a nonzero unit-square gamma quotient lies in the retained integer cone.

Its real coordinate is at least one; its imaginary coordinate lies between minus the real coordinate minus one and the
real coordinate. The asymmetric lower endpoint preserves the exact floor convention. -/
public theorem digit_cone (u : Gaussian.Basic.Canonical) (nonzero : u ≠ 0) (inside : UnitSquare.Sq u) :
    let t := GaussianInt.Floor.floor (Gaussian.Basic.Canonical.gamma * u⁻¹)
    1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re := by
  let z := Gaussian.Basic.Canonical.gamma * u⁻¹
  let t := GaussianInt.Floor.floor z
  change 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re
  have realGreater : 1 < z.re := quotient_real_gt_one u nonzero inside
  have absoluteBound := quotient_abs_im_le_real u inside
  have realDigit : (1 : Int) ≤ t.re := by
    apply (Rounding.Floor.intCast_le_iff_floor 1 z.re).1
    exact Fraction.Order.Arithmetic.le_of_lt_direct realGreater
  have imagUpper : t.im ≤ t.re := by
    apply (Rounding.Floor.intCast_le_iff_floor t.im z.re).1
    exact Rat.Fraction.Order.Basic.le_trans _ _ _
      (Rounding.Floor.intCast_floor_le z.im) absoluteBound.2
  have imagFloorUpper := Rounding.Floor.lt_intCast_floor_add_one z.im
  have realFloorUpper := Rounding.Floor.lt_intCast_floor_add_one z.re
  have negatedRealFloorUpper :=
    Fraction.Order.Arithmetic.neg_lt_neg_direct realFloorUpper
  have castCross :
      ((-t.re - 1 : Int) : Fraction.Rational) <
        ((t.im + 1 : Int) : Fraction.Rational) := by
    calc
      ((-t.re - 1 : Int) : Fraction.Rational) =
          -(((t.re + 1 : Int) : Fraction.Rational)) := by
        have castNegative : ((-t.re : Int) : Fraction.Rational) =
            -(t.re : Fraction.Rational) := IntCast.neg t.re
        rewrite [IntCast.sub, castNegative, IntCast.add, Int.cast_one]
        ring1
      _ < -z.re := negatedRealFloorUpper
      _ ≤ z.im := absoluteBound.1
      _ < ((t.im + 1 : Int) : Fraction.Rational) := imagFloorUpper
  have integerCross : -t.re - 1 < t.im + 1 :=
    (Fraction.Cast.Order.intCast_lt_intCast_iff_direct _ _).1 castCross
  exact ⟨realDigit, by omega, imagUpper⟩

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Return
