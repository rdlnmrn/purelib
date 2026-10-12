module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.RootIsolation.Power.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.Ring

/-!
# Unit-parameter power-polynomial radii

The retained derivative-separation, Taylor and Lipschitz bounds supply the
exact uniqueness, Newton and source-refinement scales for a unit parameter.
Their minimum formulas keep the original polynomial and degree witnesses.
-/

namespace Purelib.RootIsolation.Power.Unit.Radius
public section
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Polynomial

/-- Uniform squared-diameter scale below which two separated winding-one
tracks for a unit-parameter power polynomial cannot share a common box.

The original large-square box and unit-parameter derivative separation supply this scale for the retained positive
degree. Neither its polynomial nor its separation witness is rebuilt by a transport. -/
@[expose]
def unitUniquenessDiagonalThreshold
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
  Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold ambient
    (Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo
      ambient)

open Purelib.RootIsolation in
/-- Fixed Newton-square radius for one unit parameter.  The four terms bound
the absolute radius, the Taylor remainder, two-track uniqueness, and the
Lipschitz variation later used by the finite lift polygon.

The exact minimum retains the Taylor, derivative-separation and Lipschitz scales for the same polynomial and
large-square box. Each bound subsequently selects a component of this unchanged formula. -/
@[expose]
def unitRobustRadius
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let taylor := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let uniqueness :=
    Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  min
    (min
      (min (1 / 8 : Fraction.Rational) ((1 / 8 : Fraction.Rational) / (72 * taylor)))
      (uniqueness / 64))
    (((1 / 8 : Fraction.Rational) ^ 3) / lipschitz)

section
open Purelib.RootIsolation
/-- The uniform robust radius for a unit parameter is at most one eighth.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_le_eighth
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo ≤ 1 / 8 :=
  (Fraction.Order.Basic.min_le_left _ _).trans ((Fraction.Order.Basic.min_le_left _ _).trans
    (Fraction.Order.Basic.min_le_left _ _))

/-- The lift constraint in the robust radius bounds one full coefficientwise
Lipschitz variation budget.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_mul_lipschitz_le
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
    let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
    Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo *
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient ≤
      (1 / 8 : Fraction.Rational) ^ 3 := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  apply (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp
  exact Fraction.Order.Basic.min_le_right _ _

end

open Purelib.RootIsolation in
/-- Refinement request used before the fixed-radius Newton step.  Its four
terms respectively keep squaring harmless, enter the derivative threshold,
bound the Newton displacement by `(r/4)^2`, and place the source box itself
within the same quarter-radius scale.

The exact minimum retains the displacement, quarter-radius and Lipschitz scales derived from the same robust radius. Its
witnesses keep the original unit parameter and degree restriction. -/
@[expose]
def unitRobustSourceRadius
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let quarterRadius := r / 4
  min 1
    (min ((1 / 4 : Fraction.Rational) / lipschitz)
      (min (((1 / 8 : Fraction.Rational) * quarterRadius ^ 2) / lipschitz)
        (quarterRadius ^ 2)))

section
open Purelib.RootIsolation
/-- The source-refinement radius is bounded by the derivative-threshold to Lipschitz ratio.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_derivativeRatio
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
    let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (1 / 4 : Fraction.Rational) /
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The source-refinement radius fits the squared quarter-radius Newton displacement budget.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_displacementRatio
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
    let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
    let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      ((1 / 8 : Fraction.Rational) * (r / 4) ^ 2) /
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient :=
  (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_left _ _))

/-- The source-refinement radius is at most one.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_one
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤ 1 :=
  Fraction.Order.Basic.min_le_left _ _

/-- The source-refinement radius is at most the squared quarter of the robust radius.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_quarterRadius_sq
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (r / 4) ^ 2 :=
  (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_right _ _))

/-- Every exact rational point on the unit parameter circuit uses the same
displayed uniqueness scale. -/
theorem unitUniquenessDiagonalThreshold_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : Data.Gaussian.Norm.Basic.normSq source = 1) (targetUnit : Data.Gaussian.Norm.Basic.normSq
      target = 1)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitUniquenessDiagonalThreshold sourceUnit degree degreeAtLeastTwo =
      Power.Unit.Radius.unitUniquenessDiagonalThreshold targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation
        in by
  unfold Power.Unit.Radius.unitUniquenessDiagonalThreshold
    Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold
  simp only [Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation]
  rw [Power.Bounds.denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree]

/-- Unit parameters of equal squared norm have the same robust Newton radius. -/
theorem unitRobustRadius_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : Data.Gaussian.Norm.Basic.normSq source = 1) (targetUnit : Data.Gaussian.Norm.Basic.normSq
      target = 1)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitRobustRadius sourceUnit degree degreeAtLeastTwo =
      Power.Unit.Radius.unitRobustRadius targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation in by
  unfold Power.Unit.Radius.unitRobustRadius
  dsimp only
  rw [Power.Bounds.denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree,
    Power.Bounds.denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    Power.Unit.Radius.unitUniquenessDiagonalThreshold_eq_of_normSq_eq sourceUnit targetUnit
      equalNorm degree degreeAtLeastTwo]

/-- Unit parameters of equal squared norm have the same source-refinement radius. -/
theorem unitRobustSourceRadius_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical}
    (sourceUnit : Data.Gaussian.Norm.Basic.normSq source = 1) (targetUnit : Data.Gaussian.Norm.Basic.normSq
      target = 1)
    (equalNorm : Data.Gaussian.Norm.Basic.normSq source = Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitRobustSourceRadius sourceUnit degree degreeAtLeastTwo =
      Power.Unit.Radius.unitRobustSourceRadius targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation in by
  unfold Power.Unit.Radius.unitRobustSourceRadius
  dsimp only
  rw [Power.Bounds.denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    Power.Unit.Radius.unitRobustRadius_eq_of_normSq_eq sourceUnit targetUnit equalNorm degree
      degreeAtLeastTwo]

/-- The unit-parameter uniqueness diagonal threshold is strictly positive for degree at least two. -/
theorem unitUniquenessDiagonalThreshold_pos
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo :=
  Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold_pos _
    (Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo _)

/-- The unit-parameter robust Newton radius is strictly positive for degree at least two.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_pos
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let taylor := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let uniqueness :=
    Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have taylorPositive : 0 < taylor :=
    Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient
  have uniquenessPositive : 0 < uniqueness :=
    Power.Unit.Radius.unitUniquenessDiagonalThreshold_pos parameterUnit degree degreeAtLeastTwo
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have oneEighthPositive : (0 : Fraction.Rational) < 1 / 8 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide))
  have seventyTwoPositive : (0 : Fraction.Rational) < 72 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide)
  have sixtyFourPositive : (0 : Fraction.Rational) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)
  have oneEighthCubedPositive : (0 : Fraction.Rational) < (1 / 8) ^ 3 :=
    Fraction.Order.Arithmetic.pow_pos_direct oneEighthPositive 3
  unfold Power.Unit.Radius.unitRobustRadius
  exact Fraction.Order.Basic.lt_min
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Basic.lt_min oneEighthPositive
        (Fraction.Order.Field.div_pos_direct oneEighthPositive
          (Fraction.Order.Arithmetic.mul_pos_direct seventyTwoPositive
            taylorPositive)))
      (Fraction.Order.Field.div_pos_direct uniquenessPositive
        sixtyFourPositive))
    (Fraction.Order.Field.div_pos_direct oneEighthCubedPositive
      lipschitzPositive)

/-- The hull of two overlapping radius-`r` robust squares will be below the
explicit track-uniqueness threshold.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem thirtyTwo_mul_unitRobustRadius_sq_lt_uniqueness
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    32 * Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo ^ 2 <
      Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo := by
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let uniqueness :=
    Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ uniqueness / 64 :=
    (Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  have sixtyFourPositive : (0 : Fraction.Rational) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)
  have scaled : r * 64 ≤ uniqueness :=
    (Fraction.Order.Field.le_div_iff_pos sixtyFourPositive).mp radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq (one_mul r)
  calc
    32 * r ^ 2 ≤ 32 * r :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLeRadius
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)).le
    _ < 64 * r := by
      have positiveScaled := Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)) radiusPositive
      calc
        32 * r = 0 + 32 * r := by ring1
        _ < 32 * r + 32 * r :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct positiveScaled _
        _ = 64 * r := by ring1
    _ = r * 64 := by ring1
    _ ≤ uniqueness := scaled

/-- The fixed radius satisfies the separated Newton Taylor dominance.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_taylor
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
    let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
    let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
      r ^ 2) ≤ (1 / 8 : Fraction.Rational) := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let taylor := Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ (1 / 8 : Fraction.Rational) / (72 * taylor) :=
    (Fraction.Order.Basic.min_le_left _ _).trans
      ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_right _ _))
  have denominatorPositive : 0 < (72 : Fraction.Rational) * taylor :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (72 * taylor) ≤ (1 / 8 : Fraction.Rational) :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct radiusLeOne
          radiusPositive.le
      _ = r := by ring1
  calc
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
        r ^ 2) = (72 * taylor) * r ^ 2 := by
      dsimp only [taylor]
      ring1
    _ ≤ (72 * taylor) * r :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareLeRadius denominatorPositive.le
    _ = r * (72 * taylor) := by ring1
    _ ≤ 1 / 8 := ratioScaled

/-- The unit-parameter source-refinement radius is strictly positive for degree at least two.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_pos
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let quarterRadius := r / 4
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have quarterRadiusPositive : 0 < quarterRadius :=
    Fraction.Order.Field.div_pos_direct
      (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
      (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide))
  have quarterPositive : (0 : Fraction.Rational) < 1 / 4 := by decide
  have eighthPositive : (0 : Fraction.Rational) < 1 / 8 := by decide
  unfold Power.Unit.Radius.unitRobustSourceRadius
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Field.div_pos_direct quarterPositive
        lipschitzPositive)
      (Fraction.Order.Basic.lt_min
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Arithmetic.mul_pos_direct eighthPositive
            (Fraction.Order.Arithmetic.pow_pos_direct quarterRadiusPositive 2))
          lipschitzPositive)
        (Fraction.Order.Arithmetic.pow_pos_direct quarterRadiusPositive 2)))

end

end
end Purelib.RootIsolation.Power.Unit.Radius
