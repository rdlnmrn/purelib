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

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Data.Rat.Fraction.Order

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
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let ambient := RootRadius.Box.largeSquareBox
    (Power.Gaussian.rootPolynomial parameter degree)
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
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let taylor := Box.Taylor.denseTaylorRemainderBound p ambient
  let lipschitz := Box.denseLipschitzBound p ambient
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
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
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustRadius parameterUnit degree degreeAtLeastTwo ≤ 1 / 8 :=
  (Basic.min_le_left _ _).trans ((Basic.min_le_left _ _).trans
    (Basic.min_le_left _ _))

/-- The lift constraint in the robust radius bounds one full coefficientwise
Lipschitz variation budget.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_mul_lipschitz_le
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Power.Gaussian.rootPolynomial parameter degree
    let ambient := RootRadius.Box.largeSquareBox p
    unitRobustRadius parameterUnit degree degreeAtLeastTwo *
        Box.denseLipschitzBound p ambient ≤
      (1 / 8 : Fraction.Rational) ^ 3 := by
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let lipschitz := Box.denseLipschitzBound p ambient
  have lipschitzPositive : 0 < lipschitz :=
    Box.denseLipschitzBound_pos p ambient
  apply (Field.le_div_iff_pos lipschitzPositive).mp
  exact Basic.min_le_right _ _

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
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let lipschitz := Box.denseLipschitzBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
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
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Power.Gaussian.rootPolynomial parameter degree
    let ambient := RootRadius.Box.largeSquareBox p
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (1 / 4 : Fraction.Rational) /
        Box.denseLipschitzBound p ambient :=
  (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)

/-- The source-refinement radius fits the squared quarter-radius Newton displacement budget.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_displacementRatio
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Power.Gaussian.rootPolynomial parameter degree
    let ambient := RootRadius.Box.largeSquareBox p
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      ((1 / 8 : Fraction.Rational) * (r / 4) ^ 2) /
        Box.denseLipschitzBound p ambient :=
  (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
    (Basic.min_le_left _ _))

/-- The source-refinement radius is at most one.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_one
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤ 1 :=
  Basic.min_le_left _ _

/-- The source-refinement radius is at most the squared quarter of the robust radius.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_le_quarterRadius_sq
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ≤
      (r / 4) ^ 2 :=
  (Basic.min_le_right _ _).trans ((Basic.min_le_right _ _).trans
    (Basic.min_le_right _ _))

/-- Every exact rational point on the unit parameter circuit uses the same
displayed uniqueness scale. -/
theorem unitUniquenessDiagonalThreshold_eq_of_normSq_eq
    {source target : Basic.Canonical}
    (sourceUnit : Norm.Basic.normSq source = 1) (targetUnit : Norm.Basic.normSq
      target = 1)
    (equalNorm : Norm.Basic.normSq source = Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitUniquenessDiagonalThreshold sourceUnit degree degreeAtLeastTwo =
      unitUniquenessDiagonalThreshold targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation
        in by
  unfold unitUniquenessDiagonalThreshold
    Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold
  simp only [Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation]
  rw [Bounds.denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree]

/-- Unit parameters of equal squared norm have the same robust Newton radius. -/
theorem unitRobustRadius_eq_of_normSq_eq
    {source target : Basic.Canonical}
    (sourceUnit : Norm.Basic.normSq source = 1) (targetUnit : Norm.Basic.normSq
      target = 1)
    (equalNorm : Norm.Basic.normSq source = Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustRadius sourceUnit degree degreeAtLeastTwo =
      unitRobustRadius targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation in by
  unfold unitRobustRadius
  dsimp only
  rw [Bounds.denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree,
    Bounds.denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    unitUniquenessDiagonalThreshold_eq_of_normSq_eq sourceUnit targetUnit
      equalNorm degree degreeAtLeastTwo]

/-- Unit parameters of equal squared norm have the same source-refinement radius. -/
theorem unitRobustSourceRadius_eq_of_normSq_eq
    {source target : Basic.Canonical}
    (sourceUnit : Norm.Basic.normSq source = 1) (targetUnit : Norm.Basic.normSq
      target = 1)
    (equalNorm : Norm.Basic.normSq source = Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustSourceRadius sourceUnit degree degreeAtLeastTwo =
      unitRobustSourceRadius targetUnit degree degreeAtLeastTwo := open Purelib.RootIsolation in by
  unfold unitRobustSourceRadius
  dsimp only
  rw [Bounds.denseLipschitzBound_polynomial_eq_of_normSq_eq equalNorm degree,
    unitRobustRadius_eq_of_normSq_eq sourceUnit targetUnit equalNorm degree
      degreeAtLeastTwo]

/-- The unit-parameter uniqueness diagonal threshold is strictly positive for degree at least two. -/
theorem unitUniquenessDiagonalThreshold_pos
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo :=
  Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold_pos _
    (Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo _)

/-- The unit-parameter robust Newton radius is strictly positive for degree at least two.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_pos
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitRobustRadius parameterUnit degree degreeAtLeastTwo := by
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let taylor := Box.Taylor.denseTaylorRemainderBound p ambient
  let lipschitz := Box.denseLipschitzBound p ambient
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have taylorPositive : 0 < taylor :=
    Box.Taylor.denseTaylorRemainderBound_pos p ambient
  have uniquenessPositive : 0 < uniqueness :=
    unitUniquenessDiagonalThreshold_pos parameterUnit degree degreeAtLeastTwo
  have lipschitzPositive : 0 < lipschitz :=
    Box.denseLipschitzBound_pos p ambient
  have oneEighthPositive : (0 : Fraction.Rational) < 1 / 8 :=
    Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide))
  have seventyTwoPositive : (0 : Fraction.Rational) < 72 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide)
  have sixtyFourPositive : (0 : Fraction.Rational) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)
  have oneEighthCubedPositive : (0 : Fraction.Rational) < (1 / 8) ^ 3 :=
    Arithmetic.pow_pos_direct oneEighthPositive 3
  unfold unitRobustRadius
  exact Basic.lt_min
    (Basic.lt_min
      (Basic.lt_min oneEighthPositive
        (Field.div_pos_direct oneEighthPositive
          (Arithmetic.mul_pos_direct seventyTwoPositive
            taylorPositive)))
      (Field.div_pos_direct uniquenessPositive
        sixtyFourPositive))
    (Field.div_pos_direct oneEighthCubedPositive
      lipschitzPositive)

/-- The hull of two overlapping radius-`r` robust squares will be below the
explicit track-uniqueness threshold.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem thirtyTwo_mul_unitRobustRadius_sq_lt_uniqueness
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    32 * unitRobustRadius parameterUnit degree degreeAtLeastTwo ^ 2 <
      unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo := by
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let uniqueness :=
    unitUniquenessDiagonalThreshold parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ uniqueness / 64 :=
    (Basic.min_le_left _ _).trans (Basic.min_le_right _ _)
  have sixtyFourPositive : (0 : Fraction.Rational) < 64 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)
  have scaled : r * 64 ≤ uniqueness :=
    (Field.le_div_iff_pos sixtyFourPositive).mp radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq (one_mul r)
  calc
    32 * r ^ 2 ≤ 32 * r :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct squareLeRadius
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)).le
    _ < 64 * r := by
      have positiveScaled := Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)) radiusPositive
      calc
        32 * r = 0 + 32 * r := by ring1
        _ < 32 * r + 32 * r :=
          Arithmetic.add_lt_add_right_direct positiveScaled _
        _ = 64 * r := by ring1
    _ = r * 64 := by ring1
    _ ≤ uniqueness := scaled

/-- The fixed radius satisfies the separated Newton Taylor dominance.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustRadius_taylor
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    let p := Power.Gaussian.rootPolynomial parameter degree
    let ambient := RootRadius.Box.largeSquareBox p
    let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
    2 * (36 * Box.Taylor.denseTaylorRemainderBound p ambient *
      r ^ 2) ≤ (1 / 8 : Fraction.Rational) := by
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let taylor := Box.Taylor.denseTaylorRemainderBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo
  have radiusLeOne : r ≤ 1 :=
    (unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo).trans
      (by decide)
  have radiusRatio : r ≤ (1 / 8 : Fraction.Rational) / (72 * taylor) :=
    (Basic.min_le_left _ _).trans
      ((Basic.min_le_left _ _).trans (Basic.min_le_right _ _))
  have denominatorPositive : 0 < (72 : Fraction.Rational) * taylor :=
    Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Box.Taylor.denseTaylorRemainderBound_pos p ambient)
  have ratioScaled : r * (72 * taylor) ≤ (1 / 8 : Fraction.Rational) :=
    (Field.le_div_iff_pos denominatorPositive).mp
      radiusRatio
  have squareLeRadius : r ^ 2 ≤ r := by
    rw [pow_two]
    calc
      r * r ≤ 1 * r :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct radiusLeOne
          radiusPositive.le
      _ = r := by ring1
  calc
    2 * (36 * Box.Taylor.denseTaylorRemainderBound p ambient *
        r ^ 2) = (72 * taylor) * r ^ 2 := by
      dsimp only [taylor]
      ring1
    _ ≤ (72 * taylor) * r :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareLeRadius denominatorPositive.le
    _ = r * (72 * taylor) := by ring1
    _ ≤ 1 / 8 := ratioScaled

/-- The unit-parameter source-refinement radius is strictly positive for degree at least two.

The displayed minimum retains its original association and scalar components. The bound reads the indicated component
for the same unit parameter and degree witness. -/
theorem unitRobustSourceRadius_pos
    {parameter : Basic.Canonical} (parameterUnit : Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo := by
  let p := Power.Gaussian.rootPolynomial parameter degree
  let ambient := RootRadius.Box.largeSquareBox p
  let lipschitz := Box.denseLipschitzBound p ambient
  let r := unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let quarterRadius := r / 4
  have lipschitzPositive : 0 < lipschitz :=
    Box.denseLipschitzBound_pos p ambient
  have quarterRadiusPositive : 0 < quarterRadius :=
    Field.div_pos_direct
      (unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
      (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by decide))
  have quarterPositive : (0 : Fraction.Rational) < 1 / 4 := by decide
  have eighthPositive : (0 : Fraction.Rational) < 1 / 8 := by decide
  unfold unitRobustSourceRadius
  exact Basic.lt_min (by decide)
    (Basic.lt_min
      (Field.div_pos_direct quarterPositive
        lipschitzPositive)
      (Basic.lt_min
        (Field.div_pos_direct
          (Arithmetic.mul_pos_direct eighthPositive
            (Arithmetic.pow_pos_direct quarterRadiusPositive 2))
          lipschitzPositive)
        (Arithmetic.pow_pos_direct quarterRadiusPositive 2)))

end

end
end Purelib.RootIsolation.Power.Unit.Radius
