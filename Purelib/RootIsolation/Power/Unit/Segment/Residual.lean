module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import all Purelib.Data.Rat.Fraction.Order

import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine.Segment

import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Box
public import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Power.Unit.Segment.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Residual

open Purelib.Data.Gaussian

/-- The powered robust-box segment stays within squared residual one eighth of the fixed target parameter under the
retained move budget. -/
theorem unitRobustSegment_constantTarget_residual_le_eighth
    {source target start finish : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    normSq
        ((Affine.line start (finish - start) time) ^ degree.value -
          target) ≤ (1 / 8 : Fraction.Rational) := by
  let liftPoint := Affine.line start (finish - start) time
  have liftResidual : normSq (liftPoint ^ degree.value - source) ≤
      (1 / 32 : Fraction.Rational) :=
    Power.Unit.Segment.Bounds.unitRobustSegment_residual_le (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index startInside finishInside timeInside
  have residualIdentity :
      liftPoint ^ degree.value - target =
        (liftPoint ^ degree.value - source) + (source - target) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
      ring1
  rw [residualIdentity]
  calc
    normSq ((liftPoint ^ degree.value - source) + (source - target)) ≤
      2 * (normSq (liftPoint ^ degree.value - source) +
        normSq (source - target)) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((1 / 32 : Fraction.Rational) + 1 / 128) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add liftResidual small.liftMargin) (by decide)
    _ ≤ 2 * ((1 / 32 : Fraction.Rational) + 1 / 32) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_refl _) Fraction.Order.one_over_one_twenty_eight_le_one_over_thirty_two)
        (by decide)
    _ = 1 / 8 := Fraction.Order.twice_two_thirty_seconds_eq_eighth
end Purelib.RootIsolation.Power.Unit.Segment.Residual

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Residual

open Purelib.Data.Gaussian

/-- The powered robust-box segment stays within squared residual one eighth of the synchronized affine parameter
segment. -/
theorem unitRobustSegment_parameter_residual_le_eighth
    {source target start finish : Gaussian.Basic.Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    {time : Fraction.Rational} (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    normSq
        ((Affine.line start (finish - start) time) ^ degree.value -
          Affine.line source (target - source) time) ≤
      (1 / 8 : Fraction.Rational) := by
  let liftPoint := Affine.line start (finish - start) time
  let parameterPoint := Affine.line source (target - source) time
  have liftResidual : normSq (liftPoint ^ degree.value - source) ≤
      (1 / 32 : Fraction.Rational) :=
    Power.Unit.Segment.Bounds.unitRobustSegment_residual_le (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index startInside finishInside timeInside
  have parameterDistance : normSq (source - parameterPoint) ≤
      (1 / 128 : Fraction.Rational) :=
    (Geometry.Rational.Affine.Segment.normSq_source_sub_line_le source target timeInside).trans small.liftMargin
  have residualIdentity :
      liftPoint ^ degree.value - parameterPoint =
        (liftPoint ^ degree.value - source) + (source - parameterPoint) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
      ring1
  rw [residualIdentity]
  calc
    normSq ((liftPoint ^ degree.value - source) +
        (source - parameterPoint)) ≤
      2 * (normSq (liftPoint ^ degree.value - source) +
        normSq (source - parameterPoint)) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((1 / 32 : Fraction.Rational) + 1 / 128) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add liftResidual parameterDistance) (by decide)
    _ ≤ 2 * ((1 / 32 : Fraction.Rational) + 1 / 32) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_refl _) Fraction.Order.one_over_one_twenty_eight_le_one_over_thirty_two)
        (by decide)
    _ = 1 / 8 := Fraction.Order.twice_two_thirty_seconds_eq_eighth
end Purelib.RootIsolation.Power.Unit.Segment.Residual

end
