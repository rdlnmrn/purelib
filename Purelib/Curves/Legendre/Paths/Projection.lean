module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# One projection chart for retained Legendre parameters

The two slopes that collide a parameter reading with zero or one have
explicit rational absolute values. A finite sum of these costs computes a
single strictly larger positive slope, including real parameters, repeated
vertices and an empty finite family.
-/

public section

namespace Purelib.Curves.Legendre.Paths.Projection

open Purelib.Algebra
open Purelib.Data.Rat
open Fraction.Order

/-- The absolute costs of the two slopes that can identify a parameter reading with zero or one.

Total rational division assigns zero to a zero imaginary denominator. Such
real parameters need no forbidden slope: intrinsic regularity distinguishes
their real reading from the two fixed branch readings in every chart. -/
@[expose] def slopeCost (lambda : Gaussian) : Coordinate :=
  Fraction.abs ((0 - lambda.re) / lambda.im) + Fraction.abs ((1 - lambda.re) / lambda.im)

/-- Both retained absolute slope costs have nonnegative total. -/
theorem slopeCost_nonnegative (lambda : Gaussian) : 0 ≤ slopeCost lambda := by
  calc
    0 = (0 : Coordinate) + 0 := by ring1
    _ ≤ slopeCost lambda := Arithmetic.add_le_add_direct
      (Arithmetic.abs_nonneg_direct _) (Arithmetic.abs_nonneg_direct _)

/-- Compute one positive rational projection slope for an original finite parameter family.

The original finite indices select the original Gaussian parameters. Their
two exact forbidden-slope costs are summed once, and the additional unit
makes this same slope strictly exceed each cost. -/
@[expose] def forParameters {count : Nat} (parameters : Fin count → Gaussian) : Coordinate :=
  1 + FiniteSum.Fin.sumFin (fun index => slopeCost (parameters index))

/-- The computed common slope is at least one, including an empty parameter family. -/
theorem forParameters_atLeastOne {count : Nat} (parameters : Fin count → Gaussian) :
    1 ≤ forParameters parameters := by
  have totalNonnegative := FiniteSum.Rational.Order.weight_sum_nonnegative
    (fun index => slopeCost (parameters index)) (fun index => slopeCost_nonnegative (parameters index))
  calc
    1 = (1 : Coordinate) + 0 := by ring1
    _ ≤ forParameters parameters := Arithmetic.add_le_add_direct le_rfl totalNonnegative

/-- The computed common slope strictly exceeds each original parameter's forbidden-slope cost. -/
theorem slopeCost_lt_forParameters {count : Nat} (parameters : Fin count → Gaussian) (index : Fin count) :
    slopeCost (parameters index) < forParameters parameters := by
  have bounded := FiniteSum.Rational.Order.weight_le_sum
    (fun other => slopeCost (parameters other))
    (fun other => slopeCost_nonnegative (parameters other)) index
  have unitPositive : (0 : Coordinate) < 1 := by decide
  calc
    slopeCost (parameters index) ≤ FiniteSum.Fin.sumFin (fun other => slopeCost (parameters other)) := bounded
    _ = 0 + FiniteSum.Fin.sumFin (fun other => slopeCost (parameters other)) := by ring1
    _ < forParameters parameters := Arithmetic.add_lt_add_right_direct unitPositive _

/-- Each of the two original forbidden slopes is bounded by the same retained cost. -/
private theorem forbiddenSlope_le_cost (lambda : Gaussian) :
    (0 - lambda.re) / lambda.im ≤ slopeCost lambda ∧
      (1 - lambda.re) / lambda.im ≤ slopeCost lambda := by
  constructor
  · calc
      (0 - lambda.re) / lambda.im ≤ Fraction.abs ((0 - lambda.re) / lambda.im) := Basic.le_max_left _ _
      _ = Fraction.abs ((0 - lambda.re) / lambda.im) + 0 := by ring1
      _ ≤ slopeCost lambda := Arithmetic.add_le_add_direct le_rfl (Arithmetic.abs_nonneg_direct _)
  · calc
      (1 - lambda.re) / lambda.im ≤ Fraction.abs ((1 - lambda.re) / lambda.im) := Basic.le_max_left _ _
      _ = 0 + Fraction.abs ((1 - lambda.re) / lambda.im) := by ring1
      _ ≤ slopeCost lambda := Arithmetic.add_le_add_direct (Arithmetic.abs_nonneg_direct _) le_rfl

/-- A chart above the two original forbidden-slope costs places every positive-imaginary parameter above one.

The original one-reading ratio lies strictly below the displayed slope.
Multiplication by the same positive imaginary coordinate and translation by
the original real coordinate retain the strict projected reading inequality.
-/
theorem reading_above_one (lambda : Gaussian) (slope : Coordinate)
    (paid : slopeCost lambda < slope) (positive : 0 < lambda.im) : 1 < lambda.re + slope * lambda.im := by
  have less := (forbiddenSlope_le_cost lambda).2.trans_lt paid
  have multiplied := Arithmetic.mul_lt_mul_of_pos_right_direct less positive
  rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'] at multiplied
  have translated := Arithmetic.add_lt_add_left_direct multiplied lambda.re
  rewrite [show lambda.re + (1 - lambda.re) = (1 : Coordinate) by ring1] at translated
  exact translated

/-- A chart above the two original forbidden-slope costs places every negative-imaginary parameter below zero.

Multiplication by the positive reflected imaginary coordinate preserves the
strict forbidden-ratio bound. Its exact scalar readback and translation
give the negative actual reading without an ordered-field instance shortcut.
-/
theorem reading_below_zero (lambda : Gaussian) (slope : Coordinate)
    (paid : slopeCost lambda < slope) (negative : lambda.im < 0) : lambda.re + slope * lambda.im < 0 := by
  have less := (forbiddenSlope_le_cost lambda).1.trans_lt paid
  have reflected : (0 : Coordinate) < -lambda.im := by
    calc
      0 = -(0 : Coordinate) := by ring1
      _ < -lambda.im := Arithmetic.neg_lt_neg_direct negative
  have multiplied := Arithmetic.mul_lt_mul_of_pos_right_direct less reflected
  have original : ((0 - lambda.re) / lambda.im) * (-lambda.im) = lambda.re := by
    calc
      ((0 - lambda.re) / lambda.im) * (-lambda.im) =
          -(((0 - lambda.re) / lambda.im) * lambda.im) := by ring1
      _ = -(0 - lambda.re) := congrArg (fun value : Coordinate => -value)
        (Fraction.Field.div_mul_cancel_of_ne _ _ negative.ne)
      _ = lambda.re := by ring1
  have translated := Arithmetic.add_lt_add_right_direct multiplied (slope * lambda.im)
  rewrite [original, show slope * (-lambda.im) + slope * lambda.im = (0 : Coordinate) by ring1] at translated
  exact translated

/-- A real parameter keeps its exact original real reading in every rational chart. -/
theorem reading_of_real (lambda : Gaussian) (slope : Coordinate) (real : lambda.im = 0) :
    lambda.re + slope * lambda.im = lambda.re := by
  rewrite [real]
  ring1

/-- Every positive-imaginary retained vertex lies above one in the same internally computed finite-family chart. -/
theorem forParameters_reading_above_one {count : Nat} (parameters : Fin count → Gaussian) (index : Fin count)
    (positive : 0 < (parameters index).im) :
    1 < (parameters index).re + forParameters parameters * (parameters index).im :=
  reading_above_one (parameters index) (forParameters parameters) (slopeCost_lt_forParameters parameters index) positive

/-- Every negative-imaginary retained vertex lies below zero in the same internally computed finite-family chart. -/
theorem forParameters_reading_below_zero {count : Nat} (parameters : Fin count → Gaussian) (index : Fin count)
    (negative : (parameters index).im < 0) :
    (parameters index).re + forParameters parameters * (parameters index).im < 0 :=
  reading_below_zero (parameters index) (forParameters parameters)
    (slopeCost_lt_forParameters parameters index) negative

/-- Two charts above the original forbidden-slope cost preserve both weak comparisons with every unit reading.

Positive and negative imaginary coordinates lie on the same outer side
of the whole unit interval in both charts. Real parameters retain their
same original scalar reading, including equality at either endpoint.
-/
theorem reading_comparisons_of_slopeCost (lambda : Gaussian) (first last reading : Coordinate)
    (firstPaid : slopeCost lambda < first) (lastPaid : slopeCost lambda < last)
    (nonnegative : 0 ≤ reading) (atMostOne : reading ≤ 1) :
    (lambda.re + first * lambda.im ≤ reading ↔ lambda.re + last * lambda.im ≤ reading) ∧
      (reading ≤ lambda.re + first * lambda.im ↔ reading ≤ lambda.re + last * lambda.im) := by
  rcases lt_trichotomy lambda.im 0 with negative | real | positive
  · have firstBelow := reading_below_zero lambda first firstPaid negative
    have lastBelow := reading_below_zero lambda last lastPaid negative
    exact ⟨⟨fun _ => lastBelow.le.trans nonnegative, fun _ => firstBelow.le.trans nonnegative⟩,
      ⟨fun above => (lt_irrefl reading ((above.trans_lt firstBelow).trans_le nonnegative)).elim,
        fun above => (lt_irrefl reading ((above.trans_lt lastBelow).trans_le nonnegative)).elim⟩⟩
  · rewrite [reading_of_real lambda first real, reading_of_real lambda last real]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · have firstAbove := reading_above_one lambda first firstPaid positive
    have lastAbove := reading_above_one lambda last lastPaid positive
    exact ⟨⟨fun below => (lt_irrefl reading ((atMostOne.trans_lt firstAbove).trans_le below)).elim,
        fun below => (lt_irrefl reading ((atMostOne.trans_lt lastAbove).trans_le below)).elim⟩,
      ⟨fun _ => atMostOne.trans lastAbove.le, fun _ => atMostOne.trans firstAbove.le⟩⟩

/-- Every regular parameter has distinct fixed readings in any chart above its original forbidden-slope cost.

Nonreal parameters lie strictly outside the whole unit reading interval.
A real parameter retains its original scalar coordinate, and intrinsic
zero/one exclusion rules out both fixed readings directly.
-/
theorem separates_of_slopeCost (lambda : Gaussian) (slope : Coordinate) (paid : slopeCost lambda < slope)
    (nonzero : lambda ≠ 0) (notOne : lambda ≠ 1) :
    lambda.re + slope * lambda.im ≠ 0 ∧ lambda.re + slope * lambda.im ≠ 1 := by
  rcases lt_trichotomy lambda.im 0 with negative | real | positive
  · have below := reading_below_zero lambda slope paid negative
    exact ⟨below.ne, (below.trans (by decide : (0 : Coordinate) < 1)).ne⟩
  · rewrite [reading_of_real lambda slope real]
    exact ⟨fun equal => nonzero (Purelib.Data.Gaussian.Basic.ext equal real),
      fun equal => notOne (Purelib.Data.Gaussian.Basic.ext equal real)⟩
  · have above := reading_above_one lambda slope paid positive
    exact ⟨((by decide : (0 : Coordinate) < 1).trans above).ne', above.ne'⟩

/-- A collision with a fixed real reading identifies the actual slope with its exact forbidden ratio. -/
private theorem slope_eq_forbidden (lambda : Gaussian) (slope target : Coordinate)
    (imaginaryNonzero : lambda.im ≠ 0) (collision : lambda.re + slope * lambda.im = target) :
    slope = (target - lambda.re) / lambda.im := by
  apply Fraction.Field.mul_right_cancel_of_ne imaginaryNonzero
  calc
    slope * lambda.im = (lambda.re + slope * lambda.im) - lambda.re := by ring1
    _ = target - lambda.re := congrArg (fun reading : Coordinate => reading - lambda.re) collision
    _ = ((target - lambda.re) / lambda.im) * lambda.im :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ imaginaryNonzero).symm

/-- Every regular parameter retains distinct zero, parameter and one readings in the computed common chart.

Real parameters use the two intrinsic singular-value exclusions. For a
nonzero imaginary coordinate, a projected collision would identify the
computed slope with a forbidden ratio strictly below that same slope. -/
theorem forParameters_separates {count : Nat} (parameters : Fin count → Gaussian)
    (index : Fin count) (nonzero : parameters index ≠ 0) (notOne : parameters index ≠ 1) :
    (parameters index).re + forParameters parameters * (parameters index).im ≠ 0 ∧
      (parameters index).re + forParameters parameters * (parameters index).im ≠ 1 := by
  let lambda := parameters index
  by_cases imaginaryZero : lambda.im = 0
  · have realNonzero : lambda.re ≠ 0 := fun equal => nonzero (Purelib.Data.Gaussian.Basic.ext equal imaginaryZero)
    have realNotOne : lambda.re ≠ 1 := fun equal => notOne (Purelib.Data.Gaussian.Basic.ext equal imaginaryZero)
    change lambda.re + forParameters parameters * lambda.im ≠ 0 ∧
      lambda.re + forParameters parameters * lambda.im ≠ 1
    rewrite [imaginaryZero, Fraction.Field.mul_zero_direct,
      show lambda.re + 0 = lambda.re by ring1]
    exact ⟨realNonzero, realNotOne⟩
  · have paid := slopeCost_lt_forParameters parameters index
    have bounded := forbiddenSlope_le_cost lambda
    constructor
    · intro collision
      have slopeEquation := slope_eq_forbidden lambda (forParameters parameters) 0 imaginaryZero collision
      have less := bounded.1.trans_lt paid
      rewrite [← slopeEquation] at less
      exact lt_irrefl _ less
    · intro collision
      have slopeEquation := slope_eq_forbidden lambda (forParameters parameters) 1 imaginaryZero collision
      have less := bounded.2.trans_lt paid
      rewrite [← slopeEquation] at less
      exact lt_irrefl _ less

end Purelib.Curves.Legendre.Paths.Projection
