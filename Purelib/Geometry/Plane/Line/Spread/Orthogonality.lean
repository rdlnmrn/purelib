module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Cross
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Orthogonality

variable {K : Type*} [ExplicitField K]

/-- The spreads made by a third line with two perpendicular lines sum to one.

All three lines are non-null, certifying the norm denominators. -/
theorem complementary_spreads [DecidableEq K]
    (first second third : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull)
    (perpendicular : first.Perpendicular second) :
    Spread.spread second third secondNonNull thirdNonNull +
      Spread.spread first third firstNonNull thirdNonNull = 1 := by
  have firstNormNonzero : Basic.lineNorm first ≠ 0 := firstNonNull
  have secondNormNonzero : Basic.lineNorm second ≠ 0 := secondNonNull
  have thirdNormNonzero : Basic.lineNorm third ≠ 0 := thirdNonNull
  have firstThirdDenominatorNonzero :
      Basic.lineNorm first * Basic.lineNorm third ≠ 0 :=
    ExplicitField.mul_ne_zero firstNormNonzero thirdNormNonzero
  have secondThirdDenominatorNonzero :
      Basic.lineNorm second * Basic.lineNorm third ≠ 0 :=
    ExplicitField.mul_ne_zero secondNormNonzero thirdNormNonzero
  let uvDet := first.a * second.b - second.a * first.b
  let uwDot := first.a * third.a + first.b * third.b
  let vwDet := second.a * third.b - third.a * second.b
  have perpendicularZero : first.a * second.a + first.b * second.b = 0 :=
    perpendicular
  have determinantSquare : uvDet ^ 2 = Basic.lineNorm first * Basic.lineNorm second := by
    unfold uvDet Basic.lineNorm
    calc
      (first.a * second.b - second.a * first.b) ^ 2 =
          (first.a ^ 2 + first.b ^ 2) *
            (second.a ^ 2 + second.b ^ 2) -
          (first.a * second.a + first.b * second.b) ^ 2 := by ring1
      _ = (first.a ^ 2 + first.b ^ 2) *
          (second.a ^ 2 + second.b ^ 2) := by rw [perpendicularZero]; ring1
  have linearIdentity : Basic.lineNorm first * vwDet = -(uvDet * uwDot) := by
    unfold Basic.lineNorm vwDet uvDet uwDot
    calc
      (first.a ^ 2 + first.b ^ 2) *
          (second.a * third.b - third.a * second.b) =
        (first.a * second.a + first.b * second.b) *
            (first.a * third.b - third.a * first.b) -
          (first.a * second.b - second.a * first.b) *
            (first.a * third.a + first.b * third.b) := by ring1
      _ = -(uvDet * uwDot) := by rw [perpendicularZero]; ring1
  have squaredIdentity : Basic.lineNorm first ^ 2 * vwDet ^ 2 =
      uvDet ^ 2 * uwDot ^ 2 := by
    calc
      Basic.lineNorm first ^ 2 * vwDet ^ 2 =
          (Basic.lineNorm first * vwDet) ^ 2 := by ring1
      _ = (-(uvDet * uwDot)) ^ 2 := by rw [linearIdentity]
      _ = uvDet ^ 2 * uwDot ^ 2 := by ring1
  have cancellationProduct : Basic.lineNorm first *
      (Basic.lineNorm first * vwDet ^ 2 - Basic.lineNorm second * uwDot ^ 2) = 0 := by
    calc
      Basic.lineNorm first *
          (Basic.lineNorm first * vwDet ^ 2 - Basic.lineNorm second * uwDot ^ 2) =
        Basic.lineNorm first ^ 2 * vwDet ^ 2 -
          (Basic.lineNorm first * Basic.lineNorm second) * uwDot ^ 2 := by ring1
      _ = uvDet ^ 2 * uwDot ^ 2 - uvDet ^ 2 * uwDot ^ 2 := by
        rw [squaredIdentity, determinantSquare]
      _ = 0 := by ring1
  have scaledNumerators : Basic.lineNorm first * vwDet ^ 2 =
      Basic.lineNorm second * uwDot ^ 2 := by
    have differenceZero := ExplicitField.eq_zero_of_mul_eq_zero_left
      firstNormNonzero cancellationProduct
    calc
      Basic.lineNorm first * vwDet ^ 2 =
          (Basic.lineNorm first * vwDet ^ 2 - Basic.lineNorm second * uwDot ^ 2) +
            Basic.lineNorm second * uwDot ^ 2 := by ring1
      _ = Basic.lineNorm second * uwDot ^ 2 := by rw [differenceZero]; ring1
  have spreadEqualsCross :
      Spread.spread second third secondNonNull thirdNonNull =
        Cross.cross first third firstNonNull thirdNonNull := by
    apply Ratio.ratio_eq_of_cross_product
      secondThirdDenominatorNonzero firstThirdDenominatorNonzero
    change vwDet ^ 2 * (Basic.lineNorm first * Basic.lineNorm third) =
      uwDot ^ 2 * (Basic.lineNorm second * Basic.lineNorm third)
    calc
      vwDet ^ 2 * (Basic.lineNorm first * Basic.lineNorm third) =
        Basic.lineNorm third * (Basic.lineNorm first * vwDet ^ 2) := by ring1
      _ = Basic.lineNorm third * (Basic.lineNorm second * uwDot ^ 2) := by
        rw [scaledNumerators]
      _ = uwDot ^ 2 * (Basic.lineNorm second * Basic.lineNorm third) := by ring1
  rw [spreadEqualsCross]
  calc
    Cross.cross first third firstNonNull thirdNonNull +
        Spread.spread first third firstNonNull thirdNonNull =
      Spread.spread first third firstNonNull thirdNonNull +
        Cross.cross first third firstNonNull thirdNonNull := by ring1
    _ = 1 := Trigonometry.Conversion.spread_add_cross first third firstNonNull thirdNonNull

/-- Replacing both lines by perpendicular non-null directions preserves their spread.

Both original lines and both replacement lines are non-null. -/
theorem perpendicular_spreads [DecidableEq K]
    (first second firstOther secondOther : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (firstOtherNonNull : ¬ firstOther.IsNull)
    (secondOtherNonNull : ¬ secondOther.IsNull)
    (firstPairPerpendicular : first.Perpendicular second)
    (secondPairPerpendicular : firstOther.Perpendicular secondOther) :
    Spread.spread first firstOther firstNonNull firstOtherNonNull =
      Spread.spread second secondOther secondNonNull secondOtherNonNull := by
  have firstComplement := complementary_spreads
    first second firstOther firstNonNull secondNonNull firstOtherNonNull
    firstPairPerpendicular
  have secondComplement := complementary_spreads
    firstOther secondOther second firstOtherNonNull secondOtherNonNull
    secondNonNull secondPairPerpendicular
  rw [Spread.spread_symm firstOther second firstOtherNonNull secondNonNull,
    Spread.spread_symm secondOther second secondOtherNonNull secondNonNull]
    at secondComplement
  have secondComplementReordered :
      Spread.spread second firstOther secondNonNull firstOtherNonNull +
        Spread.spread second secondOther secondNonNull secondOtherNonNull = 1 := by
    calc
      Spread.spread second firstOther secondNonNull firstOtherNonNull +
          Spread.spread second secondOther secondNonNull secondOtherNonNull =
        Spread.spread second secondOther secondNonNull secondOtherNonNull +
          Spread.spread second firstOther secondNonNull firstOtherNonNull := by ring1
      _ = 1 := secondComplement
  calc
    Spread.spread first firstOther firstNonNull firstOtherNonNull =
        1 - Spread.spread second firstOther secondNonNull firstOtherNonNull := by
          calc
            Spread.spread first firstOther firstNonNull firstOtherNonNull =
              (Spread.spread second firstOther secondNonNull firstOtherNonNull +
                Spread.spread first firstOther firstNonNull firstOtherNonNull) -
                Spread.spread second firstOther secondNonNull firstOtherNonNull := by ring1
            _ = 1 - Spread.spread second firstOther secondNonNull firstOtherNonNull := by
              rw [firstComplement]
    _ = Spread.spread second secondOther secondNonNull secondOtherNonNull := by
      calc
        1 - Spread.spread second firstOther secondNonNull firstOtherNonNull =
          (Spread.spread second firstOther secondNonNull firstOtherNonNull +
            Spread.spread second secondOther secondNonNull secondOtherNonNull) -
            Spread.spread second firstOther secondNonNull firstOtherNonNull := by
              rw [secondComplementReordered]
        _ = Spread.spread second secondOther secondNonNull secondOtherNonNull := by ring1
end Purelib.Geometry.Plane.Line.Spread.Orthogonality

end
