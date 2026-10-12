module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
public import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Line.Twist
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Plane.Line.Trigonometry.Conversion

variable {K : Type*} [ExplicitField K]

/-- Theorem 33 (Spread plus cross), Fibonacci's two-square identity with its finite denominator cancelled explicitly. -/
theorem spread_add_cross (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Spread.spread first second firstNonNull secondNonNull +
      Cross.cross first second firstNonNull secondNonNull = 1 := by
  have denominatorNonzero :=
    Purelib.Geometry.Plane.Line.Spread.normProductNonzero first second firstNonNull secondNonNull
  have denominatorCancel :
      (Basic.lineNorm first * Basic.lineNorm second) *
        (Basic.lineNorm first * Basic.lineNorm second)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  unfold Spread.spread Cross.cross
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (first.a * second.b - second.a * first.b) ^ 2 *
          (Basic.lineNorm first * Basic.lineNorm second)⁻¹ +
        (first.a * second.a + first.b * second.b) ^ 2 *
          (Basic.lineNorm first * Basic.lineNorm second)⁻¹ =
      (Basic.lineNorm first * Basic.lineNorm second) *
        (Basic.lineNorm first * Basic.lineNorm second)⁻¹ := by
          unfold Basic.lineNorm
          ring1
    _ = 1 := denominatorCancel

/-- Perpendicular non-null lines have unit spread. -/
theorem spread_eq_one_of_perpendicular
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (perpendicular : first.Perpendicular second) :
    Spread.spread first second firstNonNull secondNonNull = 1 := by
  have crossZero : Cross.cross first second firstNonNull secondNonNull = 0 := by
    unfold Plane.Line.Perpendicular at perpendicular
    unfold Cross.cross
    rw [perpendicular]
    rw [show (0 : K) ^ 2 = 0 by ring1]
    exact ExplicitField.zero_div _
  calc
    Spread.spread first second firstNonNull secondNonNull =
        Spread.spread first second firstNonNull secondNonNull +
          Cross.cross first second firstNonNull secondNonNull := by
      rw [crossZero, add_zero]
    _ = 1 := spread_add_cross first second firstNonNull secondNonNull
end Purelib.Geometry.Plane.Line.Trigonometry.Conversion

end

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Plane.Line.Trigonometry.Conversion

variable {K : Type*} [ExplicitField K]

/-- The Spread-plus-cross theorem solved for the spread. -/
theorem spread_eq_one_sub_cross
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    Spread.spread first second firstNonNull secondNonNull =
      1 - Cross.cross first second firstNonNull secondNonNull := by
  have sum := spread_add_cross first second firstNonNull secondNonNull
  calc
    Spread.spread first second firstNonNull secondNonNull =
        (Spread.spread first second firstNonNull secondNonNull +
          Cross.cross first second firstNonNull secondNonNull) -
          Cross.cross first second firstNonNull secondNonNull := by ring1
    _ = 1 - Cross.cross first second firstNonNull secondNonNull := by rw [sum]
end Purelib.Geometry.Plane.Line.Trigonometry.Conversion

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 6.1--6.2

Exercise 6.1 is proved by cancelling only the displayed non-null and
nonperpendicular denominators.  Exercise 6.2 is a closed constructive-rational
counterexample: two distinct nonperpendicular directions have complementary
spreads with a third line.
-/

namespace Purelib.Geometry.Plane.Line.Trigonometry.Conversion

variable {K : Type*} [ExplicitField K]

/-- The five rational conversion identities between spread, cross and twist.

Both lines are non-null and not perpendicular, so the norm, cross and one-plus-twist denominators are nonzero. -/
theorem exercise_6_1 [Nontrivial K]
    (first second : Plane.Line K)
    (firstNonNull : ¬ first.IsNull)
    (secondNonNull : ¬ second.IsNull)
    (notPerpendicular : ¬ first.Perpendicular second) :
    let s := Spread.spread first second firstNonNull secondNonNull
    let c := Cross.cross first second firstNonNull secondNonNull
    let t := Twist.twist first second notPerpendicular
    t = s / c ∧
      t = s / (1 - s) ∧
      t = (1 - c) / c ∧
      s = t / (1 + t) ∧
      c = 1 / (1 + t) := by
  dsimp only
  let s := Spread.spread first second firstNonNull secondNonNull
  let c := Cross.cross first second firstNonNull secondNonNull
  let t := Twist.twist first second notPerpendicular
  change
    t = s / c ∧
      t = s / (1 - s) ∧
      t = (1 - c) / c ∧
      s = t / (1 + t) ∧
      c = 1 / (1 + t)
  let determinant := first.a * second.b - second.a * first.b
  let dot := first.a * second.a + first.b * second.b
  let normProduct := Line.Basic.lineNorm first * Line.Basic.lineNorm second
  have dotNonzero : dot ≠ 0 := by
    exact notPerpendicular
  have dotSquareNonzero : dot ^ 2 ≠ 0 := by
    simpa [pow_two] using
      ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have normProductNonzero : normProduct ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have crossNonzero : c ≠ 0 := by
    change dot ^ 2 / normProduct ≠ 0
    exact ExplicitField.div_ne_zero dotSquareNonzero
      normProductNonzero
  have spreadCross : s + c = 1 := by
    exact spread_add_cross first second firstNonNull secondNonNull
  have twistSpreadCross : t = s / c := by
    apply Ratio.ratio_eq_of_cross_product dotSquareNonzero crossNonzero
    change determinant ^ 2 * c = s * dot ^ 2
    unfold s Spread.spread c Cross.cross
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have oneMinusSpread : 1 - s = c := by
    calc
      1 - s = (s + c) - s := by rw [spreadCross]
      _ = c := by ring1
  have oneMinusCross : 1 - c = s := by
    calc
      1 - c = (s + c) - c := by rw [spreadCross]
      _ = s := by ring1
  have twistSpreadOneMinusSpread : t = s / (1 - s) := by
    calc
      t = s / c := twistSpreadCross
      _ = s / (1 - s) := by rw [oneMinusSpread]
  have twistOneMinusCrossCross : t = (1 - c) / c := by
    calc
      t = s / c := twistSpreadCross
      _ = (1 - c) / c := by rw [oneMinusCross]
  have crossTimesOnePlusTwist : c * (1 + t) = 1 := by
    rw [twistSpreadCross]
    calc
      c * (1 + s / c) = c + (s / c) * c := by ring1
      _ = c + s := by
        rw [ExplicitField.div_mul_cancel _ crossNonzero]
      _ = 1 := by rw [add_comm, spreadCross]
  have onePlusTwistNonzero : 1 + t ≠ 0 := by
    intro zero
    have oneNonzero : (1 : K) ≠ 0 := one_ne_zero
    apply oneNonzero
    calc
      (1 : K) = c * (1 + t) := crossTimesOnePlusTwist.symm
      _ = 0 := by rw [zero]; ring1
  have spreadTimesOnePlusTwist : s * (1 + t) = t := by
    apply ExplicitField.eq_of_mul_eq_mul_right crossNonzero
    calc
      s * (1 + t) * c = s * (c * (1 + t)) := by ring1
      _ = s := by rw [crossTimesOnePlusTwist, mul_one]
      _ = (s / c) * c :=
        (ExplicitField.div_mul_cancel _ crossNonzero).symm
      _ = t * c := by rw [twistSpreadCross]
  have spreadFromTwist : s = t / (1 + t) := by
    apply ExplicitField.eq_of_mul_eq_mul_right onePlusTwistNonzero
    calc
      s * (1 + t) = t := spreadTimesOnePlusTwist
      _ = (t / (1 + t)) * (1 + t) :=
        (ExplicitField.div_mul_cancel _ onePlusTwistNonzero).symm
  have crossFromTwist : c = 1 / (1 + t) := by
    apply ExplicitField.eq_of_mul_eq_mul_right onePlusTwistNonzero
    calc
      c * (1 + t) = 1 := crossTimesOnePlusTwist
      _ = (1 / (1 + t)) * (1 + t) :=
        (ExplicitField.div_mul_cancel _ onePlusTwistNonzero).symm
  exact ⟨twistSpreadCross, twistSpreadOneMinusSpread,
    twistOneMinusCrossCross, spreadFromTwist, crossFromTwist⟩

end Purelib.Geometry.Plane.Line.Trigonometry.Conversion

end
