module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L1
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Uniform stability of finite rational variance

Uniformly close rational observables taking values in `[0, 1]` have close
exact finite variances.  The proof compares their second moments and squared
means directly, using only finite expectations and rational separation.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Unit-interval observables within a pointwise radius have variances within four times that radius.

Both range certificates and the separation bound apply to every atom of the same original distribution. -/
theorem variance_rationalSeparation_le_of_unitInterval {α : Type}
    (distribution : Measure.Distribution α) (left right : α → Fraction.Rational)
    (radius : Fraction.Rational)
    (leftRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ left atom.item ∧ left atom.item ≤ 1)
    (rightRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ right atom.item ∧ right atom.item ≤ 1)
    (close : ∀ atom, atom ∈ distribution.atoms →
      Distance.rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    Distance.rationalSeparation (distribution.variance left)
        (distribution.variance right) ≤ 4 * radius := by
  have meanClose : Distance.rationalSeparation
      (distribution.expectation left) (distribution.expectation right) ≤
      radius := by
    exact (distribution.expectation_separation_le_l1Distance left right).trans
      (by
        calc
          distribution.l1Distance left right ≤
              distribution.expectation (fun _ => radius) := by
            apply distribution.expectation_mono
            intro atom member
            exact close atom member
          _ = radius := distribution.expectation_constant radius)
  have leftMeanNonnegative : 0 ≤ distribution.expectation left :=
    distribution.expectation_nonneg left fun atom member =>
      (leftRange atom member).1
  have rightMeanNonnegative : 0 ≤ distribution.expectation right :=
    distribution.expectation_nonneg right fun atom member =>
      (rightRange atom member).1
  have leftMeanLeOne : distribution.expectation left ≤ 1 := by
    calc
      distribution.expectation left ≤ distribution.expectation (fun _ => 1) := by
        apply distribution.expectation_mono
        intro atom member
        exact (leftRange atom member).2
      _ = 1 := distribution.expectation_constant 1
  have rightMeanLeOne : distribution.expectation right ≤ 1 := by
    calc
      distribution.expectation right ≤ distribution.expectation (fun _ => 1) := by
        apply distribution.expectation_mono
        intro atom member
        exact (rightRange atom member).2
      _ = 1 := distribution.expectation_constant 1
  have squaredMeanClose : Distance.rationalSeparation
      (distribution.expectation left ^ 2)
      (distribution.expectation right ^ 2) ≤ 2 * radius :=
    (Distance.rationalSeparation_sq_le_two_mul leftMeanNonnegative leftMeanLeOne
      rightMeanNonnegative rightMeanLeOne).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct meanClose
        (by decide))
  have secondMomentClose : Distance.rationalSeparation
      (distribution.expectation fun item => left item ^ 2)
      (distribution.expectation fun item => right item ^ 2) ≤
      2 * radius := by
    have pointwise : ∀ atom, atom ∈ distribution.atoms →
        Distance.rationalSeparation (left atom.item ^ 2) (right atom.item ^ 2) ≤
          2 * radius := by
      intro atom member
      exact (Distance.rationalSeparation_sq_le_two_mul
        (leftRange atom member).1 (leftRange atom member).2
        (rightRange atom member).1 (rightRange atom member).2).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (close atom member) (by decide))
    exact (distribution.expectation_separation_le_l1Distance
      (fun item => left item ^ 2) (fun item => right item ^ 2)).trans (by
        calc
          distribution.l1Distance
                (fun item => left item ^ 2)
                (fun item => right item ^ 2) ≤
              distribution.expectation (fun _ => 2 * radius) := by
            apply distribution.expectation_mono
            intro atom member
            exact pointwise atom member
          _ = 2 * radius := distribution.expectation_constant _)
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.variance_eq_secondMoment_sub_sq]
  calc
    Distance.rationalSeparation
        (distribution.expectation (fun item => left item ^ 2) -
          distribution.expectation left ^ 2)
        (distribution.expectation (fun item => right item ^ 2) -
          distribution.expectation right ^ 2) ≤
      Distance.rationalSeparation
          (distribution.expectation (fun item => left item ^ 2) -
            distribution.expectation left ^ 2)
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation left ^ 2) +
        Distance.rationalSeparation
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation left ^ 2)
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation right ^ 2) :=
      Distance.rationalSeparation_triangle _ _ _
    _ = Distance.rationalSeparation
          (distribution.expectation fun item => left item ^ 2)
          (distribution.expectation fun item => right item ^ 2) +
        Distance.rationalSeparation (distribution.expectation left ^ 2)
          (distribution.expectation right ^ 2) := by
      rw [Distance.rationalSeparation_sub_same_right,
        Distance.rationalSeparation_same_left_sub]
    _ ≤ 2 * radius + 2 * radius :=
      Fraction.Order.Arithmetic.add_le_add_direct secondMomentClose
        squaredMeanClose
    _ = 4 * radius := by ring1

end Distribution

end Purelib.Measure

end
