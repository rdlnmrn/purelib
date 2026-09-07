import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.L1
import FiniteMeasure.Moments

/-!
# Uniform stability of finite rational variance

Uniformly close rational observables taking values in `[0, 1]` have close
exact finite variances.  The proof compares their second moments and squared
means directly, using only finite expectations and rational separation.
-/

namespace FiniteMeasure

/-- Subtracting one common rational value preserves rational separation. -/
theorem rationalSeparation_sub_same_right
    (left right shift : Coordinate) :
    rationalSeparation (left - shift) (right - shift) =
      rationalSeparation left right := by
  unfold rationalSeparation
  congr 1 <;> ring1

/-- Subtracting two rational values from one common value preserves their
separation, with the directed differences exchanged. -/
theorem rationalSeparation_same_left_sub
    (anchor left right : Coordinate) :
    rationalSeparation (anchor - left) (anchor - right) =
      rationalSeparation left right := by
  unfold rationalSeparation
  rw [max_comm]
  congr 1 <;> ring1

/-- Squaring two rational values in `[0, 1]` expands their separation by at
most the explicit factor two. -/
theorem rationalSeparation_sq_le_two_mul
    {left right : Coordinate}
    (leftNonnegative : 0 ≤ left) (leftLeOne : left ≤ 1)
    (rightNonnegative : 0 ≤ right) (rightLeOne : right ≤ 1) :
    rationalSeparation (left ^ 2) (right ^ 2) ≤
      2 * rationalSeparation left right := by
  have sumNonnegative : 0 ≤ left + right :=
    add_nonneg leftNonnegative rightNonnegative
  have sumLeTwo : left + right ≤ 2 := by
    calc
      left + right ≤ 1 + 1 :=
        RFAP.ConstructiveFraction.add_le_add_direct leftLeOne rightLeOne
      _ = 2 := by ring1
  have separationNonnegative := rationalSeparation_nonneg left right
  unfold rationalSeparation
  apply max_le
  · calc
      left ^ 2 - right ^ 2 = (left - right) * (left + right) := by ring1
      _ ≤ max (left - right) (right - left) * (left + right) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (le_max_left _ _) sumNonnegative
      _ ≤ max (left - right) (right - left) * 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sumLeTwo separationNonnegative
      _ = 2 * max (left - right) (right - left) := by ring1
  · calc
      right ^ 2 - left ^ 2 = (right - left) * (left + right) := by ring1
      _ ≤ max (left - right) (right - left) * (left + right) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (le_max_right _ _) sumNonnegative
      _ ≤ max (left - right) (right - left) * 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          sumLeTwo separationNonnegative
      _ = 2 * max (left - right) (right - left) := by ring1

namespace Distribution

/-- Uniformly close unit-interval observables have exact rational variances
separated by at most four times their pointwise separation allowance. -/
theorem variance_rationalSeparation_le_of_unitInterval {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (radius : Coordinate)
    (leftRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ left atom.item ∧ left atom.item ≤ 1)
    (rightRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ right atom.item ∧ right atom.item ≤ 1)
    (close : ∀ atom, atom ∈ distribution.atoms →
      rationalSeparation (left atom.item) (right atom.item) ≤ radius) :
    rationalSeparation (distribution.variance left)
        (distribution.variance right) ≤ 4 * radius := by
  have meanClose : rationalSeparation
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
  have squaredMeanClose : rationalSeparation
      (distribution.expectation left ^ 2)
      (distribution.expectation right ^ 2) ≤ 2 * radius :=
    (rationalSeparation_sq_le_two_mul leftMeanNonnegative leftMeanLeOne
      rightMeanNonnegative rightMeanLeOne).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct meanClose
        (by decide))
  have secondMomentClose : rationalSeparation
      (distribution.expectation fun item => left item ^ 2)
      (distribution.expectation fun item => right item ^ 2) ≤
      2 * radius := by
    have pointwise : ∀ atom, atom ∈ distribution.atoms →
        rationalSeparation (left atom.item ^ 2) (right atom.item ^ 2) ≤
          2 * radius := by
      intro atom member
      exact (rationalSeparation_sq_le_two_mul
        (leftRange atom member).1 (leftRange atom member).2
        (rightRange atom member).1 (rightRange atom member).2).trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
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
    rationalSeparation
        (distribution.expectation (fun item => left item ^ 2) -
          distribution.expectation left ^ 2)
        (distribution.expectation (fun item => right item ^ 2) -
          distribution.expectation right ^ 2) ≤
      rationalSeparation
          (distribution.expectation (fun item => left item ^ 2) -
            distribution.expectation left ^ 2)
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation left ^ 2) +
        rationalSeparation
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation left ^ 2)
          (distribution.expectation (fun item => right item ^ 2) -
            distribution.expectation right ^ 2) :=
      rationalSeparation_triangle _ _ _
    _ = rationalSeparation
          (distribution.expectation fun item => left item ^ 2)
          (distribution.expectation fun item => right item ^ 2) +
        rationalSeparation (distribution.expectation left ^ 2)
          (distribution.expectation right ^ 2) := by
      rw [rationalSeparation_sub_same_right,
        rationalSeparation_same_left_sub]
    _ ≤ 2 * radius + 2 * radius :=
      RFAP.ConstructiveFraction.add_le_add_direct secondMomentClose
        squaredMeanClose
    _ = 4 * radius := by ring1

end Distribution

end FiniteMeasure
