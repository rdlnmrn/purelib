module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Cumulative.Grid
public import Purelib.Measure.Distribution.Cumulative.Support
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Compute the maximum cumulative separation on the combined finite payload grid of the two exact laws.

The grid covers both retained supports, so this executable finite maximum bounds separation at every rational threshold.
-/
def kolmogorovDistance (left right : Distribution Fraction.Rational) :
    Fraction.Rational :=
  left.cumulativeGridDistance right (cumulativeSupportGrid left right)

/-- Any finite threshold grid covering both original supports gives an upper bound for their Kolmogorov distance. -/
theorem kolmogorovDistance_le_cumulativeGridDistance_of_support_covered
    (left right : Distribution Fraction.Rational) (thresholds : List Fraction.Rational)
    (leftCovered : ∀ atom, atom ∈ left.atoms → atom.item ∈ thresholds)
    (rightCovered : ∀ atom, atom ∈ right.atoms → atom.item ∈ thresholds) :
    left.kolmogorovDistance right ≤
      left.cumulativeGridDistance right thresholds := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right)
    (left.cumulativeGridDistance right thresholds)
    (left.cumulativeGridDistance_nonnegative right thresholds)
  intro cut member
  exact left.cumulative_separation_le_cumulativeGridDistance_of_support_covered
    right thresholds leftCovered rightCovered cut

/-- The finite Kolmogorov distance is nonnegative. -/
theorem kolmogorovDistance_nonnegative
    (left right : Distribution Fraction.Rational) :
    0 ≤ left.kolmogorovDistance right :=
  left.cumulativeGridDistance_nonnegative right
    (cumulativeSupportGrid left right)

/-- Every distribution has Kolmogorov distance zero from itself. -/
@[simp] theorem kolmogorovDistance_refl
    (distribution : Distribution Fraction.Rational) :
    distribution.kolmogorovDistance distribution = 0 :=
  distribution.cumulativeGridDistance_refl
    (cumulativeSupportGrid distribution distribution)

/-- Every rational threshold's cumulative separation is bounded by Kolmogorov distance. -/
theorem cumulative_separation_leKolmogorovDistance
    (left right : Distribution Fraction.Rational) (cut : Fraction.Rational) :
    Distance.rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.kolmogorovDistance right :=
  left.cumulative_separation_le_cumulativeSupportGridDistance right cut

/-- A nonnegative uniform bound on cumulative separation bounds Kolmogorov distance. -/
theorem kolmogorovDistance_le
    (left right : Distribution Fraction.Rational) (bound : Fraction.Rational)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ cut, Distance.rationalSeparation
      (left.cumulative cut) (right.cumulative cut) ≤ bound) :
    left.kolmogorovDistance right ≤ bound := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right) bound boundNonnegative
  intro cut member
  exact pointwise cut

/-- For a nonnegative bound, Kolmogorov-distance control is equivalent to cumulative-separation control at every
rational threshold. -/
theorem kolmogorovDistance_le_iff
    (left right : Distribution Fraction.Rational) (bound : Fraction.Rational)
    (boundNonnegative : 0 ≤ bound) :
    left.kolmogorovDistance right ≤ bound ↔
      ∀ cut, Distance.rationalSeparation
        (left.cumulative cut) (right.cumulative cut) ≤ bound := by
  constructor
  · intro distanceLe cut
    exact (left.cumulative_separation_leKolmogorovDistance right cut)
      |>.trans distanceLe
  · exact fun pointwise => left.kolmogorovDistance_le right bound
      boundNonnegative pointwise

/-- For positive tolerance, strict Kolmogorov-distance control is equivalent to strict cumulative-separation control at
every threshold. -/
theorem kolmogorovDistance_lt_iff
    (left right : Distribution Fraction.Rational) (tolerance : Fraction.Rational)
    (tolerancePositive : 0 < tolerance) :
    left.kolmogorovDistance right < tolerance ↔
      ∀ cut, Distance.rationalSeparation
        (left.cumulative cut) (right.cumulative cut) < tolerance := by
  constructor
  · intro distanceSmall cut
    exact (left.cumulative_separation_leKolmogorovDistance right cut)
      |>.trans_lt distanceSmall
  · intro pointwise
    apply (left.cumulativeGridDistance_lt_iff right
      (cumulativeSupportGrid left right) tolerance tolerancePositive).2
    intro cut member
    exact pointwise cut

/-- Swapping the two original laws preserves their Kolmogorov distance. -/
theorem kolmogorovDistance_symm
    (left right : Distribution Fraction.Rational) :
    left.kolmogorovDistance right =
      right.kolmogorovDistance left := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply left.cumulativeGridDistance_le right
      (cumulativeSupportGrid left right)
      (right.kolmogorovDistance left)
      (right.kolmogorovDistance_nonnegative left)
    intro cut member
    rw [Distance.rationalSeparation_symm]
    exact right.cumulative_separation_leKolmogorovDistance left cut
  · apply right.cumulativeGridDistance_le left
      (cumulativeSupportGrid right left)
      (left.kolmogorovDistance right)
      (left.kolmogorovDistance_nonnegative right)
    intro cut member
    rw [Distance.rationalSeparation_symm]
    exact left.cumulative_separation_leKolmogorovDistance right cut

/-- Kolmogorov distance satisfies the triangle inequality through a third retained law. -/
theorem kolmogorovDistance_triangle
    (left middle right : Distribution Fraction.Rational) :
    left.kolmogorovDistance right ≤
      left.kolmogorovDistance middle +
        middle.kolmogorovDistance right := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right)
  · exact add_nonneg
      (left.kolmogorovDistance_nonnegative middle)
      (middle.kolmogorovDistance_nonnegative right)
  · intro cut member
    exact (Distance.rationalSeparation_triangle
      (left.cumulative cut) (middle.cumulative cut)
      (right.cumulative cut)).trans
        (add_le_add
          (left.cumulative_separation_leKolmogorovDistance middle cut)
          (middle.cumulative_separation_leKolmogorovDistance right cut))

/-- Kolmogorov distance vanishes exactly when the original cumulative functions agree at every rational cut. -/
theorem kolmogorovDistance_eq_zero_iff
    (left right : Distribution Fraction.Rational) :
    left.kolmogorovDistance right = 0 ↔
      ∀ cut, left.cumulative cut = right.cumulative cut := by
  constructor
  · intro distanceZero cut
    apply (Distance.rationalSeparation_eq_zero_iff _ _).mp
    apply Fraction.Order.Basic.Compatibility.le_antisymm
    · rw [← distanceZero]
      exact left.cumulative_separation_leKolmogorovDistance right cut
    · exact Distance.rationalSeparation_nonneg _ _
  · intro equal
    apply Fraction.Order.Basic.Compatibility.le_antisymm
    · apply left.cumulativeGridDistance_le right
        (cumulativeSupportGrid left right) 0 le_rfl
      intro cut member
      exact ((Distance.rationalSeparation_eq_zero_iff _ _).mpr (equal cut)).le
    · exact left.kolmogorovDistance_nonnegative right
end

end Distribution

end Purelib.Measure

end
