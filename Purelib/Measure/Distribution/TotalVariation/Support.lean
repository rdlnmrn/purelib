module
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Histogram
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction

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

open Purelib.Data.Rat in
/-- Count the exact consolidated key list from the two original rational distributions' content comparison. -/
def comparisonSupportCardinality
    (left right : Distribution Fraction.Rational) : Nat :=
  (left.toContent.radonNikodymKeys right.toContent).length

open Purelib.Data.Rat in
open Purelib.Data.List in
/-- The retained comparison-key count is at most the sum of the two original atom-list lengths. -/
theorem comparisonSupportCardinality_le
    (left right : Distribution Fraction.Rational) :
    left.comparisonSupportCardinality right ≤
      left.atoms.length + right.atoms.length := by
  unfold comparisonSupportCardinality Content.radonNikodymKeys
    Distribution.toContent
  have bound := consolidateAtoms_length_le (left.atoms ++ right.atoms)
  rewrite [Append.length_append] at bound
  exact bound

open Purelib.Data.Rat in
/-- The exact comparison-key list of two normalized rational laws is nonempty. -/
theorem comparisonSupportCardinality_pos
    (left right : Distribution Fraction.Rational) :
    0 < left.comparisonSupportCardinality right := by
  unfold comparisonSupportCardinality Content.radonNikodymKeys
    Distribution.toContent
  apply List.length_pos_iff.mpr
  intro empty
  have consolidatedTotalZero :
      totalWeight (consolidateAtoms (left.atoms ++ right.atoms)) = 0 := by
    rw [empty]
    rfl
  have consolidatedTotalTwo :
      totalWeight (consolidateAtoms (left.atoms ++ right.atoms)) = 2 := by
    rw [totalWeight_consolidateAtoms, totalWeight_append,
      left.total_one, right.total_one]
    decide
  have zeroEqualsTwo : (0 : Fraction.Rational) = 2 :=
    consolidatedTotalZero.symm.trans consolidatedTotalTwo
  exact (by decide : (0 : Fraction.Rational) ≠ 2) zeroEqualsTwo
end Distribution

end Purelib.Measure

end
