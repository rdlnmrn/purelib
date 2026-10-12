module
import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Bool.Relation
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

namespace LawCoupling

/-- Any retained coupling of the exact two laws bounds their total variation by its equality-mismatch probability. -/
theorem totalVariationDistance_le_mismatchProbability
    {α : Type} [DecidableEq α]
    {left right : Distribution α} (witness : LawCoupling left right) :
    left.totalVariationDistance right ≤
      witness.mismatchProbability equalityRelation := by
  let event := left.totalVariationEvent right
  have agree : witness.coupling.EventsAgreeOn equalityRelation event event := by
    intro atom member related
    have same : atom.item.1 = atom.item.2 := by
      unfold equalityRelation at related
      exact of_decide_eq_true related
    rw [same]
  have close := witness.probability_close_of_eventsAgree
    equalityRelation event event agree
  calc
    left.totalVariationDistance right =
        left.probability event - right.probability event :=
      (left.probability_sub_at_totalVariationEvent right).symm
    _ ≤ witness.mismatchProbability equalityRelation := close.2

end LawCoupling

end Purelib.Measure

end
