module

section
@[expose] public section

/-!
# Coupling witnesses between named finite laws

A raw coupling computes its own marginals.  A `LawCoupling` additionally
certifies that those marginals agree in every exact evaluation with two
particular displayed distributions.  Thus transport estimates can be stated
directly about the named finite laws without quotienting atom tables.
-/

namespace Purelib.Measure
namespace LawCoupling

/-- Test equality of two values using the supplied decidable equality.

The result is an executable Boolean obtained directly from the equality decision for
the payload type. -/
def equalityRelation {α : Type} [DecidableEq α] (left right : α) : Bool :=
  decide (left = right)
end LawCoupling

end Purelib.Measure

end
