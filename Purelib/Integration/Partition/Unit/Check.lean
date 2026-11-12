module

public import Purelib.Integration.Partition.Unit.Presentation

namespace Purelib.Integration.Partition.Unit.Presentation.Check

/-- Decide equality of two results for the same original list of cuts.

An adjacent failure retains its prefix, ordered pair and suffix. Those finite
data determine its identity; the location and failure proofs are irrelevant
to equality. Different failures in one list may therefore be distinct. The
comparison does not rerun cut recognition or reconstruct a partition cache. -/
public def compare {cuts : Code} (left right : Check cuts) : Decidable (left = right) :=
  match left, right with
  | .accepted _, .accepted _ => .isTrue (by rfl)
  | .outOfRange i _, .outOfRange j _ =>
      if equal : i = j then .isTrue (by cases equal; rfl)
      else .isFalse (by intro same; cases same; exact equal rfl)
  | .badAdjacent before a b after _ _ _, .badAdjacent before' a' b' after' _ _ _ =>
      if equal : (before, a, b, after) = (before', a', b', after') then
        .isTrue (by cases equal; rfl)
      else .isFalse (by intro same; cases same; exact equal rfl)
  | .accepted _, .outOfRange .. => .isFalse (by intro same; cases same)
  | .accepted _, .badAdjacent .. => .isFalse (by intro same; cases same)
  | .outOfRange .., .accepted _ => .isFalse (by intro same; cases same)
  | .outOfRange .., .badAdjacent .. => .isFalse (by intro same; cases same)
  | .badAdjacent .., .accepted _ => .isFalse (by intro same; cases same)
  | .badAdjacent .., .outOfRange .. => .isFalse (by intro same; cases same)

/-- Two adjacent failures agree exactly when their retained finite data agree. -/
public theorem badAdjacent_eq_iff {cuts : Code}
    {before before' after after' : Code} {a a' b b' : Purelib.Data.Rat.Fraction.Rational}
    {position : cuts = before ++ a :: b :: after} {failed : ¬ a < b}
    {notSorted : ¬ cuts.Pairwise (· < ·)}
    {position' : cuts = before' ++ a' :: b' :: after'} {failed' : ¬ a' < b'}
    {notSorted' : ¬ cuts.Pairwise (· < ·)} :
    Check.badAdjacent before a b after position failed notSorted =
      Check.badAdjacent before' a' b' after' position' failed' notSorted' ↔
    (before, a, b, after) = (before', a', b', after') := by
  constructor
  · intro same
    cases same
    rfl
  · intro same
    cases same
    rfl

end Purelib.Integration.Partition.Unit.Presentation.Check
