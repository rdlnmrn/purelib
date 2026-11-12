module

public import Purelib.Polynomial.Clearance.Pair.Cover.Basic

/-!
# Unresolved leaves of a retained clearance cover

The traversal retains the actual cached leaves in their original left-to-right
order. Only a positive quadrance floor removes a leaf from the unresolved list.
-/

namespace Purelib.Polynomial.Clearance.Pair.Cover

open Purelib.Data.Rat
open Purelib.Polynomial

variable {realPolynomial imagPolynomial : Dense.Rational.Basic.CoordinatePolynomial}
  {source : Leaf.Source realPolynomial imagPolynomial}
  {parameters : Interval.Bounds} {normFloor coordinateFloor : Fraction.Rational}

/-- An original cached leaf whose quadrance proposal is proved insufficient.

The subtype retains that exact leaf and its parameter interval, rather than
copying its numerical fields into an unrelated diagnostic record. -/
public abbrev UnresolvedLeaf (source : Leaf.Source realPolynomial imagPolynomial) :=
  Sigma fun parameters => {leaf : Leaf source parameters // ¬ 0 < leaf.normFloor}

/-- The actual unresolved terminal leaves, with their indexed parameter intervals.

Split-node baselines are not terminal covering leaves. The traversal visits both
retained children and preserves every terminal leaf lacking a positive floor. -/
@[expose] public def unresolved : {parameters : Interval.Bounds} →
    {normFloor coordinateFloor : Fraction.Rational} →
    Cover source parameters normFloor coordinateFloor → List (UnresolvedLeaf source)
  | parameters, _, _, .leaf data =>
      if positive : 0 < data.normFloor then [] else [⟨parameters, ⟨data, positive⟩⟩]
  | _, _, _, .split _ left right => left.unresolved ++ right.unresolved

/-- If no terminal leaf remains unresolved, every leaf has a positive floor. -/
public theorem allPositive_of_unresolved_nil
    (cover : Cover source parameters normFloor coordinateFloor)
    (empty : cover.unresolved = []) : cover.AllPositive := by
  induction cover with
  | leaf data =>
      by_cases positive : 0 < data.normFloor
      · exact positive
      · simp only [unresolved, dif_neg positive] at empty
        cases empty
  | split baseline left right leftPositive rightPositive =>
      have leftEmpty : left.unresolved = [] := by
        cases equation : left.unresolved with
        | nil => rfl
        | cons head tail =>
            change left.unresolved ++ right.unresolved = [] at empty
            rw [equation] at empty
            cases empty
      have rightEmpty : right.unresolved = [] := by
        change left.unresolved ++ right.unresolved = [] at empty
        rw [leftEmpty] at empty
        exact empty
      exact ⟨leftPositive leftEmpty, rightPositive rightEmpty⟩

/-- A nonpositive aggregate floor leaves at least one actual terminal obligation.

This is a statement about the retained finite attempt, not a boundary root claim. -/
public theorem unresolved_ne_nil
    (cover : Cover source parameters normFloor coordinateFloor)
    (blocked : ¬ 0 < normFloor) : cover.unresolved ≠ [] := by
  intro empty
  exact blocked (cover.positive_of_all (cover.allPositive_of_unresolved_nil empty))

end Purelib.Polynomial.Clearance.Pair.Cover
