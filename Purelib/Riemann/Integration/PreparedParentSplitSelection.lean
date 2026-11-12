module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

public import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.NatCast
public import Purelib.Data.Vector.Dependent

public section

/-! Positional selection from the retained splitting spine. Repeated parent
occurrences stay distinct; no decidable equality on prepared models is used. -/
namespace Purelib.Riemann.Integration.PreparedParentSplitSelection
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits)
open Purelib.Riemann.Integration.PreparedParentSplitting.ParentSplits (Member)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr)
open Purelib.Algebra
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}

/-- Read a parent at its retained finite list coordinate.

The supplied index bound selects the same original parent occurrence, including
repeated entries in the displayed splitting spine. -/
@[expose] def parentAt (parents : List (CenteredEdge curve differential)) (index : Fin parents.length) : CenteredEdge
  curve differential :=
  parents[index.val]'index.isLt

set_option genInjectivity false in
/-- A segment split with membership in the original parent-splitting family.

The split keeps the exact queried parent's endpoints; its membership witness identifies the original retained family
entry. -/
structure Selected {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents)
    (parent : CenteredEdge curve differential) where
  /-- The retained split of this original parent's exact endpoints. -/ split : SegmentSplit cuts (parent.edge.point 0)
    (parent.edge.point 1)
  /-- Membership of this exact split in the original parent-splitting family. -/ member : Member split splits

constructive_injectivity Selected

/-- Select the parent split at its retained finite list coordinate.

Structural recursion follows the same parent spine and preserves the selected
split, endpoints and membership witness in the original family. -/
@[expose] def select : {parents : List (CenteredEdge curve differential)} → (splits : ParentSplits cuts parents) →
    (index : Fin parents.length) → Selected splits (parentAt parents index)
  | _, .nil, index => Fin.elim0 index
  | _, .cons split tail, ⟨0, _⟩ => ⟨split, .here tail⟩
  | _, .cons split tail, ⟨index + 1, bound⟩ =>
    let selected := select tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩
    ⟨selected.split, .there split selected.member⟩

/-- Materialize the original split spine using one supplied, decreasing parent count. -/
private def indexedOfLength : (size : Nat) → {parents : List (CenteredEdge curve differential)} →
    (equal : size = parents.length) → (splits : ParentSplits cuts parents) →
    DependentVector (fun index : Fin size =>
      SegmentSplit cuts ((parentAt parents ⟨index.val, equal ▸ index.isLt⟩).edge.point 0)
        ((parentAt parents ⟨index.val, equal ▸ index.isLt⟩).edge.point 1))
  | 0, [], _, .nil => .nil
  | 0, _ :: _, equal, _ => nomatch equal
  | _ + 1, [], equal, _ => nomatch equal
  | size + 1, _ :: _, equal, .cons split tail =>
      .cons split (indexedOfLength size (Nat.succ.inj equal) tail)

/-- Reading the materialized spine returns the complete original selected split. -/
private theorem indexedOfLength_get : ∀ (size : Nat) {parents : List (CenteredEdge curve differential)}
    (equal : size = parents.length) (splits : ParentSplits cuts parents) (index : Fin size),
    (indexedOfLength size equal splits).get index =
      (select splits ⟨index.val, equal ▸ index.isLt⟩).split
  | 0, _, _, _, index => Fin.elim0 index
  | _ + 1, [], equal, _, _ => nomatch equal
  | _ + 1, _ :: _, _, .cons _ _, ⟨0, _⟩ => rfl
  | size + 1, _ :: _, equal, .cons _ tail, ⟨index + 1, bound⟩ =>
      indexedOfLength_get size (Nat.succ.inj equal) tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Materialize a positional view of the same retained parent splits.

The original split payloads are copied by reference into one stored vector.
The parent count is read once before structural traversal; neither splitting
nor point, root or mesh preparation is repeated.
-/
def indexed {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents) :
    DependentVector (fun index : Fin parents.length =>
      SegmentSplit cuts ((parentAt parents index).edge.point 0) ((parentAt parents index).edge.point 1)) :=
  indexedOfLength parents.length rfl splits

/-- Each positional entry is the entire split selected from the original parent bank. -/
theorem indexed_get {parents : List (CenteredEdge curve differential)} (splits : ParentSplits cuts parents)
    (index : Fin parents.length) : (indexed splits).get index = (select splits index).split :=
  indexedOfLength_get parents.length rfl splits index

/-- Summing the retained positional piece counts reads the original splitting bank's total count.

Every parent occurrence contributes its exact cached split count once.
The identity holds after natural casting into any commutative ring and
includes the empty splitting bank.
-/
theorem sum_counts {K : Type*} [CommRing K] {parents : List (CenteredEdge curve differential)}
    (splits : ParentSplits cuts parents) :
    sumFin (fun index : Fin parents.length => (((indexed splits).get index).count : K)) =
      (splits.pieceCount : K) := by
  induction splits with
  | nil =>
      change (0 : K) = ((0 : Nat) : K)
      exact (Nat.cast_zero).symm
  | @cons parent remaining split tail ih =>
      rewrite [sumFin_succ]
      calc
        _ = (split.count : K) +
            sumFin (fun index : Fin remaining.length => (((indexed tail).get index).count : K)) := by
          apply congrArg₂ (fun first last : K => first + last)
          · rewrite [indexed_get]
            rfl
          · apply sumFin_congr
            intro index
            rewrite [indexed_get, indexed_get]
            rfl
        _ = _ := by
          rewrite [ih, ParentSplits.pieceCount, NatCast.add]
          rfl

/-- A mapped parent coordinate reads the projection of its retained item.

The list identity and both supplied bounds identify the same source occurrence,
preserving the parent projection and its original positional coordinate. -/
theorem mapped_read {Item : Type u} (items : List Item) (project : Item → CenteredEdge curve differential)
    {parents : List (CenteredEdge curve differential)} (equal : items.map project = parents)
    (index : Fin items.length) (bound : index.val < parents.length) :
    parentAt parents ⟨index.val, bound⟩ = project (items[index.val]'index.isLt) := by
  subst parents
  exact Map.getElem_map project items index.val index.isLt bound

open Purelib.Riemann.Integration in
/-- Select a retained parent split through an exact mapped-list identity.

The original item index supplies the parent index and bound; transport preserves the selected split's membership in the
same family. -/
@[expose] def selectMapped {Item : Type u} {parents : List (CenteredEdge curve differential)}
    (splits : ParentSplits cuts parents) (items : List Item) (project : Item → CenteredEdge curve differential)
    (equal : items.map project = parents) (index : Fin items.length) :
    Selected splits (project (items[index.val]'index.isLt)) :=
  have bound : index.val < parents.length := by
    rw [← equal, Map.length_map]
    exact index.isLt
  Eq.mp (congrArg (Selected splits) (mapped_read items project equal index bound))
    (PreparedParentSplitSelection.select splits ⟨index.val, bound⟩)

end Purelib.Riemann.Integration.PreparedParentSplitSelection
