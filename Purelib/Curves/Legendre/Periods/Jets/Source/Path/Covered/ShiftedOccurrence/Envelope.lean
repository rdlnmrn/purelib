module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Entries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Envelope
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Bounds.Rows
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Lineage

/-! # Actual global incoming-source ceilings from original retained block occurrences

The original occurrence map identifies both the physical child and its
whole covering-patch entry. Its actual child ceiling is bounded by the
finite maximum of original retained source-neighborhood computations.
No all-stage completion, desired H or signed-root relation is inferred.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step (Joint)

/-- Whole exact covering-entry transport preserves its scalar row ceiling under the original parent equality. -/
private theorem entry_rowCeiling_eq {parameter : Canonical} {frame : Paths.Frame parameter}
    {basis : Differential 1} {count : Nat} {firstParent lastParent : CenteredEdge (Fibre.frameCurve frame) basis}
    (parentEq : firstParent = lastParent)
    (first : { patch : PreparedPatch firstParent //
      (patch.neighborhood count).box.Contains (firstParent.edge.point 1) })
    (last : { patch : PreparedPatch lastParent //
      (patch.neighborhood count).box.Contains (lastParent.edge.point 1) })
    (same : HEq first last) (increment : Canonical) (order coordinate : Fin 2) :
    Joint.rowCeiling (first.val.neighborhood count) increment order coordinate =
      Joint.rowCeiling (last.val.neighborhood count) increment order coordinate := by
  cases parentEq
  have equal : first = last := eq_of_heq same
  cases equal
  rfl

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}

namespace Occurrence

/-- The actual global occurrence preserves both physical endpoint memberships in the same original ancestral box.

The inputs concern its original immediate parent at the stored block index.
The exact global/local parent equality and retained child endpoint theorem
preserve the very same box. Applying this operation along actual successive
occurrence maps composes lineage without any enlargement or new acquisition.
-/
theorem endpoints_inside {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex) {box : Box}
    (firstInside : box.Contains (startPoint
      ((firstParent :: remaining)[located.block.val]'located.block.isLt)).coordinate)
    (lastInside : box.Contains (PreparedParent.finishPoint
      ((firstParent :: remaining)[located.block.val]'located.block.isLt)).coordinate) :
    box.Contains (startPoint
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)).coordinate ∧
      box.Contains (PreparedParent.finishPoint
        ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)).coordinate := by
  let linked := DependentProduct.get (firstParent :: remaining) blocks located.block
  have childBounds := linked.shifted.childEndpoints_inside firstInside lastInside located.child rfl
  have firstEq := congrArg (fun parent => (startPoint parent).coordinate) located.parent_eq
  have lastEq := congrArg (fun parent => (PreparedParent.finishPoint parent).coordinate) located.parent_eq
  exact ⟨Eq.mp (congrArg (fun point => box.Contains point) firstEq.symm) childBounds.1,
    Eq.mp (congrArg (fun point => box.Contains point) lastEq.symm) childBounds.2⟩

section Comparison

variable {oldGeometry : CenteredPathChain (firstParent :: remaining)
    (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}

/-- Every located actual global patch inherits the pre-mesh ceiling of its original retained source family.

The full original parent equality and complete covering-entry HEq identify
the SAME stored local child patch. Its actual acquired-child bound then
composes with the finite maximum of original source-neighborhood caches.
No desired ceiling or final programme comparison is an input.
-/
theorem rowCeiling_le {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)
    (wholeEq : whole = build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Joint.rowCeiling ((request.covered.entry sourceIndex).val.neighborhood count)
        laterIncrement order coordinate ≤ prepared.envelopeCeiling := by
  let linked := DependentProduct.get (firstParent :: remaining) blocks located.block
  have same := entry_rowCeiling_eq (frame := target) (basis := basis) (count := count)
    located.parent_eq (request.covered.entry sourceIndex)
    (linked.shifted.parents.coveredParents.entry located.child)
    (located.covered_entry_heq wholeEq) laterIncrement order coordinate
  have bounded := linked.shifted.child_rowCeiling_le located.child count laterIncrement order coordinate
  exact same.trans_le (bounded.trans (prepared.entry_envelopeCeiling_le located.block))

end Comparison

end Occurrence

namespace Request

variable (request)

/-- Carry the retained ancestral endpoint assignment through this SAME actual global occurrence map.

The original finite box family and ancestor indices remain unchanged.
Each new occurrence reads its immediate original block, then reads that
block's retained ancestor. Only existing DependentProduct.ofFn/get and the
actual endpoint-lineage theorem are used; no second path walker is built.
-/
def carryEndpoints {size : Nat} (boxes : Fin size → Box)
    (previous : DependentProduct (firstParent :: remaining) (fun index =>
      { ancestor : Fin size //
        (boxes ancestor).Contains
            (startPoint ((firstParent :: remaining)[index.val]'index.isLt)).coordinate ∧
          (boxes ancestor).Contains
            (PreparedParent.finishPoint ((firstParent :: remaining)[index.val]'index.isLt)).coordinate }))
    (stored : Occurrences blocks request) :
    DependentProduct (request.shape.val.1 :: request.shape.val.2) (fun index =>
      { ancestor : Fin size //
        (boxes ancestor).Contains
            (startPoint ((request.shape.val.1 :: request.shape.val.2)[index.val]'index.isLt)).coordinate ∧
          (boxes ancestor).Contains
            (PreparedParent.finishPoint
              ((request.shape.val.1 :: request.shape.val.2)[index.val]'index.isLt)).coordinate }) :=
  DependentProduct.ofFn (request.shape.val.1 :: request.shape.val.2) (fun index =>
    let located := DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored index
    let ancestor := DependentProduct.get (firstParent :: remaining) previous located.block
    ⟨ancestor.val, located.endpoints_inside ancestor.property.1 ancestor.property.2⟩)

/-- Every carried ancestor is exactly the original stored ancestor at the actual block occurrence.

The complete subtype entry, including both original-box endpoint proofs,
is the existing finite product constructor's result. The whole occurrence
map, previous ancestry product and fixed box family are retained inputs.
-/
theorem carryEndpoints_entry {size : Nat} (boxes : Fin size → Box)
    (previous : DependentProduct (firstParent :: remaining) (fun index =>
      { ancestor : Fin size //
        (boxes ancestor).Contains
            (startPoint ((firstParent :: remaining)[index.val]'index.isLt)).coordinate ∧
          (boxes ancestor).Contains
            (PreparedParent.finishPoint ((firstParent :: remaining)[index.val]'index.isLt)).coordinate }))
    (stored : Occurrences blocks request)
    (index : Fin (request.shape.val.1 :: request.shape.val.2).length) :
    DependentProduct.get (request.shape.val.1 :: request.shape.val.2)
        (request.carryEndpoints boxes previous stored) index =
      let located := DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored index
      let ancestor := DependentProduct.get (firstParent :: remaining) previous located.block
      ⟨ancestor.val, located.endpoints_inside ancestor.property.1 ancestor.property.2⟩ :=
  DependentProduct.get_ofFn (request.shape.val.1 :: request.shape.val.2) _ index

variable {oldGeometry : CenteredPathChain (firstParent :: remaining)
    (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}

/-- Every actual incoming covered occurrence has the same computed original-family ceiling at all later source stages.

The stored occurrence map is consumed at each original index. Stage changes
alter Targets and preparation requests on this SAME covering spine, so the
bound already has exactly the owner/index shape required by the all-later
Taylor and divided-difference constructors.
-/
theorem rowCeiling_le (stored : Occurrences blocks request)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (laterIncrement : Canonical) (order coordinate : Fin 2)
    (sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length) :
    Joint.rowCeiling ((request.covered.entry sourceIndex).val.neighborhood count)
        laterIncrement order coordinate ≤ prepared.envelopeCeiling :=
  (DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored sourceIndex).rowCeiling_le
    wholeEq laterIncrement order coordinate

end Request

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
