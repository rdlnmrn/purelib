module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.List.OfFn.Basic

/-! # Original local children at their unchanged global source indices

The whole geometry build equation identifies the original global concatenation.
Embedding a retained local occurrence preserves its original block/child spine
and exact global offset without retagging Targets or searching point values.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

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
    {admitted : Data.Gaussian.Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    (blocks : Blocks (target := target) prepared ranges allocation admitted widths)
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    (request : Request whole requestIndex globalFloor rootStage)

/-- The exact global source index of a supplied original block/child occurrence, retaining both ordered readbacks. -/
@[expose] def Position (outer : Fin (firstParent :: remaining).length)
    (inner : Fin
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length) :=
  { sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length //
    (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt =
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents[
        inner.val]'inner.isLt ∧
    sourceIndex.val = ((blockWords prepared ranges allocation admitted widths blocks).take outer.val).flatten.length +
      inner.val }

/-- Embed one supplied local child using the SAME retained whole geometry and cached original block-word table.

Only exact list/index transports run. No locate, source preparation, root
query, shifted acquisition or allocation is repeated. The resulting source
index belongs to the original global Request and its one global Targets.
-/
def positionWithWords
    (whole_eq : whole = build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (words : List (List (CenteredEdge (Fibre.frameCurve target) basis)))
    (words_eq : words = blockWords prepared ranges allocation admitted widths blocks)
    (outer : Fin (firstParent :: remaining).length)
    (inner : Fin
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length) :
    Position blocks request outer inner := by
  have joined : (request.shape.val.1 :: request.shape.val.2) = words.flatten :=
    request.shape.property.symm.trans
      ((congrArg (fun result => result.parents) whole_eq).trans
        ((build_parents prepared ranges allocation admitted widths blocks oldGeometry oldRoots).trans
          (congrArg List.flatten words_eq.symm)))
  have wordsLength : words.length = (firstParent :: remaining).length :=
    (congrArg List.length words_eq).trans Data.List.OfFn.Basic.length_ofFn
  let wordOuter : Fin words.length := ⟨outer.val,
    Eq.mpr (congrArg (fun length => outer.val < length) wordsLength) outer.isLt⟩
  have wordBound : outer.val < (blockWords prepared ranges allocation admitted widths blocks).length := by
    rewrite [blockWords, Data.List.OfFn.Basic.length_ofFn]
    exact outer.isLt
  have selected : words[wordOuter.val]'wordOuter.isLt =
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents :=
    (getElem_congr words_eq rfl wordOuter.isLt).trans
      (Data.List.OfFn.Basic.getElem_ofFn (fun index =>
        (DependentProduct.get (firstParent :: remaining) blocks index).shifted.parents.covered.parents) outer wordBound)
  let wordInner : Fin (words[wordOuter.val]'wordOuter.isLt).length := ⟨inner.val,
    Eq.mpr (congrArg (fun length => inner.val < length) (congrArg List.length selected)) inner.isLt⟩
  let found := Data.List.Flatten.position words wordOuter wordInner
  let sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length := ⟨found.val.val,
    Eq.mpr (congrArg (fun parents => found.val.val < parents.length) joined) found.val.isLt⟩
  refine ⟨sourceIndex, ?_, ?_⟩
  · exact (getElem_congr joined rfl sourceIndex.isLt).trans
      (found.property.1.trans (getElem_congr selected rfl wordInner.isLt))
  · exact found.property.2.trans
      (congrArg (fun table => (table.take outer.val).flatten.length + inner.val) words_eq)

namespace Position

variable {blocks request} {outer : Fin (firstParent :: remaining).length}
    {inner : Fin (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length}
    (position : Position blocks request outer inner)

/-- Read the exact original global source occurrence without changing its natural index. -/
@[expose] def sourceIndex := position.val

/-- The same embedded occurrence retains its original outer/inner indices as an actual Occurrence certificate. -/
@[expose] def located : Occurrence blocks request position.sourceIndex :=
  ⟨outer, ⟨inner, position.property.1, position.property.2⟩⟩

/-- The located global occurrence retains exactly the supplied original block occurrence. -/
theorem block_eq : position.located.block = outer := rfl

/-- The located global occurrence retains exactly the supplied original child occurrence. -/
theorem child_eq : position.located.child = inner := rfl

end Position

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
