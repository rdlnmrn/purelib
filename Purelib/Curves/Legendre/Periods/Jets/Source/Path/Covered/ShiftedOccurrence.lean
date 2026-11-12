module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Entries
public import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.List.OfFn.Basic

/-! # Actual global shifted source occurrences at their original retained blocks

The SAME cached ShiftedGeometry and its whole build equation identify its
actual concatenated parent word. A deterministic ordered lookup returns the
original block and local child at each global source/bank index. All source
queries remain on the actual StageAttempt preparation and its ONE original
global Targets; no local shifted Prepared wrapper or target transport is used.
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

section RequestEntries

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {whole : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat}

namespace Request

variable (request : Request whole index floor rootStage)

/-- Read an actual bank position as its SAME global parent/source occurrence using the retained bank length law. -/
@[expose] def bankSourceIndex (bankIndex : Fin request.bank.length) :
    Fin (request.shape.val.1 :: request.shape.val.2).length :=
  ⟨bankIndex.val, Eq.mp (congrArg (fun length => bankIndex.val < length) request.attempt.bank_length)
    bankIndex.isLt⟩

/-- The bank-to-source index transport keeps the original natural occurrence coordinate exactly. -/
theorem bankSourceIndex_val (bankIndex : Fin request.bank.length) :
    (request.bankSourceIndex bankIndex).val = bankIndex.val := by rfl

/-- The actual bank occurrence retains the SAME global source preparation, query and original Targets.

The source query is `(request.attempt.2.1.entry (request.bankSourceIndex ...)).preparation.query`.
The bank's retained whole factory equation identifies that SAME preparation;
no local-target cast or replacement endpoint/source observation occurs.
-/
theorem bank_entry_eq (bankIndex : Fin request.bank.length) :
    request.bank[bankIndex.val]'bankIndex.isLt =
      Vertex.Entry.request (request.attempt.2.1.entry (request.bankSourceIndex bankIndex)).firstVertex.val
        request.attempt.1.val.endpoint request.attempt.1.val.endpoint_positive :=
  request.attempt.bank_getElem (request.bankSourceIndex bankIndex) bankIndex.isLt

end Request

end RequestEntries

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

/-- An original block/local child at one retained GLOBAL source position, including the exact ordered prefix offset.

The global index remains the original Request's bounded source occurrence.
The child is read from the SAME retained acquisition parent list. Equality
of values alone does not choose an occurrence; the original block order and
full natural offset are certified separately.
-/
@[expose] def Occurrence (sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length) :=
  (outer : Fin (firstParent :: remaining).length) ×
  { inner : Fin (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length //
    (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt =
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents[
        inner.val]'inner.isLt ∧
    sourceIndex.val = ((blockWords prepared ranges allocation admitted widths blocks).take outer.val).flatten.length +
      inner.val }

namespace Occurrence

variable {blocks request} {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)

/-- Read the original block occurrence retained by the actual global source location. -/
@[expose] def block : Fin (firstParent :: remaining).length := located.1

/-- Read the local child occurrence in that SAME original retained block's actual parent list. -/
@[expose] def child :
    Fin (DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.parents.covered.parents.length :=
  located.2.val

/-- The actual global parent is the identical retained parent at the stored original block/child indices. -/
theorem parent_eq :
    (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt =
      (DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.parents.covered.parents[
        located.child.val]'located.child.isLt := located.2.property.1

/-- The full original prefix offset preserves the global occurrence independently of equal repeated parent values. -/
theorem offset_eq :
    sourceIndex.val =
      ((blockWords prepared ranges allocation admitted widths blocks).take located.block.val).flatten.length +
        located.child.val := located.2.property.2

end Occurrence

/-- Locate a global source position in its original retained block without changing a query cache.

The whole retained geometry factory equation supplies the ordered block
readback. The original Request shape changes only its parent-list index.
The finite locator retains global/source indices, repeated physical values,
empty intervening blocks and the actual global allocation unchanged.
-/
private def locateWithWords
    (whole_eq : whole = build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (words : List (List (CenteredEdge (Fibre.frameCurve target) basis)))
    (words_eq : words = blockWords prepared ranges allocation admitted widths blocks)
    (sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length) :
    Occurrence blocks request sourceIndex := by
  have joined : (request.shape.val.1 :: request.shape.val.2) = words.flatten :=
    request.shape.property.symm.trans
      ((congrArg (fun result => result.parents) whole_eq).trans
        ((build_parents prepared ranges allocation admitted widths blocks oldGeometry oldRoots).trans
          (congrArg List.flatten words_eq.symm)))
  let globalIndex : Fin words.flatten.length := ⟨sourceIndex.val,
    Eq.mp (congrArg (fun parents => sourceIndex.val < parents.length) joined) sourceIndex.isLt⟩
  let found := Data.List.Flatten.locate words globalIndex
  have wordsLength : words.length = (firstParent :: remaining).length :=
    (congrArg List.length words_eq).trans (Data.List.OfFn.Basic.length_ofFn)
  have outerBound : found.1.val < (firstParent :: remaining).length :=
    Eq.mp (congrArg (fun length => found.1.val < length) wordsLength) found.1.isLt
  let outer : Fin (firstParent :: remaining).length := ⟨found.1.val, outerBound⟩
  have selected : words[found.1.val]'found.1.isLt =
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents := by
    have wordBound : found.1.val <
        (blockWords prepared ranges allocation admitted widths blocks).length :=
      Eq.mp (congrArg (fun length => found.1.val < length) (congrArg List.length words_eq)) found.1.isLt
    exact (getElem_congr words_eq rfl found.1.isLt).trans
      (Data.List.OfFn.Basic.getElem_ofFn (fun index =>
        (DependentProduct.get (firstParent :: remaining) blocks index).shifted.parents.covered.parents) outer wordBound)
  have innerBound : found.2.val.val <
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length :=
    Eq.mp (congrArg (fun length => found.2.val.val < length) (congrArg List.length selected)) found.2.val.isLt
  let inner :
      Fin (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length :=
    ⟨found.2.val.val, innerBound⟩
  refine ⟨outer, ⟨inner, ?_, ?_⟩⟩
  · exact (getElem_congr joined rfl sourceIndex.isLt).trans
      (found.2.property.1.trans (getElem_congr selected rfl found.2.val.isLt))
  · exact found.2.property.2.trans
      (congrArg (fun table => (table.take found.1.val).flatten.length + found.2.val.val) words_eq)

/-- A stored occurrence map at every SAME original global source/parent index.

The existing dependent product materializes the finite geometric locations
once outside query callbacks. It stores no replacement source, Targets or
query and retains the original Request as its nominal parent.
-/
abbrev Occurrences := DependentProduct (request.shape.val.1 :: request.shape.val.2)
  (fun sourceIndex => Occurrence blocks request sourceIndex)

/-- Materialize the actual global occurrence map using one cached table of the SAME original retained block words.

Only the existing block parent-list projections and the exact whole-build
readback are used. The finite table is computed once before materializing
all original global positions; subsequent callbacks read that stored map.
-/
def occurrences (whole_eq : whole = build prepared ranges allocation admitted widths blocks oldGeometry oldRoots) :
    Occurrences blocks request :=
  let words := blockWords prepared ranges allocation admitted widths blocks
  DependentProduct.ofFn (request.shape.val.1 :: request.shape.val.2)
    (fun sourceIndex => locateWithWords blocks request whole_eq words rfl sourceIndex)

/-- Locate an actual bank occurrence by reading the SAME stored global source-occurrence map.

The bank's own original global index supplies the lookup. No block table,
source preparation, endpoint query or allocation is reconstructed here.
-/
@[expose] def bankOccurrence (stored : Occurrences blocks request) (bankIndex : Fin request.bank.length) :
    Occurrence blocks request (request.bankSourceIndex bankIndex) :=
  DependentProduct.get (request.shape.val.1 :: request.shape.val.2) stored (request.bankSourceIndex bankIndex)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
