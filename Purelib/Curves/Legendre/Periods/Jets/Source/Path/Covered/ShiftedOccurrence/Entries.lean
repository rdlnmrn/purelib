module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
public import Purelib.Riemann.Integration.PreparedCoveredParentLists.Entries

/-! # Exact original covering patches at cached global shifted source occurrences

The original occurrence cache retains its block, child and full prefix offset.
The SAME global geometry's whole factory equation and covered append readbacks
then preserve the complete original patch/containment entry heterogeneously.
No local source allocation, seed substitution or patch preparation is involved.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

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
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

/-- A stored global source occurrence retains exactly its SAME original local covering patch and finish certificate.

The exact whole geometry equality is the real builder's original cache
identity. Equality elimination changes only that nominal index; the actual
Request and source preparation remain its supplied retained data. The full
prefix offset selects the original append occurrence independently of
repeated coordinate, parent or sheet values.
-/
theorem covered_entry_heq (located : Occurrence blocks request sourceIndex)
    (whole_eq : whole = build prepared ranges allocation admitted widths blocks oldGeometry oldRoots) :
    HEq (request.covered.entry sourceIndex)
      ((DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.parents.coveredParents.entry
        located.child) := by
  cases whole_eq
  let originalIndex :
      Fin (build prepared ranges allocation admitted widths blocks oldGeometry oldRoots).parents.length :=
    ⟨sourceIndex.val, Eq.mp
      (congrArg (fun parents => sourceIndex.val < parents.length) request.shape.property.symm) sourceIndex.isLt⟩
  have casted := CoveredParents.castParents_entry_heq request.shape.property
    (build prepared ranges allocation admitted widths blocks oldGeometry oldRoots).covered originalIndex sourceIndex rfl
  have retained := build_entry_heq prepared ranges allocation admitted widths blocks oldGeometry oldRoots
    located.block located.child originalIndex located.offset_eq
  exact casted.trans retained

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
