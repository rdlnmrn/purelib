module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Position
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Cells
import Purelib.Data.List.Flatten.Table
import Purelib.Data.List.DependentProduct
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed

/-! # Original global model samples at retained block and child positions

The original ordered Position certificates regroup the literal global
prepared cell word without changing a source, target or query cache.
The selected-stage preparation-family law reads that SAME request model.
No completion or signed comparison is needed for this arithmetic readback.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

section SelectedModel

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : Request geometry index floor rootStage)

namespace Request

/-- The original selected programme-stage model reads the SAME actual Request preparation and cell lists. -/
theorem model_at_cells (channel : Fin 6) :
    (model request.covered request.chain request.attempt.preparationFamily channel index).cells =
      (sources request.covered request.attempt.2.1 request.chain).cells channel :=
  congrArg (fun source => source.cells channel) request.attempt.preparationFamily_sources

/-- The selected original model sample is the SAME literal whole Request integral sample. -/
theorem model_at_sample (channel : Fin 6) :
    (model request.covered request.chain request.attempt.preparationFamily channel index).integralSample =
      (PathModel.mk ((sources request.covered request.attempt.2.1 request.chain).cells channel)).integralSample :=
  congrArg (fun cells => (PathModel.mk cells).integralSample) (request.model_at_cells channel)

end Request

end SelectedModel

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
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    (request : Request whole requestIndex globalFloor rootStage)

namespace Position

/-- The stored exact global positions of all original block and child occurrences.

The two original dependent products retain ordered occurrences even when
physical points or parents repeat. Every entry is the original Position
certificate with its whole centered-parent and full-prefix equations.
-/
@[expose] def Family := DependentProduct (firstParent :: remaining) (fun outer =>
  DependentProduct
    (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents
    (fun inner => Position blocks request outer inner))

namespace Family

/-- Materialize the original global Position certificates once from the complete retained geometry factory.

One original block-word table precedes the ordered products. Only the
existing positionWithWords operation runs; no model, acquisition, query,
Target allocation, bank or completion is reconstructed.
-/
def build
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    (whole_eq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks oldGeometry oldRoots) :
    Family blocks request :=
  let words := blockWords prepared ranges allocation admitted widths blocks
  DependentProduct.ofFn (firstParent :: remaining) (fun outer =>
    DependentProduct.ofFn
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents
      (fun inner => positionWithWords blocks request whole_eq words rfl outer inner))

variable {blocks request} (retained : Family blocks request)

/-- Read one SAME stored Position, retaining both original bounded occurrence indices. -/
@[expose] def entry (outer : Fin (firstParent :: remaining).length)
    (inner : Fin
      (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents.length) :
    Position blocks request outer inner :=
  DependentProduct.get
    (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents
    (DependentProduct.get (firstParent :: remaining) retained outer) inner

variable {selectedStage : Nat} {selectedTargets : CellEndpoints.Targets request.chain.path selectedStage}
    (selected : PreparedParents request.covered globalFloor selectedTargets)

/-- Read the SAME globally allocated cell word in its original local block occurrence order. -/
@[expose] def groups (channel : Fin 6) (outer : Fin (firstParent :: remaining).length) : List CellModel :=
  List.ofFn (fun inner =>
    (selected.entry (retained.entry outer inner).sourceIndex).preparation.cell.models.cell channel)

/-- Original whole geometry and Position prefixes identify the literal global list with its exact ordered groups. -/
theorem cells_eq_groups
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    (whole_eq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (channel : Fin 6) :
    (sources request.covered selected request.chain).cells channel =
      (List.ofFn (fun outer => retained.groups selected channel outer)).flatten := by
  let words := fun outer : Fin (firstParent :: remaining).length =>
    (DependentProduct.get (firstParent :: remaining) blocks outer).shifted.parents.covered.parents
  have joined : (request.shape.val.1 :: request.shape.val.2) = (List.ofFn words).flatten :=
    request.shape.property.symm.trans
      ((congrArg (fun result => result.parents) whole_eq).trans
        (build_parents prepared ranges allocation admitted widths blocks oldGeometry oldRoots))
  let values := fun sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length =>
    (selected.entry sourceIndex).preparation.cell.models.cell channel
  let positions := fun outer : Fin (firstParent :: remaining).length =>
    fun inner : Fin (words outer).length => (retained.entry outer inner).sourceIndex
  have offsets (outer : Fin (firstParent :: remaining).length) (inner : Fin (words outer).length) :
      (positions outer inner).val = ((List.ofFn words).take outer.val).flatten.length + inner.val :=
    (retained.entry outer inner).property.2
  exact (cells_eq_ofFn request.covered selected request.chain channel).trans
    (Data.List.Flatten.ofFn_grouped words (congrArg List.length joined) values positions offsets)

/-- The original whole sample is the ordered sum of the SAME stored global child-cell samples.

Both sums range over original occurrences, including repeated values and
empty intermediate fibers. The proof only reads the existing model tables;
it constructs no polynomial restrictions or comparison certificates.
-/
theorem sample_eq_groups
    {oldGeometry : CenteredPathChain (firstParent :: remaining)
      (start := startPoint firstParent) (finish := startPoint firstParent)}
    {oldRoot : Named} {oldRoots : RootChain (firstParent :: remaining) oldRoot oldRoot}
    (whole_eq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks oldGeometry oldRoots)
    (channel : Fin 6) :
    (PathModel.mk ((sources request.covered selected request.chain).cells channel)).integralSample =
      sumFin (fun outer => sumFin (fun inner =>
        ((selected.entry (retained.entry outer inner).sourceIndex).preparation.cell.models.cell
          channel).integralSample)) :=
  (congrArg (fun cells => (PathModel.mk cells).integralSample)
    (retained.cells_eq_groups selected whole_eq channel)).trans
      ((PathModel.integralSample_flatten_ofFn (fun outer => retained.groups selected channel outer)).trans
        (sumFin_congr (fun outer => PathModel.integralSample_ofFn_eq_sumFin (fun inner =>
          (selected.entry (retained.entry outer inner).sourceIndex).preparation.cell.models.cell channel))))

end Family

end Position

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
