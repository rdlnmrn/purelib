module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Cell.Integral
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Position
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Partition
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Chain
public import Purelib.Calculus.Jet.Quadratic.Weighted.Widths
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Actual retained whole-parent integral Taylor assembly

One original block Alignment is cached outside the child map. Each actual
child retains its SAME global source index, six original polynomial
restriction caches, per-time arithmetic data and integral certificate.
Exact interval-chain reassembly and weighted finite Cauchy give a factor
using the fixed original patch/count and parent endpoints, independently of
the increment, source stages and adaptive child count.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Curves.Legendre.Periods.Jets.Variation

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
  (startPoint finishPoint liftedCell ShiftedAcquisition)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (blockIndex : Fin (parent :: parents).length)

open Occurrence

namespace ValueBlock

/-- The SAME original ordered child parent list of this retained shifted block. -/
@[expose] def children :=
  (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted.parents.covered.parents

/-- Original local children retain their exact global source positions and the original global allocation owner. -/
@[expose] def Positions := DependentProduct (children (next := next) blockIndex)
  (fun index => Position next.blocks next.requested.request blockIndex index)

/-- One original signed block alignment on the already materialized path/reference owners. -/
@[expose] def Alignment := Acquisition.Segment.RootComparisons.Alignment
  (DependentProduct.get (parent :: parents) next.blocks blockIndex).comparison.paths
  (DependentProduct.get (parent :: parents) next.blocks blockIndex).comparison.firstReference

/-- Retained child ValueCells indexed by their original local occurrences and exact stored global positions. -/
@[expose] def Cells (positions : Positions (next := next) blockIndex) :=
  DependentProduct (children (next := next) blockIndex) (fun index =>
    ValueCell (source := source) (next := next) (spatial := spatial) (nonzero := nonzero)
      (DependentProduct.get (children (next := next) blockIndex) positions index).located)

/-- Retained child integral certificates on the SAME original cells and their actual cached observations. -/
@[expose] def Integrals (positions : Positions (next := next) blockIndex) (cells : Cells (next := next) blockIndex
    positions) :=
  DependentProduct (children (next := next) blockIndex) (fun index =>
    ValueCell.IntegralBank (source := source) (next := next) (spatial := spatial) (nonzero := nonzero)
      (DependentProduct.get (children (next := next) blockIndex) cells index))

end ValueBlock

/-- One original block's exact global positions, shared Alignment, child cells and their genuine integral Taylor caches.

All nominal old/global source requests remain indices. The materialized
cell family stores its original polynomial six-table restriction banks, and each
integral cache refers to that same cell rather than an independently built
copy. The Alignment is retained once outside the child producer.
-/
@[expose] def ValueBlock :=
  (positions : ValueBlock.Positions (next := next) blockIndex) ×
  (aligned : { value : ValueBlock.Alignment (next := next) blockIndex //
    value = (DependentProduct.get (parent :: parents) next.blocks blockIndex).comparison.align }) ×
  (cells : { value : ValueBlock.Cells (next := next) blockIndex positions //
    ∀ index, (DependentProduct.get (ValueBlock.children (next := next) blockIndex) value index).aligned =
      aligned.val }) ×
  ValueBlock.Integrals (next := next) blockIndex positions cells.val

namespace ValueBlock

/-- Acquire only the finite occurrence/cell/integral caches on one SAME retained shifted block.

One original block-word table and signed Alignment are computed before
child materialization. Each child's six restriction tables, ValueCell and
four integral certificates then execute once; callbacks keep their actual
Sample factories. No old source, target allocation, subdivision, trace or root
continuation is re-executed here.
-/
def build : ValueBlock (next := next) blockIndex :=
  let words := blockWords source.prepared ranges allocation admitted widths next.blocks
  let positions : Positions (next := next) blockIndex :=
    DependentProduct.ofFn (children (next := next) blockIndex) (fun index =>
      positionWithWords next.blocks next.requested.request next.geometry_eq words rfl blockIndex index)
  let aligned : Alignment (next := next) blockIndex :=
    (DependentProduct.get (parent :: parents) next.blocks blockIndex).comparison.align
  let entries : (index : Fin (children (next := next) blockIndex).length) →
      ValueCell (source := source) (next := next) (spatial := spatial) (nonzero := nonzero)
        (DependentProduct.get (children (next := next) blockIndex) positions index).located :=
    fun index =>
      let position := DependentProduct.get (children (next := next) blockIndex) positions index
      let restriction : ValueCell.Restrictions (source := source) (next := next)
          (spatial := spatial) (nonzero := nonzero) position.located := ShiftedAcquisition.Restrictions.build
        (source := source.prepared.entry blockIndex)
        (child := (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
          position.sourceIndex.val]'position.sourceIndex.isLt)
      ValueCell.ofRetained (source := source) (next := next) (spatial := spatial) (nonzero := nonzero)
        position.located restriction rfl aligned rfl
  let cells : Cells (next := next) blockIndex positions :=
    DependentProduct.ofFn (children (next := next) blockIndex) entries
  let integrals : Integrals (next := next) blockIndex positions cells :=
    DependentProduct.ofFn (children (next := next) blockIndex) (fun index =>
      ValueCell.buildIntegrals (source := source) (next := next) (spatial := spatial) (nonzero := nonzero)
        (DependentProduct.get (children (next := next) blockIndex) cells index))
  ⟨positions, ⟨aligned, rfl⟩, ⟨cells, by
    intro index
    let position := DependentProduct.get (children (next := next) blockIndex) positions index
    have selected : DependentProduct.get (children (next := next) blockIndex) cells index = entries index :=
      DependentProduct.get_ofFn (children (next := next) blockIndex) entries index
    let restriction : ValueCell.Restrictions (source := source) (next := next)
        (spatial := spatial) (nonzero := nonzero) position.located := ShiftedAcquisition.Restrictions.build
      (source := source.prepared.entry blockIndex)
      (child := (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
        position.sourceIndex.val]'position.sourceIndex.isLt)
    exact (congrArg (fun value : ValueCell (source := source) (next := next) (spatial := spatial)
        (nonzero := nonzero) position.located => value.aligned) selected).trans
      (ValueCell.ofRetained_aligned (source := source) (next := next)
        (spatial := spatial) (nonzero := nonzero) restriction rfl aligned rfl)⟩, integrals⟩

variable {blockIndex} (retained : ValueBlock (next := next) blockIndex)

/-- Read the SAME materialized exact local-to-global occurrence positions. -/
@[expose] def positions := retained.1

/-- Read the one actual block Alignment retained outside all child callbacks. -/
@[expose] def aligned := retained.2.1.val

/-- Read the original stored child ValueCells without re-running their producers. -/
@[expose] def cells := retained.2.2.1.val

/-- Read the actual integral Taylor caches on those SAME child cells. -/
@[expose] def integrals := retained.2.2.2

/-- Read the retained global position of one original local child occurrence. -/
@[expose] def position (index : Fin (children (next := next) blockIndex).length) :=
  DependentProduct.get (children (next := next) blockIndex) retained.positions index

/-- Read that original child's SAME stored ValueCell and restriction caches. -/
@[expose] def cell (index : Fin (children (next := next) blockIndex).length) :=
  DependentProduct.get (children (next := next) blockIndex) retained.cells index

/-- Read the original child's SAME actual integral Taylor certificate. -/
@[expose] def entry (index : Fin (children (next := next) blockIndex).length) (order coordinate : Fin 2) :=
  (((DependentProduct.get (children (next := next) blockIndex) retained.integrals index).get order).get coordinate).val

/-- Read the physical parameter interval from that SAME actual global centered child. -/
@[expose] def interval (index : Fin (children (next := next) blockIndex).length) :=
  ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    (retained.position index).sourceIndex.val]'(retained.position index).sourceIndex.isLt).parameterInterval

end ValueBlock

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
