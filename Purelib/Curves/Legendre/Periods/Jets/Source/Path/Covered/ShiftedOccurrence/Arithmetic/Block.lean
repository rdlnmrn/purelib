module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block.Entries
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Weighted integral certificates on retained block entries

The original ordered child intervals reassemble the same retained cell integrals.
Finite weighted estimates bound their joint certificate by the original parent data.
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

variable {blockIndex} (retained : ValueBlock (next := next) blockIndex)

/-- The global interval is exactly the original local centered child interval, with repeated occurrences retained. -/
theorem interval_eq (index : Fin (children (next := next) blockIndex).length) :
    retained.interval index =
      (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted.intervalAt index :=
  congrArg Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge.parameterInterval
    (retained.position index).property.1

/-- The SAME actual global child interval view chains the original parent parameter zero to one. -/
theorem interval_chain : Partition.Interval.Chain 0 1 (List.ofFn retained.interval) := by
  have equal : List.ofFn retained.interval = List.ofFn
      (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted.intervalAt :=
    List.OfFn.Basic.ofFn_congr (fun index => retained.interval_eq index)
  exact Eq.mpr (congrArg (Partition.Interval.Chain 0 1) equal)
    (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted.interval_chain

/-- The original accepted width of every SAME actual child is nonnegative, including zero width. -/
theorem width_nonnegative (index : Fin (children (next := next) blockIndex).length) :
    0 ≤ (retained.interval index).finish - (retained.interval index).start := by
  rewrite [retained.interval_eq]
  exact (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted.interval_nonnegative index

/-- The original child widths sum exactly to one without a child-count estimate. -/
theorem sum_widths : Algebra.FiniteSum.Fin.sumFin (fun index =>
    (retained.interval index).finish - (retained.interval index).start) = 1 :=
  (Partition.Interval.Chain.sum_widths retained.interval retained.interval_chain).trans (by ring1)

/-- The selected child bases reassemble the SAME original old base parent integral sample. -/
theorem base_sum (order coordinate : Fin 2) : Algebra.FiniteSum.Fin.sumFin (fun index => (retained.entry index
    order coordinate).base) =
    ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).integralSample := by
  calc
    _ = Algebra.FiniteSum.Fin.sumFin (fun index =>
        ((retained.cell index).restriction.model (Specification.Table.baseIndex order coordinate)).integralSample) :=
      Algebra.FiniteSum.Fin.sumFin_congr (fun index =>
        (((DependentProduct.get (children (next := next) blockIndex) retained.integrals index).get order).get
            coordinate).property.1)
    _ = _ := Restriction.integralSample_sum_unit
      ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
          coordinate)) retained.interval
      (fun index => (retained.cell index).restriction.cache (Specification.Table.baseIndex order coordinate))
          retained.interval_chain

/-- The selected child slopes reassemble the SAME original independent derivative parent integral sample. -/
theorem slope_sum (order coordinate : Fin 2) : Algebra.FiniteSum.Fin.sumFin (fun index => (retained.entry index
    order coordinate).slope) =
    ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).integralSample := by
  calc
    _ = Algebra.FiniteSum.Fin.sumFin (fun index =>
        ((retained.cell index).restriction.model (Specification.Table.slopeIndex order coordinate)).integralSample) :=
      Algebra.FiniteSum.Fin.sumFin_congr (fun index =>
        (((DependentProduct.get (children (next := next) blockIndex) retained.integrals index).get order).get
            coordinate).property.2.2.1)
    _ = _ := Restriction.integralSample_sum_unit
      ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.slopeIndex order
          coordinate)) retained.interval
      (fun index => (retained.cell index).restriction.cache (Specification.Table.slopeIndex order coordinate))
          retained.interval_chain

/-- The original output sum retains precisely the actual target global cell integrals in original local-child order. -/
theorem output_sum (order coordinate : Fin 2) : Algebra.FiniteSum.Fin.sumFin (fun index => (retained.entry index
    order coordinate).output) =
    Algebra.FiniteSum.Fin.sumFin (fun index =>
      ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample) :=
  Algebra.FiniteSum.Fin.sumFin_congr (fun index =>
    (((DependentProduct.get (children (next := next) blockIndex) retained.integrals index).get order).get
        coordinate).property.2.1)

/-- The original target cell models in exact retained local-child order, as a finite view of global source caches. -/
@[expose] def targetCells (order coordinate : Fin 2) : List CellModel := List.ofFn (fun index =>
  ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)))

/-- The SAME target child-list integral sample is its original ordered finite sample sum. -/
theorem targetSample_eq (order coordinate : Fin 2) : (PathModel.mk (retained.targetCells order
    coordinate)).integralSample =
    Algebra.FiniteSum.Fin.sumFin (fun index =>
      ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample) :=
  PathModel.integralSample_ofFn_eq_sumFin _

/-- The density is computed on the original fixed covered patch/count and whole physical parent endpoints. -/
@[expose] def density (index : Fin (parent :: parents).length) (order coordinate : Fin 2) : Rational :=
  2 * (4 * (Point.Step.Joint.rowCeiling
    ((covered.entry index).1.neighborhood count) 0 order coordinate + 7 / 2 + 7 / 2 + 7 / 2)) *
    Norm.Basic.normSq
      ((finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate -
        (startPoint ((parent :: parents)[index.val]'index.isLt)).coordinate)

/-- The original fixed-geometry density is nonnegative without selecting a child or a source-request stage. -/
theorem density_nonnegative (index : Fin (parent :: parents).length) (order coordinate : Fin 2) :
    0 ≤ density (covered := covered) index order coordinate := by
  have original := Point.Step.Joint.rowCeiling_nonnegative
    ((covered.entry index).1.neighborhood count) 0 order coordinate
  have constants : (0 : Rational) ≤ 7 / 2 + 7 / 2 + 7 / 2 := by decide
  have sum := Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct original constants
  have coefficient : (0 : Rational) ≤ 2 * 4 := by decide
  have bounded := Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct coefficient sum)
    (Norm.Basic.normSq_nonneg
      ((finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate -
        (startPoint ((parent :: parents)[index.val]'index.isLt)).coordinate))
  exact bounded.trans_eq (by unfold density; ring1)

/-- Every retained block keeps the exact displacement of each original restricted child model.

The complete proposition retains both requested parent families, their
original occurrence bounds, and the same stored restriction and target caches.
-/
abbrev DisplacementEquation : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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
    {blockIndex : Fin (parent :: parents).length}
    (retained : ValueBlock (next := next) blockIndex)
    (index : Fin (children (next := next) blockIndex).length) (channel : Fin 6),
    ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
      channel).displacement = ((retained.cell index).restriction.model channel).displacement

/-- The actual target child retains the scalar displacement of its SAME cached original polynomial restriction.

The existing endpoint readbacks compare the actual global prepared model
with the retained restricted model. Every channel uses the same physical
child; neither source, restriction, query nor target model is rebuilt.
-/
theorem displacement_eq : DisplacementEquation := by
  intro parameter increment frame basis target count parent parents covered chain ranges allocation admitted widths
    root roots spatial nonzero sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage
    source next blockIndex retained index channel
  let position := retained.position index
  let shifted := (DependentProduct.get (parent :: parents) next.blocks blockIndex).shifted
  let fresh := next.requested.prepared.entry position.sourceIndex
  have sameStart := ((retained.cell index).restriction.model_start
    shifted index position.property.1 channel).trans (fresh.preparation.cell.models.cell_start channel).symm
  have sameFinish := ((retained.cell index).restriction.model_finish
    shifted index position.property.1 channel).trans (fresh.preparation.cell.models.cell_finish channel).symm
  exact (congrArg (fun value : Canonical =>
    value - (fresh.preparation.cell.models.cell channel).start) sameFinish.symm).trans
      (congrArg (fun value : Canonical =>
        ((retained.cell index).restriction.model channel).finish - value) sameStart.symm)

/-- The original target child's displacement quadrance pays its squared original width against the fixed parent. -/
theorem displacement_normSq (index : Fin (children (next := next) blockIndex).length) (order coordinate : Fin 2) :
    Norm.Basic.normSq
      ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).displacement =
      ((retained.interval index).finish - (retained.interval index).start) ^ 2 *
        Norm.Basic.normSq ((source.prepared.entry blockIndex).preparation.cell.models.cell
            (Specification.Table.baseIndex order coordinate)).displacement := by
  exact (congrArg Norm.Basic.normSq
    (retained.displacement_eq index (Specification.Table.baseIndex order coordinate))).trans
      (Restriction.displacement_normSq
        ((source.prepared.entry blockIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate))
        ((retained.cell index).restriction.cache (Specification.Table.baseIndex order coordinate)))

/-- Each SAME actual integral certificate factor is paid by the squared original width and fixed-parent density. -/
theorem entry_factor (index : Fin (children (next := next) blockIndex).length) (order coordinate : Fin 2) :
    (retained.entry index order coordinate).factor = density (covered := covered) blockIndex order coordinate *
      ((retained.interval index).finish - (retained.interval index).start) ^ 2 := by
  let originalParent := (parent :: parents)[blockIndex.val]'blockIndex.isLt
  let old := source.prepared.entry blockIndex
  have original : (retained.entry index order coordinate).factor =
      2 * (4 * (Point.Step.Joint.rowCeiling old.preparation.cell.patch increment order coordinate +
        7 / 2 + 7 / 2 + 7 / 2)) * Norm.Basic.normSq
          ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
            (Specification.Table.baseIndex order coordinate)).displacement :=
    (((DependentProduct.get (children (next := next) blockIndex) retained.integrals index).get order).get
        coordinate).property.2.2.2
  have actualCeiling := congrArg
    (fun cell : Source.Cell (parameter := parameter) (liftedCell originalParent) =>
      Point.Step.Joint.rowCeiling cell.patch increment order coordinate) old.preparation.cell_eq
  have sameCeiling : Point.Step.Joint.rowCeiling
      old.preparation.cell.patch increment order coordinate =
      Point.Step.Joint.rowCeiling ((covered.entry blockIndex).1.neighborhood count) 0 order coordinate := by
    calc
      _ = Point.Step.Joint.rowCeiling
          ((covered.entry blockIndex).1.neighborhood count) increment order coordinate := actualCeiling
      _ = _ := Point.Step.Joint.rowCeiling_increments
        ((covered.entry blockIndex).1.neighborhood count) increment 0 order coordinate
  have sameDisplacement : (old.preparation.cell.models.cell (Specification.Table.baseIndex order
      coordinate)).displacement =
      (finishPoint originalParent).coordinate - (startPoint originalParent).coordinate := by
    unfold CellModel.displacement
    rewrite [old.preparation.cell.models.cell_start (Specification.Table.baseIndex order coordinate),
      old.preparation.cell.models.cell_finish (Specification.Table.baseIndex order coordinate)]
    rfl
  rewrite [original, retained.displacement_normSq index order coordinate, sameCeiling, sameDisplacement]
  unfold density
  ring1

/-- Construct one finite Taylor certificate from the SAME retained child integrals with a mesh-independent factor.

Weighted finite Cauchy uses the original nonnegative child widths. Their
sum is exactly one, so no adaptive count multiplies the fixed-parent
density, independently of increment and source stages. No new child restriction, observation, query or integral factory
runs during this certificate assembly.
-/
@[expose] def certificate (order coordinate : Fin 2) : Quadratic.Basic.Certificate increment :=
  Quadratic.Basic.Certificate.sumWithWidths (fun index => retained.entry index order coordinate)
    (fun index => (retained.interval index).finish - (retained.interval index).start)
    (density (covered := covered) blockIndex order coordinate) (density_nonnegative (covered := covered)
        blockIndex order coordinate)
    retained.width_nonnegative
    (fun index => by
      rewrite [retained.entry_factor index order coordinate]
      exact Data.Rat.Fraction.Order.Basic.le_refl _)

/-- The assembled certificate base is the SAME selected original whole old parent integral. -/
theorem certificate_base (order coordinate : Fin 2) : (retained.certificate order coordinate).base =
    ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).integralSample := retained.base_sum order coordinate

/-- The assembled slope is the SAME selected original independent derivative parent integral. -/
theorem certificate_slope (order coordinate : Fin 2) : (retained.certificate order coordinate).slope =
    ((source.prepared.entry blockIndex).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).integralSample := retained.slope_sum order coordinate

/-- The assembled output is the actual original target child integral sum in retained local-child order. -/
theorem certificate_output (order coordinate : Fin 2) : (retained.certificate order coordinate).output =
    Algebra.FiniteSum.Fin.sumFin (fun index =>
      ((next.requested.prepared.entry (retained.position index).sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample) := retained.output_sum order coordinate

/-- The assembled output is the actual stored target child-list integral sample without replacing any cell values. -/
theorem certificate_targetSample (order coordinate : Fin 2) : (retained.certificate order coordinate).output =
    (PathModel.mk (retained.targetCells order coordinate)).integralSample :=
  (retained.certificate_output order coordinate).trans (retained.targetSample_eq order coordinate).symm

/-- The exact factor is the computed fixed-parent density, independent of the adaptive child count. -/
theorem certificate_factor (order coordinate : Fin 2) : (retained.certificate order coordinate).factor = (density
    (covered := covered) blockIndex order coordinate) := by
  change (density (covered := covered) blockIndex order coordinate) * (Algebra.FiniteSum.Fin.sumFin (fun index =>
    (retained.interval index).finish - (retained.interval index).start)) ^ 2 = (density (covered := covered)
        blockIndex order coordinate)
  rewrite [retained.sum_widths]
  ring1

end ValueBlock

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
