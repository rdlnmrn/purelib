module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Programs
import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Global finite Taylor certificates on actual source-programme samples

The selected global certificate already retains all original parent blocks,
child restrictions and actual arithmetic observations. This operation changes
only its displayed base and slope to independent actual progressive samples
on the same original fixed source cycle. Their original Targets derive both
payments; the output remains the same globally allocated shifted cell word.
No target programme coherence or canonical-cycle attachment is asserted.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

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

namespace ValueBlocks.Integral

variable {retained : ValueBlocks (next := next)} (actual : Integral retained)
    (preparations : (index : Nat) →
      PreparedParents covered sourceFloor (CellEndpoints.Targets.build chain.path index))
    (programmes : (channel : Fin 6) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (constantCycle chain))
    (programme_cells : ∀ channel index, ((programmes channel).integral.model index).cells =
      (sources covered (preparations index) chain).cells channel)
    (index : Nat) (after : source.selected.stage ≤ index)

include preparations programme_cells after in
/-- The programme base differs from this same stored global base by its computed fourth-order payment. -/
theorem program_base_difference_le (order coordinate : Fin 2) :
    Norm.Basic.normSq
      (((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample -
        (actual.certificate order coordinate).base) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
  have sourceSample : (actual.certificate order coordinate).base =
      (PathModel.mk ((sources covered source.prepared chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample :=
    (actual.base order coordinate).trans
      (congrArg (fun cells => (PathModel.mk cells).integralSample)
        (ValueBlocks.oldCells_eq_sources (source := source) (Specification.Table.baseIndex order coordinate)))
  have difference := source.program_difference_le preparations (Specification.Table.baseIndex order coordinate)
    index after (programmes (Specification.Table.baseIndex order coordinate))
    (programme_cells (Specification.Table.baseIndex order coordinate) index)
  rewrite [← sourceSample] at difference
  exact difference.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (spatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
    (errorScale_nonnegative (parent :: parents)))

include preparations programme_cells after in
/-- The independent programme slope differs from the same stored derivative integral by its computed payment. -/
theorem program_slope_difference_le (order coordinate : Fin 2) :
    Norm.Basic.normSq
      (((programmes (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample -
        (actual.certificate order coordinate).slope) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
  have sourceSample : (actual.certificate order coordinate).slope =
      (PathModel.mk ((sources covered source.prepared chain).cells
        (Specification.Table.slopeIndex order coordinate))).integralSample :=
    (actual.slope order coordinate).trans
      (congrArg (fun cells => (PathModel.mk cells).integralSample)
        (ValueBlocks.oldCells_eq_sources (source := source) (Specification.Table.slopeIndex order coordinate)))
  have difference := source.program_difference_le preparations (Specification.Table.slopeIndex order coordinate)
    index after (programmes (Specification.Table.slopeIndex order coordinate))
    (programme_cells (Specification.Table.slopeIndex order coordinate) index)
  rewrite [← sourceSample] at difference
  exact difference.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (spatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
    (errorScale_nonnegative (parent :: parents)))

/-- The unchanged global target sample is exactly the original certificate's output and costs no perturbation. -/
private theorem target_difference_le (order coordinate : Fin 2) :
    Norm.Basic.normSq
      ((PathModel.mk (ValueBlocks.targetCells (next := next) order coordinate)).integralSample -
        (actual.certificate order coordinate).output) ≤
      0 * Norm.Basic.normSq increment ^ 2 := by
  rewrite [actual.output order coordinate, Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero,
    Field.zero_mul_direct]
  exact Order.Basic.le_refl 0

/-- Transport the same selected global certificate to independent actual base and slope programme samples.

The original source's admitted common allocation gives the unit increment
bound. Its sufficient stage and both original Targets derive the two
fixed-geometry discrepancy factors. The original target cell word remains
the output, with no supplied final Taylor or programme comparison.
-/
def atPrograms (order coordinate : Fin 2) : Quadratic.Basic.Certificate increment := by
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  exact (actual.certificate order coordinate).perturb
    (((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample)
    (PathModel.mk (ValueBlocks.targetCells (next := next) order coordinate)).integralSample
    (((programmes (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample)
    (errorScale (parent :: parents)) 0 (errorScale (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) (Order.Basic.le_refl 0)
    (errorScale_nonnegative (parent :: parents)) unit
    (actual.program_base_difference_le preparations programmes programme_cells index after order coordinate)
    (actual.target_difference_le order coordinate)
    (actual.program_slope_difference_le preparations programmes programme_cells index after order coordinate)

/-- The transported base is the actual retained progressive base-channel sample at its unchanged requested index. -/
theorem atPrograms_base (order coordinate : Fin 2) :
    (actual.atPrograms preparations programmes programme_cells index after order coordinate).base =
      ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample := by
  unfold atPrograms
  rfl

/-- The transported output remains the same actual globally allocated shifted target cell-word sample. -/
theorem atPrograms_output (order coordinate : Fin 2) :
    (actual.atPrograms preparations programmes programme_cells index after order coordinate).output =
      (PathModel.mk (ValueBlocks.targetCells (next := next) order coordinate)).integralSample := by
  unfold atPrograms
  rfl

/-- The transported slope is the actual independent progressive derivative-channel sample at the same index. -/
theorem atPrograms_slope (order coordinate : Fin 2) :
    (actual.atPrograms preparations programmes programme_cells index after order coordinate).slope =
      ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample := by
  unfold atPrograms
  rfl

/-- The transported factor depends only on the fixed original geometry and selected row's fixed ceiling. -/
theorem atPrograms_factor (order coordinate : Fin 2) :
    (actual.atPrograms preparations programmes programme_cells index after order coordinate).factor =
      4 * (ValueBlocks.factor (covered := covered) order coordinate +
        2 * errorScale (parent :: parents)) := by
  unfold atPrograms
  change 4 * ((actual.certificate order coordinate).factor + errorScale (parent :: parents) + 0 +
    errorScale (parent :: parents)) = _
  rewrite [actual.factor_eq order coordinate]
  ring1

include actual preparations programme_cells after in
/-- The actual target word and independent same-cycle programme samples have a fixed-geometry parameter remainder.

All source and target observations, allocation stages, signed root owners
and adaptive child restrictions are those retained by the original global
certificate. This statement does not identify the target word with a
progressive target programme or a canonical transported geometric period.
-/
theorem atPrograms_remainder_le (order coordinate : Fin 2) :
    Canonical.normSq
      ((PathModel.mk (ValueBlocks.targetCells (next := next) order coordinate)).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample - increment
          *
        ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample) ≤
      4 * (ValueBlocks.factor (covered := covered) order coordinate +
        2 * errorScale (parent :: parents)) * Canonical.normSq increment ^ 2 := by
  have paid := (actual.atPrograms preparations programmes programme_cells index after order coordinate).remainder_le
  rewrite [← (actual.atPrograms preparations programmes programme_cells index after order coordinate).expansion,
    actual.atPrograms_base preparations programmes programme_cells index after order coordinate,
    actual.atPrograms_output preparations programmes programme_cells index after order coordinate,
    actual.atPrograms_slope preparations programmes programme_cells index after order coordinate,
    actual.atPrograms_factor preparations programmes programme_cells index after order coordinate] at paid
  exact paid

end ValueBlocks.Integral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
