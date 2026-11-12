module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Programs
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Calculus.Jet.Quadratic.Chord
import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Paid independent target readings on the retained global Taylor output

The actual target cover, local-to-global positions and original widths
remain fixed. Independent preparation floors pay a new target reading
against the already stored selected output. Positional source completions
supply the original six programme readbacks, without legacy readiness.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Riemann.Topology

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
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

namespace ValueBlocks

/-- The new actual target cache and the stored selected cache pay their own fourth-order allowances.

The original retained widths and positions remove every adaptive child
count. The old allowance is already paid by next.requested; the supplied
finite search is the original selection data for the new allocation.
-/
theorem independent_target_payment_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage)) (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources next.requested.request.covered prepared
        next.requested.request.chain).cells channel)).integralSample -
        (PathModel.mk ((sources next.requested.request.covered next.requested.prepared
          next.requested.request.chain).cells channel)).integralSample) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
  let newTargets := CellEndpoints.Targets.build next.requested.request.chain.path selected.stage
  have firstPaid : newTargets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    newTargets.localBound_le_quarterRadius.trans
      (selected.later_accurate (Nat.le_refl _)).le
  have lastPaid : next.requested.targets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    next.requested.localBound_lt.le.trans
      (spatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
  have allowance := (Order.Arithmetic.add_le_add_direct firstPaid lastPaid).trans_eq
    (show Norm.Basic.normSq increment ^ 2 + Norm.Basic.normSq increment ^ 2 =
      2 * Norm.Basic.normSq increment ^ 2 by ring1)
  have geometry : 0 ≤ ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := (parent :: parents).length) (Nat.zero_le _))
      (displacementCost_nonnegative (parent :: parents))
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowance (by decide +kernel : (0 : Rational) ≤ 16))
    geometry
  have original := retained.independent_target_difference_le prepared next.requested.prepared channel
  calc
    _ ≤ 16 * (newTargets.localBound + next.requested.targets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := original
    _ = (16 * (newTargets.localBound + next.requested.targets.localBound)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := by ring1
    _ ≤ (16 * (2 * Norm.Basic.normSq increment ^ 2)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := scaled
    _ = errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by unfold errorScale; ring1

end ValueBlocks

namespace ValueBlocks.Integral

/-- The independent target sample pays against this same atPrograms certificate's unchanged computed output. -/
theorem independent_target_difference_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (preparations : (index : Nat) →
      PreparedParents covered sourceFloor (CellEndpoints.Targets.build chain.path index))
    (programmes : (channel : Fin 6) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (constantCycle chain))
    (programme_cells : ∀ channel index, ((programmes channel).integral.model index).cells =
      (sources covered (preparations index) chain).cells channel)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage)) (order coordinate : Fin 2) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
        (actual.atPrograms preparations programmes programme_cells index after order coordinate).output) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
  have output := (actual.atPrograms_output preparations programmes programme_cells index after order coordinate).trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample)
      (targetCells_eq_sources (next := next) order coordinate))
  have difference := congrArg (fun sample : Canonical => Norm.Basic.normSq
    ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
      (Specification.Table.baseIndex order coordinate))).integralSample - sample)) output
  exact difference.trans_le
    (retained.independent_target_payment_le selected prepared (Specification.Table.baseIndex order coordinate))

/-- The supplied independent target cache obeys the original atPrograms remainder with its internally paid factor.

The atPrograms certificate is used only inside this proposition-valued
proof. Its unchanged output is the actual Global comparison anchor; this
operation makes no new runtime source-callback or acquisition claim.
-/
theorem atTargetPrepared_remainder_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (preparations : (index : Nat) →
      PreparedParents covered sourceFloor (CellEndpoints.Targets.build chain.path index))
    (programmes : (channel : Fin 6) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (constantCycle chain))
    (programme_cells : ∀ channel index, ((programmes channel).integral.model index).cells =
      (sources covered (preparations index) chain).cells channel)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage)) (order coordinate : Fin 2) :
    Canonical.normSq
      ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample -
        increment * ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
          index).integralSample) ≤
      4 * (4 * (ValueBlocks.factor (covered := covered) order coordinate + 2 * errorScale (parent :: parents)) +
        errorScale (parent :: parents)) * Canonical.normSq increment ^ 2 := by
  let original := actual.atPrograms preparations programmes programme_cells index after order coordinate
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  have unchangedBase : Norm.Basic.normSq (original.base - original.base) ≤
      0 * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero, Field.zero_mul_direct]
    exact Order.Basic.le_refl 0
  have unchangedSlope : Norm.Basic.normSq (original.slope - original.slope) ≤
      0 * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero, Field.zero_mul_direct]
    exact Order.Basic.le_refl 0
  have bound := original.perturbation_bound original.base
    (PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
      (Specification.Table.baseIndex order coordinate))).integralSample original.slope
    0 (errorScale (parent :: parents)) 0 unit unchangedBase
    (actual.independent_target_difference_le preparations programmes programme_cells index after
      selected prepared order coordinate) unchangedSlope
  have base := actual.atPrograms_base preparations programmes programme_cells index after order coordinate
  have slope := actual.atPrograms_slope preparations programmes programme_cells index after order coordinate
  have factor := actual.atPrograms_factor preparations programmes programme_cells index after order coordinate
  have residual := congrArg₂ (fun base slope : Canonical =>
    (PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
      (Specification.Table.baseIndex order coordinate))).integralSample - base - increment * slope) base slope
  have bounded := (congrArg Norm.Basic.normSq residual).symm.trans_le bound
  have norm := Norm.Basic.normSq_eq_canonical
    ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
      (Specification.Table.baseIndex order coordinate))).integralSample -
      ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample -
      increment * ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample)
  have canonical := norm.symm.trans_le bounded
  have scale := congrArg₂ (fun factor quadrance : Rational =>
    4 * (factor + 0 + errorScale (parent :: parents) + 0) * quadrance ^ 2)
      factor (Norm.Basic.normSq_eq_canonical increment)
  have paid := canonical.trans_eq scale
  exact paid.trans_eq (by ring1)

/-- A genuine whole target-programme cell readback transports the paid target cache remainder to its actual sample. -/
theorem atTargetProgramme_remainder_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (preparations : (index : Nat) →
      PreparedParents covered sourceFloor (CellEndpoints.Targets.build chain.path index))
    (programmes : (channel : Fin 6) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (constantCycle chain))
    (programme_cells : ∀ channel index, ((programmes channel).integral.model index).cells =
      (sources covered (preparations index) chain).cells channel)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage)) (order coordinate : Fin 2)
    (programme : CertifiedPeriodProgram (Fibre.frameCurve target)
      (Specification.Table.forms (parameter + increment) (Specification.Table.baseIndex order coordinate))
      (constantCycle next.requested.request.chain))
    (cells : (programme.integral.model selected.stage).cells =
      (sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate)) :
    Canonical.normSq
      ((programme.integral.model selected.stage).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample -
        increment * ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
          index).integralSample) ≤
      4 * (4 * (ValueBlocks.factor (covered := covered) order coordinate + 2 * errorScale (parent :: parents)) +
        errorScale (parent :: parents)) * Canonical.normSq increment ^ 2 := by
  have sample := congrArg (fun cells => (PathModel.mk cells).integralSample) cells
  exact Eq.mpr (congrArg (fun reading : Canonical => Canonical.normSq
    (reading - ((programmes (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample -
      increment * ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
        index).integralSample) ≤
      4 * (4 * (ValueBlocks.factor (covered := covered) order coordinate + 2 * errorScale (parent :: parents)) +
        errorScale (parent :: parents)) * Canonical.normSq increment ^ 2) sample)
    (actual.atTargetPrepared_remainder_le preparations programmes programme_cells index after
      selected prepared order coordinate)

end ValueBlocks.Integral

namespace ValueBlocks.Integral

/-- The actual whole positional member identifies its original programme sample without a new preparation. -/
private theorem occurrence_sample_eq
    {parameter : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {sourceFloor sourceRootStage : Nat}
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (channel : Fin 6) :
    (((StageAttempt.OccurrenceCompletion.staged covered chain completed channel).integral.model
      index).integralSample) =
      (PathModel.mk ((sources covered cached.1.preparations chain).cells channel)).integralSample := by
  have original := StageAttempt.OccurrenceCompletion.staged_cells covered chain completed channel index
  have same := congrArg
    (fun value : (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain index sourceFloor sourceRootStage) × StageAttempt.OccurrenceCompletion attempt =>
      value.2.stage.sources.cells channel) member.symm
  have cells := original.trans (same.trans
    (congrArg (fun value => value.cells channel)
      (cached.2.stage_sources.trans cached.1.preparations_sources.symm)))
  exact congrArg (fun cells => (PathModel.mk cells).integralSample) cells

/-- Assemble the independent readings from the actual retained positional source and target caches.

The whole source-member equation authenticates the original preparation and
Stage together. Programme evaluations occur only in erased comparison
proofs. Executable base, output and slope fields read the supplied caches;
no callback, preparation, acquisition or old Global producer is executed.
-/
def atOccurrenceTargetPrepared
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) : Quadratic.Basic.Certificate increment := by
  let preparations := fun stage => (completed stage).1.preparations
  let programmes := StageAttempt.OccurrenceCompletion.staged covered chain completed
  have cells : ∀ channel stage, ((programmes channel).integral.model stage).cells =
      (sources covered (preparations stage) chain).cells channel := fun channel stage =>
    (StageAttempt.OccurrenceCompletion.staged_cells covered chain completed channel stage).trans
      (congrArg (fun original => original.cells channel)
        ((completed stage).2.stage_sources.trans (completed stage).1.preparations_sources.symm))
  let base := (PathModel.mk ((sources covered cached.1.preparations chain).cells
    (Specification.Table.baseIndex order coordinate))).integralSample
  let output := (PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
    (Specification.Table.baseIndex order coordinate))).integralSample
  let slope := (PathModel.mk ((sources covered cached.1.preparations chain).cells
    (Specification.Table.slopeIndex order coordinate))).integralSample
  have baseBound : Norm.Basic.normSq (base - (actual.certificate order coordinate).base) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 :=
    (congrArg (fun reading => Norm.Basic.normSq (reading - (actual.certificate order coordinate).base))
      (occurrence_sample_eq completed index cached member
        (Specification.Table.baseIndex order coordinate))).symm.trans_le
        (actual.program_base_difference_le preparations programmes cells index after order coordinate)
  have slopeBound : Norm.Basic.normSq (slope - (actual.certificate order coordinate).slope) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 :=
    (congrArg (fun reading => Norm.Basic.normSq (reading - (actual.certificate order coordinate).slope))
      (occurrence_sample_eq completed index cached member
        (Specification.Table.slopeIndex order coordinate))).symm.trans_le
          (actual.program_slope_difference_le preparations programmes cells index after order coordinate)
  have oldOutput := (actual.output order coordinate).trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample)
      (targetCells_eq_sources (next := next) order coordinate))
  have outputBound : Norm.Basic.normSq (output - (actual.certificate order coordinate).output) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 :=
    (congrArg (fun reading => Norm.Basic.normSq (output - reading)) oldOutput).trans_le
      (retained.independent_target_payment_le selected prepared (Specification.Table.baseIndex order coordinate))
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  exact (actual.certificate order coordinate).perturb base output slope
    (errorScale (parent :: parents)) (errorScale (parent :: parents)) (errorScale (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) (errorScale_nonnegative (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) unit baseBound outputBound slopeBound

/-- The actual cache-only certificate has the directly computed original-geometry factor. -/
private theorem packaged_atOccurrenceTargetPrepared_factor
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).factor =
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3 * errorScale (parent :: parents)) := by
  unfold atOccurrenceTargetPrepared
  change 4 * ((actual.certificate order coordinate).factor + errorScale (parent :: parents) +
    errorScale (parent :: parents) + errorScale (parent :: parents)) = _
  rewrite [actual.factor_eq order coordinate]
  ring1

/-- The actual cache-only certificate has the directly computed original-geometry factor. -/
theorem atOccurrenceTargetPrepared_factor
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).factor =
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3 * errorScale (parent :: parents)) :=
  packaged_atOccurrenceTargetPrepared_factor actual completed index after selected prepared
    cached member order coordinate

/-- The cache-only certificate reads its SAME actual positional base cell list. -/
private theorem packaged_atOccurrenceTargetPrepared_base
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).base =
      (PathModel.mk ((sources covered cached.1.preparations chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample := by
  unfold atOccurrenceTargetPrepared
  rfl

/-- The cache-only certificate reads its SAME actual positional base cell list. -/
theorem atOccurrenceTargetPrepared_base
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).base =
      (PathModel.mk ((sources covered cached.1.preparations chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample :=
  packaged_atOccurrenceTargetPrepared_base actual completed index after selected prepared
    cached member order coordinate

/-- The cache-only certificate reads the supplied whole independent target preparation. -/
private theorem packaged_atOccurrenceTargetPrepared_output
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).output =
      (PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample := by
  unfold atOccurrenceTargetPrepared
  rfl

/-- The cache-only certificate reads the supplied whole independent target preparation. -/
theorem atOccurrenceTargetPrepared_output
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).output =
      (PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample :=
  packaged_atOccurrenceTargetPrepared_output actual completed index after selected prepared
    cached member order coordinate

/-- The cache-only certificate reads its SAME actual positional derivative cell list. -/
private theorem packaged_atOccurrenceTargetPrepared_slope
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).slope =
      (PathModel.mk ((sources covered cached.1.preparations chain).cells
        (Specification.Table.slopeIndex order coordinate))).integralSample := by
  unfold atOccurrenceTargetPrepared
  rfl

/-- The cache-only certificate reads its SAME actual positional derivative cell list. -/
theorem atOccurrenceTargetPrepared_slope
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    (actual.atOccurrenceTargetPrepared completed index after selected prepared cached member order coordinate).slope =
      (PathModel.mk ((sources covered cached.1.preparations chain).cells
        (Specification.Table.slopeIndex order coordinate))).integralSample :=
  packaged_atOccurrenceTargetPrepared_slope actual completed index after selected prepared
    cached member order coordinate

/-- The actual cached source and target readings have a fourth-order remainder with no adaptive-child-count factor. -/
theorem cached_target_remainder_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    Canonical.normSq
      ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
        (PathModel.mk ((sources covered cached.1.preparations chain).cells
          (Specification.Table.baseIndex order coordinate))).integralSample -
        increment * (PathModel.mk ((sources covered cached.1.preparations chain).cells
          (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3 * errorScale (parent :: parents)) *
        Canonical.normSq increment ^ 2 := by
  let original := actual.atOccurrenceTargetPrepared completed index after selected prepared
    cached member order coordinate
  have base := actual.atOccurrenceTargetPrepared_base completed index after selected prepared
    cached member order coordinate
  have output := actual.atOccurrenceTargetPrepared_output completed index after selected prepared
    cached member order coordinate
  have slope := actual.atOccurrenceTargetPrepared_slope completed index after selected prepared
    cached member order coordinate
  have factor := actual.atOccurrenceTargetPrepared_factor completed index after selected prepared
    cached member order coordinate
  have readings := congrArg₂ (fun difference slope : Canonical => difference - increment * slope)
    (congrArg₂ (fun output base : Canonical => output - base) output base) slope
  have expansion := readings.symm.trans original.expansion
  have bounded := (congrArg Canonical.normSq expansion).trans_le original.remainder_le
  exact bounded.trans_eq (congrArg (fun factor : Rational =>
    factor * Canonical.normSq increment ^ 2) factor)

/-- The SAME retained readings have the finite quotient error obtained by dividing the paid remainder. -/
theorem cached_target_differenceQuotient_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (cached : (attempt : StageAttempt (parameter := parameter) (frame := frame)
      covered chain index sourceFloor sourceRootStage) ×
      StageAttempt.OccurrenceCompletion attempt)
    (member : cached = completed index) (order coordinate : Fin 2) :
    Canonical.normSq
      (((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
        (PathModel.mk ((sources covered cached.1.preparations chain).cells
          (Specification.Table.baseIndex order coordinate))).integralSample) / increment -
        (PathModel.mk ((sources covered cached.1.preparations chain).cells
          (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      4 * (ValueBlocks.factor (covered := covered) order coordinate + 3 * errorScale (parent :: parents)) *
        Canonical.normSq increment := by
  have paid := (actual.atOccurrenceTargetPrepared completed index after selected prepared
    cached member order coordinate).differenceQuotient_le nonzero
  have base := actual.atOccurrenceTargetPrepared_base completed index after selected prepared
    cached member order coordinate
  have output := actual.atOccurrenceTargetPrepared_output completed index after selected prepared
    cached member order coordinate
  have slope := actual.atOccurrenceTargetPrepared_slope completed index after selected prepared
    cached member order coordinate
  have factor := actual.atOccurrenceTargetPrepared_factor completed index after selected prepared
    cached member order coordinate
  have readings := congrArg₂ (fun difference slope : Canonical => difference / increment - slope)
    (congrArg₂ (fun output base : Canonical => output - base) output base) slope
  have bounded := (congrArg Canonical.normSq readings).symm.trans_le paid
  exact bounded.trans_eq (congrArg (fun factor : Rational =>
    factor * Canonical.normSq increment) factor)

/-- Genuine positional Stage programme samples obey the finite paid target remainder on this same cycle.

Every source-cell equality is derived from the supplied original completion
and its preparation cache. The width-weighted target estimate and both
source payments are internal; no final channel estimate is an input.
-/
theorem occurrence_target_remainder_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage)) (order coordinate : Fin 2) :
    Canonical.normSq
      ((PathModel.mk ((sources next.requested.request.covered prepared next.requested.request.chain).cells
        (Specification.Table.baseIndex order coordinate))).integralSample -
        (((StageAttempt.OccurrenceCompletion.staged covered chain completed
          (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample) -
        increment * (((StageAttempt.OccurrenceCompletion.staged covered chain completed
          (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample)) ≤
      4 * (4 * (ValueBlocks.factor (covered := covered) order coordinate + 2 * errorScale (parent :: parents)) +
        errorScale (parent :: parents)) * Canonical.normSq increment ^ 2 :=
  actual.atTargetPrepared_remainder_le (fun stage => (completed stage).1.preparations)
    (StageAttempt.OccurrenceCompletion.staged covered chain completed)
    (fun channel stage =>
      (StageAttempt.OccurrenceCompletion.staged_cells covered chain completed channel stage).trans
        (congrArg (fun original => original.cells channel)
        ((completed stage).2.stage_sources.trans (completed stage).1.preparations_sources.symm)))
    index after selected prepared order coordinate

/-- The actual independently certified target programme obeys the internally paid positional-source remainder.

The supplied target cache is the same actual member of independent, as
certified by its whole member equality. The original certified_cells and
positional Stage laws derive the two programme readbacks. Both independent
preparation floors, the stored Global output and the physical cycle remain.
-/
theorem occurrence_certifiedTarget_remainder_le
    {parameter increment : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)}
    {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered}
    {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named}
    {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest}
    {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)}
    (actual : Integral retained)
    (completed : (stage : Nat) →
      (attempt : StageAttempt (parameter := parameter) (frame := frame)
        covered chain stage sourceFloor sourceRootStage) ×
        StageAttempt.OccurrenceCompletion attempt)
    (index : Nat)
    (after : source.selected.stage ≤ index)
    {independentFloor start : Nat}
    (selected : Geometric.Search.Selection 1 start
      (Variation.Sampling.incrementRequest increment nonzero).tolerance)
    (prepared : PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path selected.stage))
    (independent : (stage : Nat) → PreparedParents (parameter := parameter + increment) (frame := target)
      next.requested.request.covered independentFloor
      (CellEndpoints.Targets.build next.requested.request.chain.path stage))
    (member : prepared = independent selected.stage) (order coordinate : Fin 2) :
    Canonical.normSq
      ((((certified (parameter := parameter + increment) (frame := target) next.requested.request.covered
        next.requested.request.chain independent (Specification.Table.baseIndex order coordinate)).integral.model
          selected.stage).integralSample) -
        (((StageAttempt.OccurrenceCompletion.staged covered chain completed
          (Specification.Table.baseIndex order coordinate)).integral.model index).integralSample) -
        increment * (((StageAttempt.OccurrenceCompletion.staged covered chain completed
          (Specification.Table.slopeIndex order coordinate)).integral.model index).integralSample)) ≤
      4 * (4 * (ValueBlocks.factor (covered := covered) order coordinate + 2 * errorScale (parent :: parents)) +
        errorScale (parent :: parents)) * Canonical.normSq increment ^ 2 := by
  have cells := (certified_cells (parameter := parameter + increment) (frame := target)
    next.requested.request.covered next.requested.request.chain independent
    (Specification.Table.baseIndex order coordinate) selected.stage).trans
      (congrArg (fun value => (sources next.requested.request.covered value
        next.requested.request.chain).cells (Specification.Table.baseIndex order coordinate)) member.symm)
  exact actual.atTargetProgramme_remainder_le (fun stage => (completed stage).1.preparations)
    (StageAttempt.OccurrenceCompletion.staged covered chain completed)
    (fun channel stage =>
      (StageAttempt.OccurrenceCompletion.staged_cells covered chain completed channel stage).trans
        (congrArg (fun original => original.cells channel)
        ((completed stage).2.stage_sources.trans (completed stage).1.preparations_sources.symm)))
    index after selected prepared order coordinate
    (certified (parameter := parameter + increment) (frame := target) next.requested.request.covered
      next.requested.request.chain independent (Specification.Table.baseIndex order coordinate)) cells

end ValueBlocks.Integral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
