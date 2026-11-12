module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
public import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip.Increment
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Programs
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Comparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Fin.Two
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Calculus.Jet.Quadratic.Chord
import Purelib.Approximation.AccuracyRequest.Scaling
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring

/-! # Finite parameter-derivative readings on independently acquired same-cycle programmes

One original four-row Global certificate pays the source readings. Both
independently retained shifted geometries refine the same original physical
parent spine. Common dyadic restrictions pay an actual target-programme
sample with its own global allocation. The result is the original quadratic
certificate on genuine programme samples, with a fixed-geometry factor and
a divided-difference error for the value-to-first and first-to-second rows.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Data
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
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

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))

namespace ValueBlocks

/-- The finite programme derivative factor computed solely from the original fixed covered geometry. -/
@[expose] def derivativeFactor (order coordinate : Fin 2) : Rational :=
  4 * (factor (covered := covered) order coordinate + 3 * errorScale (parent :: parents))

/-- The fixed original-geometry derivative factor is nonnegative, including constant physical parent cases. -/
theorem derivativeFactor_nonnegative (order coordinate : Fin 2) :
    0 ≤ derivativeFactor (covered := covered) order coordinate := by
  have positiveScales := Order.Arithmetic.add_le_add_direct
    (factor_nonnegative (covered := covered) order coordinate)
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 3)
      (errorScale_nonnegative (parent :: parents)))
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 4)
    ((Field.zero_add (0 : Rational)).symm.trans_le positiveScales)

/-- Adding one to the actual fixed derivative factor supplies a strictly positive request divisor. -/
private theorem derivativeDivisor_positive (order coordinate : Fin 2) :
    0 < derivativeFactor (covered := covered) order coordinate + 1 :=
  Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (derivativeFactor_nonnegative (covered := covered) order coordinate)
    (by decide +kernel : (0 : Rational) < 1)

/-- Compute the positive increment-quadrance request for a displayed derivative error tolerance.

The divisor is the original fixed-geometry factor plus one, so zero-factor
and constant-parent cases remain total. The independent original strip
admission still constrains the same actual increment and its root owners.
-/
def derivativeIncrementRequest (accuracy : AccuracyRequest) (order coordinate : Fin 2) : AccuracyRequest :=
  accuracy.divide (derivativeFactor (covered := covered) order coordinate + 1)
    (derivativeDivisor_positive (covered := covered) order coordinate)

/-- The increment request retains exactly the displayed tolerance divided by the actual fixed factor plus one. -/
theorem derivativeIncrementRequest_tolerance (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    (derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance =
      accuracy.tolerance / (derivativeFactor (covered := covered) order coordinate + 1) := by
  unfold derivativeIncrementRequest
  rfl

/-- Compute one positive quadrance request for all four derivative rows and the original common strip.

Each original row request is retained once before taking the finite minimum.
The original strip-allocation operation supplies the additional strip payment;
no source stage, target acquisition or query is executed by this operation.
-/
def derivativeRequest
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {ranges : ParameterRange covered}
    (allocation : ParameterRange.StripAllocation ranges) (accuracy : AccuracyRequest) : AccuracyRequest :=
  let valueZero := derivativeIncrementRequest (covered := covered) accuracy 0 0
  let valueOne := derivativeIncrementRequest (covered := covered) accuracy 0 1
  let firstZero := derivativeIncrementRequest (covered := covered) accuracy 1 0
  let firstOne := derivativeIncrementRequest (covered := covered) accuracy 1 1
  allocation.incrementRequest ((valueZero.minimum valueOne).minimum (firstZero.minimum firstOne))

/-- The same joint request pays the retained original strip allocation. -/
theorem derivativeRequest_le_bound
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {ranges : ParameterRange covered}
    (allocation : ParameterRange.StripAllocation ranges) (accuracy : AccuracyRequest) :
    (derivativeRequest allocation accuracy).tolerance ≤ allocation.bound := by
  unfold derivativeRequest
  exact allocation.incrementRequest_le_bound _

/-- Every original row request is paid by the same computed joint request. -/
theorem derivativeRequest_le_row
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {ranges : ParameterRange covered}
    (allocation : ParameterRange.StripAllocation ranges) (accuracy : AccuracyRequest)
    (order coordinate : Fin 2) :
    (derivativeRequest allocation accuracy).tolerance ≤
      (derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance := by
  let valueZero := derivativeIncrementRequest (covered := covered) accuracy 0 0
  let valueOne := derivativeIncrementRequest (covered := covered) accuracy 0 1
  let firstZero := derivativeIncrementRequest (covered := covered) accuracy 1 0
  let firstOne := derivativeIncrementRequest (covered := covered) accuracy 1 1
  have paid := allocation.incrementRequest_le_accuracy
    ((valueZero.minimum valueOne).minimum (firstZero.minimum firstOne))
  have valuePaid := paid.trans
    ((valueZero.minimum valueOne).minimum_le_left (firstZero.minimum firstOne))
  have firstPaid := paid.trans
    ((valueZero.minimum valueOne).minimum_le_right (firstZero.minimum firstOne))
  unfold derivativeRequest
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact Fin.cases (valuePaid.trans (valueZero.minimum_le_left valueOne))
      (Fin.cases (valuePaid.trans (valueZero.minimum_le_right valueOne))
        (fun index => Fin.elim0 index)) coordinate
  · exact Fin.cases (firstPaid.trans (firstZero.minimum_le_left firstOne))
      (Fin.cases (firstPaid.trans (firstZero.minimum_le_right firstOne))
        (fun index => Fin.elim0 index)) coordinate

/-- Any actual increment paying the joint request is admitted by the original common strip.

The admission is derived from the displayed smallness payment. The existing
`ranges.targetFrame` operation therefore constructs a regular frame at this
same arbitrary increment using `allocation.bound_le_regularBound`.
-/
theorem derivativeRequest_admitted
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {ranges : ParameterRange covered}
    (allocation : ParameterRange.StripAllocation ranges) (accuracy : AccuracyRequest)
    (increment : Canonical)
    (small : Norm.Basic.normSq increment ≤ (derivativeRequest allocation accuracy).tolerance) :
    Norm.Basic.normSq increment ≤ allocation.bound :=
  small.trans (derivativeRequest_le_bound allocation accuracy)

/-- Compute a nonzero parameter increment paying both this fixed-geometry derivative request and the original strip.

Only the original covered geometry, cached allocation and requested error
enter this construction. Source stages, acquired target child counts and
any eventual derivative comparison remain independent of the choice.
-/
@[expose] def requestedIncrement (accuracy : AccuracyRequest) (order coordinate : Fin 2) : Canonical :=
  allocation.increment (derivativeIncrementRequest (covered := covered) accuracy order coordinate)

/-- The actual derivative-request increment is nonzero, including zero-factor and constant-parent cases. -/
theorem requestedIncrement_nonzero (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    requestedIncrement (allocation := allocation) accuracy order coordinate ≠ 0 :=
  allocation.increment_nonzero (derivativeIncrementRequest (covered := covered) accuracy order coordinate)

/-- The computed derivative-request increment pays the SAME original strip and regularity allocation. -/
theorem requestedIncrement_admitted (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    Norm.Basic.normSq (requestedIncrement (allocation := allocation) accuracy order coordinate) ≤ allocation.bound :=
  allocation.increment_admitted (derivativeIncrementRequest (covered := covered) accuracy order coordinate)

/-- The computed increment also pays the exact displayed derivative-error request. -/
theorem requestedIncrement_accurate (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    Norm.Basic.normSq (requestedIncrement (allocation := allocation) accuracy order coordinate) ≤
      (derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance :=
  allocation.increment_accurate (derivativeIncrementRequest (covered := covered) accuracy order coordinate)

/-- Construct the original regular target frame at the SAME computed derivative-request increment. -/
def requestedFrame (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    Paths.Frame (parameter + requestedIncrement (allocation := allocation) accuracy order coordinate) :=
  allocation.incrementFrame (derivativeIncrementRequest (covered := covered) accuracy order coordinate)

end ValueBlocks

namespace ValueBlocks.Integral

variable (actual : Integral (next := firstNext) firstRetained)
    (completed : (index : Nat) → StageAttempt.Completed covered chain index firstSourceFloor firstSourceRootStage)
    (sourceIndex targetIndex : Nat)
    (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)

omit firstRetained lastRetained targetAfter in
/-- Both actual target allocations internally pay the displayed independent target programme against the stored output.

The common restriction cache reads the same original block Alignments and
both actual globally allocated source families. The second family is
constructed by its original programme callback once in this comparison;
its later-stage allowance and the first selected allowance each pay the
same parameter-fourth request. No final target or period equality is input.
-/
private theorem independent_target_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    (actual : Integral (next := firstNext) firstRetained) (targetIndex : Nat)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex) (order coordinate : Fin 2) :
    Norm.Basic.normSq
      ((((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample) - (actual.certificate (next := firstNext) (retained := firstRetained) order
          coordinate).output) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
  let firstPrepared := firstNext.requested.prepared
  let lastPrepared := lastNext.requested.request.attempt.preparationFamily targetIndex
  let lastTargets := CellEndpoints.Targets.build lastNext.requested.request.chain.path targetIndex
  let common := ValueBlocks.CommonRestrictions.build
    (firstNext := firstNext) (lastNext := lastNext) firstRetained lastRetained firstPrepared lastPrepared
  have compared := ValueBlocks.CommonRestrictions.integral_difference_le
    (firstNext := firstNext) (lastNext := lastNext) firstRetained lastRetained
    firstPrepared lastPrepared common (Specification.Table.baseIndex order coordinate)
  have firstSample : (actual.certificate (next := firstNext) (retained := firstRetained) order coordinate).output =
      (PathModel.mk ((PreparedParents.sources firstNext.requested.request.covered firstPrepared
        firstNext.requested.request.chain).cells (Specification.Table.baseIndex order coordinate))).integralSample :=
    (actual.output (next := firstNext) (retained := firstRetained) order coordinate).trans (congrArg (fun cells =>
      (PathModel.mk cells).integralSample)
      (ValueBlocks.targetCells_eq_sources (next := firstNext) order coordinate))
  have lastSample := lastRetained.targetProgram_sample
    (Specification.Table.baseIndex order coordinate) targetIndex
  have firstPaid : firstNext.requested.targets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    firstNext.requested.localBound_lt.le.trans
      (firstSpatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
  have lastPaid : lastTargets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    (lastNext.requested.targets.localBound_antitone lastTargets targetAfter).trans
      (lastNext.requested.localBound_lt.le.trans
        (lastSpatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero)))
  have geometryNonnegative : (0 : Rational) ≤ ((parent :: parents).length : Rational) *
      displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := (parent :: parents).length)
        (Nat.zero_le (parent :: parents).length))
      (displacementCost_nonnegative (parent :: parents))
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct firstPaid lastPaid)
      (show (0 : Rational) ≤ 16 by decide +kernel)) geometryNonnegative
  have scalar : 16 * (firstNext.requested.targets.localBound + lastTargets.localBound) *
      ((parent :: parents).length : Rational) * displacementCost (parent :: parents) ≤
      errorScale (parent :: parents) * Norm.Basic.normSq increment ^ 2 := by
    calc
      _ = (16 * (firstNext.requested.targets.localBound + lastTargets.localBound)) *
          (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := by ring1
      _ ≤ (16 * (Norm.Basic.normSq increment ^ 2 + Norm.Basic.normSq increment ^ 2)) *
          (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := scaled
      _ = _ := by unfold errorScale; ring1
  have samples := congrArg₂ (fun last first : Canonical => last - first) lastSample firstSample
  exact (congrArg Norm.Basic.normSq samples).trans_le
    ((Norm.Bounds.normSq_sub_symm _ _).trans_le (compared.trans scalar))

omit firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter in
/-- Arbitrary genuine fixed-source programmes obey the paid all-later divided-difference bound.

Only their original preparation and literal cell readbacks are inputs.
All three numerical discrepancies follow from the original independently
paid requests and common restrictions. The source programme family can
therefore remain fixed before the actual parameter increment is chosen.
-/
theorem sourcePrograms_differenceQuotient_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    (actual : Integral (next := firstNext) firstRetained)
    (preparations : (index : Nat) → PreparedParents covered firstSourceFloor
      (CellEndpoints.Targets.build chain.path index))
    (programmes : (channel : Fin 6) → CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (constantCycle chain))
    (programme_cells : ∀ channel index, ((programmes channel).integral.model index).cells =
      (PreparedParents.sources covered (preparations index) chain).cells channel)
    (sourceIndex targetIndex : Nat) (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex) (order coordinate : Fin 2) :
    Canonical.normSq
      ((((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) /
          increment -
        ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) ≤
      ValueBlocks.derivativeFactor (covered := covered) order coordinate * Canonical.normSq increment := by
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  let base := ((programmes (Specification.Table.baseIndex order coordinate)).integral.model
    sourceIndex).integralSample
  let output := ((lastRetained.targetProgram (next := lastNext)
    (Specification.Table.baseIndex order coordinate)).model targetIndex).integralSample
  let slope := ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
    sourceIndex).integralSample
  let retained := (actual.certificate (next := firstNext) (retained := firstRetained) order coordinate).perturb
    base output slope (errorScale (parent :: parents)) (errorScale (parent :: parents))
    (errorScale (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) (errorScale_nonnegative (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) unit
    (actual.program_base_difference_le (next := firstNext) (retained := firstRetained)
      preparations programmes programme_cells sourceIndex sourceAfter order coordinate)
    (independent_target_difference_le firstRetained lastRetained actual targetIndex targetAfter order coordinate)
    (actual.program_slope_difference_le (next := firstNext) (retained := firstRetained)
      preparations programmes programme_cells sourceIndex sourceAfter order coordinate)
  have quotient := retained.differenceQuotient_le nonzero
  change Canonical.normSq ((output - base) / increment - slope) ≤
    4 * ((actual.certificate (next := firstNext) (retained := firstRetained) order coordinate).factor +
      errorScale (parent :: parents) + errorScale (parent :: parents) + errorScale (parent :: parents)) *
        Canonical.normSq increment at quotient
  have factor := congrArg (fun value : Rational =>
    4 * (value + errorScale (parent :: parents) + errorScale (parent :: parents) + errorScale (parent :: parents)))
    (actual.factor_eq (next := firstNext) (retained := firstRetained) order coordinate)
  have scalar : 4 * (ValueBlocks.factor (covered := covered) order coordinate +
      errorScale (parent :: parents) + errorScale (parent :: parents) + errorScale (parent :: parents)) =
      ValueBlocks.derivativeFactor (covered := covered) order coordinate := by
    unfold ValueBlocks.derivativeFactor
    ring1
  exact quotient.trans_eq (congrArg (fun value : Rational => value * Canonical.normSq increment)
    (factor.trans scalar))

include firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter

/-- Construct one adjacent-derivative certificate on actual independent source and target programme samples.

The original source programmes consume the SAME actual completed Stage
family and its exact retained source-list readbacks. Its Commons/admissions
are genuine finite geometric inputs, not a desired jet or period equality. The
independent target programme retains its own acquired geometry, global
allocation and source callbacks. All three discrepancy payments are derived
from those original owners; no derivative, period equality or Taylor bound
is supplied by the caller.
-/
def atIndependentPrograms (order coordinate : Fin 2) : Quadratic.Basic.Certificate increment := by
  let preparations := fun index => (completed index).1.preparations
  let programmes := StageAttempt.staged (frame := frame) covered chain completed
  have cells (channel : Fin 6) (index : Nat) :
      ((programmes channel).integral.model index).cells =
        (PreparedParents.sources covered (preparations index) chain).cells channel :=
    (StageAttempt.staged_cells covered chain completed channel index).trans
      (congrArg (fun sources => sources.cells channel)
        (StageAttempt.Completion.stage_sources (completed index).1 (completed index).2))
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  exact (actual.certificate (next := firstNext) (retained := firstRetained) order coordinate).perturb
    (((programmes (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample)
    (((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
      targetIndex).integralSample)
    (((programmes (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample)
    (errorScale (parent :: parents)) (errorScale (parent :: parents)) (errorScale (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) (errorScale_nonnegative (parent :: parents))
    (errorScale_nonnegative (parent :: parents)) unit
    (actual.program_base_difference_le (next := firstNext) (retained := firstRetained) preparations programmes cells
      sourceIndex sourceAfter order coordinate)
    (independent_target_difference_le firstRetained lastRetained actual targetIndex targetAfter order coordinate)
    (actual.program_slope_difference_le (next := firstNext) (retained := firstRetained) preparations programmes
      cells sourceIndex sourceAfter order coordinate)

/-- The base is the actual original source value/first programme sample at its retained independent source index. -/
theorem atIndependentPrograms_base (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).base =
      ((StageAttempt.staged (frame := frame) covered chain completed
        (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample := by
  unfold atIndependentPrograms
  rfl

/-- The output is the actual independent same-cycle target value/first programme sample at its original index. -/
theorem atIndependentPrograms_output (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).output =
      ((lastRetained.targetProgram (next := lastNext)
        (Specification.Table.baseIndex order coordinate)).model targetIndex).integralSample := by
  unfold atIndependentPrograms
  rfl

/-- The slope is the independently evaluated original first/second source programme sample on the same source cycle. -/
theorem atIndependentPrograms_slope (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).slope =
      ((StageAttempt.staged (frame := frame) covered chain completed
        (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample := by
  unfold atIndependentPrograms
  rfl

/-- The retained base reading is the corresponding actual field of the original source jet.

Only original whole-integral readbacks and the existing two-order selector
are used. The jet, completed Stage family and independent programme
readings retain their original owners; no period comparison is supplied.
-/
theorem atIndependentPrograms_base_channel (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).base =
      ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
        (((StageAttempt.jet covered chain completed).value coordinate).integral)
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
          (((StageAttempt.jet covered chain completed).first coordinate).integral)
          (fun index => Fin.elim0 index)) order).model sourceIndex).integralSample := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · have displayed := atIndependentPrograms_base firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 0 coordinate
    have original := StageAttempt.jet_value_integral covered chain completed coordinate
    exact displayed.trans (congrArg
      (fun programme : RefinementProgram => (programme.model sourceIndex).integralSample) original.symm)
  · have displayed := atIndependentPrograms_base firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 1 coordinate
    have original := StageAttempt.jet_first_integral covered chain completed coordinate
    exact displayed.trans (congrArg
      (fun programme : RefinementProgram => (programme.model sourceIndex).integralSample) original.symm)

/-- The retained slope reading is the corresponding actual field of the original source jet.

Only original whole-integral readbacks and the existing two-order selector
are used. The jet, completed Stage family and independent programme
readings retain their original owners; no period comparison is supplied.
-/
theorem atIndependentPrograms_slope_channel (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).slope =
      ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
        (((StageAttempt.jet covered chain completed).first coordinate).integral)
        (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
          (((StageAttempt.jet covered chain completed).second coordinate).integral)
          (fun index => Fin.elim0 index)) order).model sourceIndex).integralSample := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · have displayed := atIndependentPrograms_slope firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 0 coordinate
    have original := StageAttempt.jet_first_integral covered chain completed coordinate
    exact displayed.trans (congrArg
      (fun programme : RefinementProgram => (programme.model sourceIndex).integralSample) original.symm)
  · have displayed := atIndependentPrograms_slope firstRetained lastRetained actual completed
      sourceIndex targetIndex sourceAfter targetAfter 1 coordinate
    have original := StageAttempt.jet_second_integral covered chain completed coordinate
    exact displayed.trans (congrArg
      (fun programme : RefinementProgram => (programme.model sourceIndex).integralSample) original.symm)

/-- The computed factor uses only the original fixed patches, parent count and physical displacement costs. -/
theorem atIndependentPrograms_factor (order coordinate : Fin 2) :
    (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).factor =
      ValueBlocks.derivativeFactor (covered := covered) order coordinate := by
  unfold atIndependentPrograms
  unfold ValueBlocks.derivativeFactor
  change 4 * ((actual.certificate (next := firstNext) (retained := firstRetained) order coordinate).factor +
    errorScale (parent :: parents) +
    errorScale (parent :: parents) + errorScale (parent :: parents)) = _
  exact (congrArg (fun factor : Rational =>
    4 * (factor + errorScale (parent :: parents) + errorScale (parent :: parents) + errorScale (parent :: parents)))
      (actual.factor_eq (next := firstNext) (retained := firstRetained) order coordinate)).trans (by ring1)

/-- The actual programme first difference has a fixed-geometry quadrance error tending to zero with increment quadrance.

Order zero compares the value programme with its original first channel;
order one compares the first programme with its original second channel.
Both differential coordinates use this single constructor and their exact
six-form indices. Its bound is uniform in both source/target stages and
both adaptive acquired child counts.
-/
theorem differenceQuotient_le (order coordinate : Fin 2) :
    Canonical.normSq
      ((((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) /
          increment -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) ≤
      ValueBlocks.derivativeFactor (covered := covered) order coordinate *
        Canonical.normSq increment := by
  have output := atIndependentPrograms_output firstRetained lastRetained actual completed
    sourceIndex targetIndex sourceAfter targetAfter order coordinate
  have base := atIndependentPrograms_base firstRetained lastRetained actual completed
    sourceIndex targetIndex sourceAfter targetAfter order coordinate
  have slope := atIndependentPrograms_slope firstRetained lastRetained actual completed
    sourceIndex targetIndex sourceAfter targetAfter order coordinate
  have factor := atIndependentPrograms_factor firstRetained lastRetained actual completed
    sourceIndex targetIndex sourceAfter targetAfter order coordinate
  have difference := congrArg₂ (fun output base : Canonical => (output - base) / increment) output base
  have reading := congrArg₂ (fun difference slope : Canonical => difference - slope) difference slope
  have bound := (atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate).differenceQuotient_le nonzero
  exact (congrArg Canonical.normSq reading).symm.trans_le
    (bound.trans_eq (congrArg (fun factor : Rational => factor * Canonical.normSq increment) factor))

/-- The computed positive increment request pays the actual same-cycle first/second channel comparison.

The only extra condition is the actual increment's quadrance payment to
the explicitly computed request. It is not a derivative or period
comparison. Both programme samples keep their original owners and stages;
the original admitted strip and independently paid spatial requests remain
in the constructor indices.
-/
theorem differenceQuotient_lt (accuracy : AccuracyRequest) (order coordinate : Fin 2)
    (small : Norm.Basic.normSq increment ≤
      (ValueBlocks.derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance) :
    Canonical.normSq
      ((((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) /
          increment -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) <
      accuracy.tolerance := by
  have smallCanonical := (Norm.Basic.normSq_eq_canonical increment).symm.trans_le small
  have paid := (Order.Field.le_div_iff_pos
    (ValueBlocks.derivativeDivisor_positive (covered := covered) order coordinate)).mp
      (smallCanonical.trans_eq
        (ValueBlocks.derivativeIncrementRequest_tolerance (covered := covered) accuracy order coordinate))
  have positive : (0 : Rational) < Canonical.normSq increment :=
    (Norm.Basic.normSq_pos nonzero).trans_eq (Norm.Basic.normSq_eq_canonical increment)
  let factor := ValueBlocks.derivativeFactor (covered := covered) order coordinate
  have strict : factor * Canonical.normSq increment <
      Canonical.normSq increment * (factor + 1) :=
    (show factor * Canonical.normSq increment = factor * Canonical.normSq increment + 0 by ring1).trans_lt
      ((Order.Arithmetic.add_lt_add_left_direct positive (factor * Canonical.normSq increment)).trans_eq
        (by ring1))
  exact (differenceQuotient_le firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate).trans_lt (strict.trans_le paid)

/-- Retain the finite derivative certificate beside the internally derived comparison of both original target outputs.

The operational comparison preserves its two actual programme owners and
selected tail indices. It does not identify different parameter fibres or
replace the finite certificate's actual independent target sample.
-/
def withTargetAgreement (order coordinate : Fin 2) :
    Quadratic.Basic.Certificate increment ×
      NamedEquivalent (firstRetained.targetProgram (next := firstNext) (Specification.Table.baseIndex order
        coordinate)).output.name
        (lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).output.name :=
  let retained := atIndependentPrograms firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate
  let agreement := ValueBlocks.targetOutputs_equivalent (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained
    (Specification.Table.baseIndex order coordinate)
  ⟨retained, agreement⟩

/-- Construct the original source jet/relation certificates beside its finite same-cycle derivative evidence.

The completed Stage family supplies the original six staged programme
owners and source attachment. The existing build/ofJet operations derive
connection and scalar-residual comparisons internally. Their finite
algebraic relations are kept separate from the new parameter-Taylor
certificate and independent target-programme equivalence.
-/
def withRelations (order coordinate : Fin 2) :
    (sourceJet : SynchronizedPeriodJet frame) ×
      Connection.ConnectionCertificate sourceJet × PicardFuchs.PicardFuchsCertificate sourceJet ×
        (Quadratic.Basic.Certificate increment ×
          NamedEquivalent
            (firstRetained.targetProgram (next := firstNext)
              (Specification.Table.baseIndex order coordinate)).output.name
            (lastRetained.targetProgram (next := lastNext)
              (Specification.Table.baseIndex order coordinate)).output.name) :=
  let relations := StageAttempt.build covered chain completed
  let derivative := withTargetAgreement firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate
  ⟨relations.1, relations.2.1, relations.2.2, derivative⟩

/-- The returned source jet is the original ofSource construction on the SAME retained completed Stage family. -/
theorem withRelations_jet (order coordinate : Fin 2) :
    (withRelations firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).1 = StageAttempt.jet covered chain completed := by
  unfold withRelations
  exact StageAttempt.build_jet covered chain completed

omit firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter in
/-- One fixed positive request controls every row at every later pair on each admissible nonzero increment.

The original geometry, allocation, requested error and requested starts are
fixed before the increment. Its smallness payment derives admission inside
the actual shifted-owner indices. The two maximum floors retain the original
selected stages and both requested starts. All four conclusions use the same
actual acquired caches and source completion family; this operation executes
no preparation or source query.
-/
theorem differenceQuotient_uniform_lt
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    (accuracy : AccuracyRequest) (sourceStart targetStart : Nat)
    (increment : Canonical) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤ (ValueBlocks.derivativeRequest allocation accuracy).tolerance)
    {target : Paths.Frame (parameter + increment)}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {firstSpatial lastSpatial : AccuracyRequest}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation
      (ValueBlocks.derivativeRequest_admitted allocation accuracy increment small)
      firstWidths roots firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation
      (ValueBlocks.derivativeRequest_admitted allocation accuracy increment small)
      lastWidths roots lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    (actual : Integral (next := firstNext) firstRetained)
    (completed : (index : Nat) → StageAttempt.Completed covered chain index firstSourceFloor firstSourceRootStage) :
    ∀ sourceLater targetLater,
      Nat.max sourceStart firstSource.selected.stage ≤ sourceLater →
      Nat.max targetStart lastNext.requested.selected.stage ≤ targetLater →
      ∀ order coordinate : Fin 2,
        Canonical.normSq
          ((((lastRetained.targetProgram (next := lastNext)
            (Specification.Table.baseIndex order coordinate)).model targetLater).integralSample -
            ((StageAttempt.staged (frame := frame) covered chain completed
              (Specification.Table.baseIndex order coordinate)).integral.model sourceLater).integralSample) /
              increment -
            ((StageAttempt.staged (frame := frame) covered chain completed
              (Specification.Table.slopeIndex order coordinate)).integral.model sourceLater).integralSample) <
          accuracy.tolerance := by
  intro sourceLater targetLater sourceAfter targetAfter order coordinate
  exact differenceQuotient_lt (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceLater targetLater
    ((Nat.Order.le_max_right sourceStart firstSource.selected.stage).trans sourceAfter)
    ((Nat.Order.le_max_right targetStart lastNext.requested.selected.stage).trans targetAfter)
    accuracy order coordinate
    (small.trans (ValueBlocks.derivativeRequest_le_row allocation accuracy order coordinate))

end ValueBlocks.Integral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
