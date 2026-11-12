module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # All-later parameter differences on one fixed positional source family

The source programmes are fixed before the increment. Each actual nonzero
increment has its own fourth-order numerical requests and selected floors.
The finite Taylor certificate then pays every later source/target pair on
the same original physical spine and its genuine shifted root owners.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
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
    {fixedIndex : Nat} (fixedAttempt : StageAttempt covered chain fixedIndex sourceFloor sourceRootStage)
    (fixed : fixedAttempt.OccurrenceFamily)

include actual in
/-- The fixed occurrence source programmes obey the actual later-pair divided-difference bound.

Neither the fixed attempt nor its programme family depends on the actual
increment's new source/target selection. Each later reading keeps its own
original Point/query/model cache. Original same-patch comparisons derive
their discrepancies from the genuine fourth-order request payments.
-/
theorem occurrence_differenceQuotient_le (sourceIndex targetIndex : Nat)
    (sourceAfter : source.selected.stage ≤ sourceIndex) (targetAfter : next.requested.selected.stage ≤ targetIndex)
    (order coordinate : Fin 2) :
    let programmes := StageAttempt.OccurrenceCompletion.staged (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun stage => (fixed stage).val)
    Canonical.normSq
      ((((retained.targetProgram (next := next) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) /
          increment -
        ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) ≤
      ValueBlocks.derivativeFactor (covered := covered) order coordinate * Canonical.normSq increment := by
  let completed := fun stage => (fixed stage).val
  let preparations := fun stage => (completed stage).1.preparations
  let programmes := StageAttempt.OccurrenceCompletion.staged (parameter := parameter) (frame := frame)
    (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
    covered chain completed
  have cells (channel : Fin 6) (stage : Nat) :
      ((programmes channel).integral.model stage).cells =
        (PreparedParents.sources covered (preparations stage) chain).cells channel :=
    (StageAttempt.OccurrenceCompletion.staged_cells (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain completed channel stage).trans
        (congrArg (fun sources => sources.cells channel)
          ((completed stage).2.stage_sources.trans (completed stage).1.preparations_sources.symm))
  exact sourcePrograms_differenceQuotient_le (firstNext := next) (lastNext := next)
    retained retained actual preparations programmes cells sourceIndex targetIndex sourceAfter targetAfter
    order coordinate

include actual in
/-- The computed positive row request pays the fixed source family's actual divided difference for every later pair. -/
theorem occurrence_differenceQuotient_lt (accuracy : AccuracyRequest) (sourceIndex targetIndex : Nat)
    (sourceAfter : source.selected.stage ≤ sourceIndex) (targetAfter : next.requested.selected.stage ≤ targetIndex)
    (order coordinate : Fin 2)
    (small : Norm.Basic.normSq increment ≤
      (ValueBlocks.derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance) :
    let programmes := StageAttempt.OccurrenceCompletion.staged (parameter := parameter) (frame := frame)
      (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun stage => (fixed stage).val)
    Canonical.normSq
      ((((retained.targetProgram (next := next) (Specification.Table.baseIndex order coordinate)).model
        targetIndex).integralSample -
        ((programmes (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) /
          increment -
        ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) <
      accuracy.tolerance := by
  let factor := ValueBlocks.derivativeFactor (covered := covered) order coordinate
  have divisorPositive : 0 < factor + 1 := Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (ValueBlocks.derivativeFactor_nonnegative (covered := covered) order coordinate)
    (by decide +kernel : (0 : Rational) < 1)
  have smallCanonical := (Norm.Basic.normSq_eq_canonical increment).symm.trans_le small
  have paid := (Order.Field.le_div_iff_pos divisorPositive).mp
    (smallCanonical.trans_eq
      (ValueBlocks.derivativeIncrementRequest_tolerance (covered := covered) accuracy order coordinate))
  have positive : (0 : Rational) < Canonical.normSq increment :=
    (Norm.Basic.normSq_pos nonzero).trans_eq (Norm.Basic.normSq_eq_canonical increment)
  have strict : factor * Canonical.normSq increment < Canonical.normSq increment * (factor + 1) :=
    (show factor * Canonical.normSq increment = factor * Canonical.normSq increment + 0 by ring1).trans_lt
      ((Order.Arithmetic.add_lt_add_left_direct positive (factor * Canonical.normSq increment)).trans_eq
        (by ring1))
  exact (occurrence_differenceQuotient_le (next := next) actual fixedAttempt fixed
    sourceIndex targetIndex sourceAfter targetAfter order coordinate).trans_lt (strict.trans_le paid)

include actual in
/-- The same estimate reads the actual retained source and target jets' value/first/second fields.

Whole original jet factory equations identify the supplied owners. Only
scalar sample readbacks are composed; no jet, stage, programme, Point or
query is rebuilt to transport the internally paid comparison.
-/
theorem occurrence_jet_differenceQuotient_lt
    (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = StageAttempt.OccurrenceCompletion.jet
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun stage => (fixed stage).val))
    (targetCompleted : next.requested.request.attempt.OccurrenceFamily)
    (targetJet : SynchronizedPeriodJet target)
    (targetFactory : targetJet = retained.occurrenceJet (next := next) targetCompleted)
    (accuracy : AccuracyRequest) (sourceIndex targetIndex : Nat)
    (sourceAfter : source.selected.stage ≤ sourceIndex) (targetAfter : next.requested.selected.stage ≤ targetIndex)
    (order coordinate : Fin 2)
    (small : Norm.Basic.normSq increment ≤
      (ValueBlocks.derivativeIncrementRequest (covered := covered) accuracy order coordinate).tolerance) :
    let sourceBase := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
      (sourceJet.value coordinate).integral
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
        (sourceJet.first coordinate).integral (fun index => Fin.elim0 index)) order
    let sourceSlope := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
      (sourceJet.first coordinate).integral
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
        (sourceJet.second coordinate).integral (fun index => Fin.elim0 index)) order
    let targetBase := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
      (targetJet.value coordinate).integral
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
        (targetJet.first coordinate).integral (fun index => Fin.elim0 index)) order
    Canonical.normSq (((targetBase.model targetIndex).integralSample -
      (sourceBase.model sourceIndex).integralSample) / increment -
        (sourceSlope.model sourceIndex).integralSample) < accuracy.tolerance := by
  revert order
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index))
  · intro small
    have bounded := occurrence_differenceQuotient_lt (next := next) actual fixedAttempt fixed
      accuracy sourceIndex targetIndex sourceAfter targetAfter 0 coordinate small
    have sourceBase := (congrArg (fun jet : SynchronizedPeriodJet frame =>
      ((jet.value coordinate).integral.model sourceIndex).integralSample) sourceFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model sourceIndex).integralSample)
          (StageAttempt.OccurrenceCompletion.jet_value_integral (parameter := parameter) (frame := frame)
            (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
            covered chain (fun stage => (fixed stage).val) coordinate))
    have sourceSlope := (congrArg (fun jet : SynchronizedPeriodJet frame =>
      ((jet.first coordinate).integral.model sourceIndex).integralSample) sourceFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model sourceIndex).integralSample)
          (StageAttempt.OccurrenceCompletion.jet_first_integral (parameter := parameter) (frame := frame)
            (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
            covered chain (fun stage => (fixed stage).val) coordinate))
    have targetBase := (congrArg (fun jet : SynchronizedPeriodJet target =>
      ((jet.value coordinate).integral.model targetIndex).integralSample) targetFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model targetIndex).integralSample)
          (retained.occurrenceJet_value_integral (next := next) targetCompleted coordinate))
    have difference := congrArg₂ (fun output base : Canonical => output - base) targetBase sourceBase
    have quotient := congrArg₂ (fun difference slope : Canonical => difference / increment - slope)
      difference sourceSlope
    exact (congrArg Canonical.normSq quotient).trans_lt bounded
  · intro small
    have bounded := occurrence_differenceQuotient_lt (next := next) actual fixedAttempt fixed
      accuracy sourceIndex targetIndex sourceAfter targetAfter 1 coordinate small
    have sourceBase := (congrArg (fun jet : SynchronizedPeriodJet frame =>
      ((jet.first coordinate).integral.model sourceIndex).integralSample) sourceFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model sourceIndex).integralSample)
          (StageAttempt.OccurrenceCompletion.jet_first_integral (parameter := parameter) (frame := frame)
            (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
            covered chain (fun stage => (fixed stage).val) coordinate))
    have sourceSlope := (congrArg (fun jet : SynchronizedPeriodJet frame =>
      ((jet.second coordinate).integral.model sourceIndex).integralSample) sourceFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model sourceIndex).integralSample)
          (StageAttempt.OccurrenceCompletion.jet_second_integral (parameter := parameter) (frame := frame)
            (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
            covered chain (fun stage => (fixed stage).val) coordinate))
    have targetBase := (congrArg (fun jet : SynchronizedPeriodJet target =>
      ((jet.first coordinate).integral.model targetIndex).integralSample) targetFactory).trans
        (congrArg (fun program : RefinementProgram => (program.model targetIndex).integralSample)
          (retained.occurrenceJet_first_integral (next := next) targetCompleted coordinate))
    have difference := congrArg₂ (fun output base : Canonical => output - base) targetBase sourceBase
    have quotient := congrArg₂ (fun difference slope : Canonical => difference / increment - slope)
      difference sourceSlope
    exact (congrArg Canonical.normSq quotient).trans_lt bounded

/-- The actual two sufficient floors and the internally proved estimate at every later original sample pair. -/
@[expose] def OccurrenceSchedule (accuracy : AccuracyRequest) (sourceStart targetStart : Nat) : Type :=
    { floors : Nat × Nat //
      floors = (Nat.max sourceStart source.selected.stage, Nat.max targetStart next.requested.selected.stage) ∧
      sourceStart ≤ floors.1 ∧ targetStart ≤ floors.2 ∧
      ∀ sourceLater targetLater, floors.1 ≤ sourceLater → floors.2 ≤ targetLater →
        ∀ order coordinate : Fin 2,
          let programmes := StageAttempt.OccurrenceCompletion.staged (parameter := parameter) (frame := frame)
            (basis := basis) (count := count) (floor := sourceFloor) (rootStage := sourceRootStage)
            covered chain (fun stage => (fixed stage).val)
          Canonical.normSq
            ((((retained.targetProgram (next := next) (Specification.Table.baseIndex order coordinate)).model
              targetLater).integralSample -
              ((programmes (Specification.Table.baseIndex order coordinate)).integral.model
                sourceLater).integralSample) / increment -
              ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
                sourceLater).integralSample) < accuracy.tolerance }

include actual in
/-- Retain actual increment-dependent sufficient floors and the comparison at EVERY later pair of samples.

The maxima use this increment's newly paid selections, whose tolerance is
min(spatial.tolerance, normSq increment squared). They do not use the fixed
source family's selected stage as a surrogate for numerical accuracy.
-/
def occurrenceSchedule (accuracy : AccuracyRequest) (sourceStart targetStart : Nat)
    (small : Norm.Basic.normSq increment ≤ (ValueBlocks.derivativeRequest allocation accuracy).tolerance) :
    OccurrenceSchedule (next := next) (retained := retained) fixedAttempt fixed accuracy sourceStart targetStart :=
  let floors := (Nat.max sourceStart source.selected.stage, Nat.max targetStart next.requested.selected.stage)
  ⟨floors, rfl, Order.le_max_left _ _, Order.le_max_left _ _, by
    intro sourceLater targetLater sourceAfter targetAfter order coordinate
    exact occurrence_differenceQuotient_lt (next := next) actual fixedAttempt fixed accuracy sourceLater targetLater
      ((Order.le_max_right sourceStart source.selected.stage).trans sourceAfter)
      ((Order.le_max_right targetStart next.requested.selected.stage).trans targetAfter) order coordinate
      (small.trans (ValueBlocks.derivativeRequest_le_row allocation accuracy order coordinate))⟩

end ValueBlocks.Integral

namespace ValueBlocks

/-- Request the actual increment-dependent data once and return sufficient floors for all later jet readings.

The fixed source family and source jet are inputs before the accuracy and
increment. The displayed derivativeRequest is a positive quadrance radius
computed from the original geometry alone. EVERY nonzero increment paying
it is accepted here; each such query constructs its own h-fourth requests,
same-spine shifted geometry, actual Taylor cache and target source jet.
No fixed selected stage is retagged to meet the smaller increment's budget.
-/
def withRequestedOccurrenceDerivative
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {fixedIndex sourceFloor sourceRootStage : Nat}
    (fixedAttempt : StageAttempt covered chain fixedIndex sourceFloor sourceRootStage)
    (fixed : fixedAttempt.OccurrenceFamily) (sourceJet : SynchronizedPeriodJet frame)
    (sourceFactory : sourceJet = StageAttempt.OccurrenceCompletion.jet
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (floor := sourceFloor) (rootStage := sourceRootStage)
      covered chain (fun stage => (fixed stage).val))
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {root : Named} (roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root)
    (spatial : AccuracyRequest) (sourceCurrent targetCurrent targetFloor targetRootStage : Nat)
    (accuracy : AccuracyRequest) (sourceStart targetStart : Nat)
    (increment : Canonical) (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤ (derivativeRequest allocation accuracy).tolerance)
    {Result : Type u}
    (consume :
      (keptTarget : Paths.Frame (parameter + increment)) →
      keptTarget = ranges.targetFrame increment
        ((derivativeRequest_admitted allocation accuracy increment small).trans allocation.bound_le_regularBound) →
      (source : StageAttempt.Requested (parameter := parameter) (frame := frame)
        covered chain sourceCurrent sourceFloor sourceRootStage
        (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))) →
      (next : StageAttempt.Requested.Shifted (target := keptTarget) source ranges allocation
        (derivativeRequest_admitted allocation accuracy increment small) (fun _ => spatial) roots
        targetCurrent targetFloor targetRootStage) →
      (retained : ValueBlocks (next := next)) → retained = build (next := next) →
      (_actual : Integral (next := next) retained) →
      (targetCompleted : next.requested.request.attempt.OccurrenceFamily) →
      (targetJet : SynchronizedPeriodJet keptTarget) →
      Connection.ConnectionCertificate targetJet → PicardFuchs.PicardFuchsCertificate targetJet →
      targetJet = retained.occurrenceJet (next := next) targetCompleted →
      (paid : Integral.OccurrenceSchedule (next := next) (retained := retained)
        fixedAttempt fixed accuracy sourceStart targetStart) →
      (∀ sourceLater targetLater, paid.val.1 ≤ sourceLater → paid.val.2 ≤ targetLater →
        ∀ order coordinate : Fin 2,
          let sourceBase := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
            (sourceJet.value coordinate).integral
            (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
              (sourceJet.first coordinate).integral (fun index => Fin.elim0 index)) order
          let sourceSlope := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
            (sourceJet.first coordinate).integral
            (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
              (sourceJet.second coordinate).integral (fun index => Fin.elim0 index)) order
          let targetBase := Fin.cases (motive := fun _ : Fin 2 => RefinementProgram)
            (targetJet.value coordinate).integral
            (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram)
              (targetJet.first coordinate).integral (fun index => Fin.elim0 index)) order
          Canonical.normSq (((targetBase.model targetLater).integralSample -
            (sourceBase.model sourceLater).integralSample) / increment -
              (sourceSlope.model sourceLater).integralSample) < accuracy.tolerance) → Result) : Result :=
  have admitted := derivativeRequest_admitted allocation accuracy increment small
  let keptTarget := ranges.targetFrame increment (admitted.trans allocation.bound_le_regularBound)
  let acquired := StageAttempt.Requested.joint (parameter := parameter) (increment := increment)
    (frame := frame) (basis := basis) (target := keptTarget) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    ranges allocation admitted (fun _ => spatial) roots spatial nonzero
    sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage
  let source := acquired.1
  let next := acquired.2
  let built := buildIntegral (parameter := parameter) (increment := increment) (frame := frame)
    (basis := basis) (target := keptTarget) (count := count) (parent := parent) (parents := parents)
    (covered := covered) (chain := chain) (ranges := ranges) (allocation := allocation) (admitted := admitted)
    (widths := fun _ => spatial) (root := root) (roots := roots) (spatial := spatial) (nonzero := nonzero)
    (sourceCurrent := sourceCurrent) (sourceFloor := sourceFloor) (sourceRootStage := sourceRootStage)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    (source := source) (next := next)
  let paid := Integral.occurrenceSchedule (next := next) built.2 fixedAttempt fixed
    accuracy sourceStart targetStart small
  built.1.val.withOccurrenceRelations (next := next)
    (fun targetCompleted targetJet connection residual targetFactory =>
      have sourceSelected : source.selected.stage ≤ paid.val.1 :=
        Eq.mpr (congrArg (fun value : Nat => source.selected.stage ≤ value)
          (congrArg (fun pair : Nat × Nat => pair.1) paid.property.1))
          (Order.le_max_right sourceStart source.selected.stage)
      have targetSelected : next.requested.selected.stage ≤ paid.val.2 :=
        Eq.mpr (congrArg (fun value : Nat => next.requested.selected.stage ≤ value)
          (congrArg (fun pair : Nat × Nat => pair.2) paid.property.1))
          (Order.le_max_right targetStart next.requested.selected.stage)
      have later := fun sourceLater targetLater (sourceAfter : paid.val.1 ≤ sourceLater)
          (targetAfter : paid.val.2 ≤ targetLater) (order coordinate : Fin 2) =>
        Integral.occurrence_jet_differenceQuotient_lt (next := next) built.2 fixedAttempt fixed
          sourceJet sourceFactory targetCompleted targetJet targetFactory accuracy sourceLater targetLater
          (sourceSelected.trans sourceAfter) (targetSelected.trans targetAfter) order coordinate
          (small.trans (derivativeRequest_le_row allocation accuracy order coordinate))
      consume keptTarget rfl source next built.1.val built.1.property built.2 targetCompleted
        targetJet connection residual targetFactory paid later)

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
