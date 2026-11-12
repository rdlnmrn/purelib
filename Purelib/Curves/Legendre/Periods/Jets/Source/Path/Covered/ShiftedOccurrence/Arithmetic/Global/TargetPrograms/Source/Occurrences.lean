module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Approximation.AccuracyRequest

/-! # Automatic source attachment of the retained six shifted-target programmes

The exact joined shifted geometry supplies its original closed root chain.
The selected request is completed positionally once and retained. Its
literal stage family supplies the original Stages used by the SAME target
programmes. Neither old Ready nor old Distinct is inferred or assumed.
Canonical-cycle transport and all-later derivative comparisons are separate.
-/

public section

universe u

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source (Attachment)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
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

namespace ValueBlocks

variable (retained : ValueBlocks (next := next))

/-- Each original target cell list is the literal source list of its exact retained occurrence-completed stage. -/
private theorem occurrence_cells_eq
    (completed : next.requested.request.attempt.OccurrenceFamily) (channel : Fin 6) (stage : Nat) :
    ((retained.targetCertified (next := next) channel).integral.model stage).cells =
      (completed stage).val.2.stage.sources.cells channel :=
  (retained.targetCertified_cells (next := next) channel stage).trans
    (congrArg (fun source => source.cells channel)
      (StageAttempt.OccurrenceFamily.stage_sources (parameter := parameter + increment) (frame := target)
        (basis := basis) (count := count)
        (parent := next.requested.request.shape.val.1) (parents := next.requested.request.shape.val.2)
        (covered := next.requested.request.covered) (chain := next.requested.request.chain)
        (index := next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
        (attempt := next.requested.request.attempt) completed stage)).symm

/-- The original value programme reads the same occurrence-completed Stage at the displayed coordinate. -/
private theorem sourceValue_occurrence_cells
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) (stage : Nat) :
    (((retained.sourceValue (next := next) coordinate).integral).model stage).cells =
      (completed stage).val.2.stage.sources.cells (Specification.Table.valueIndex coordinate) := by
  have source := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.sourceValue_integral (next := next) coordinate)
  have certified := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.targetCertified_integral (next := next) (Specification.Table.valueIndex coordinate))
  exact source.trans (certified.symm.trans
    (retained.occurrence_cells_eq (next := next) completed (Specification.Table.valueIndex coordinate) stage))

/-- The original first-derivative programme reads the same occurrence-completed Stage at the displayed coordinate. -/
private theorem sourceFirst_occurrence_cells
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) (stage : Nat) :
    (((retained.sourceFirst (next := next) coordinate).integral).model stage).cells =
      (completed stage).val.2.stage.sources.cells (Specification.Table.firstIndex coordinate) := by
  have source := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.sourceFirst_integral (next := next) coordinate)
  have certified := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.targetCertified_integral (next := next) (Specification.Table.firstIndex coordinate))
  exact source.trans (certified.symm.trans
    (retained.occurrence_cells_eq (next := next) completed (Specification.Table.firstIndex coordinate) stage))

/-- The original second-derivative programme reads the same occurrence-completed Stage at the displayed coordinate. -/
private theorem sourceSecond_occurrence_cells
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) (stage : Nat) :
    (((retained.sourceSecond (next := next) coordinate).integral).model stage).cells =
      (completed stage).val.2.stage.sources.cells (Specification.Table.secondIndex coordinate) := by
  have source := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.sourceSecond_integral (next := next) coordinate)
  have certified := congrArg (fun program : RefinementProgram => (program.model stage).cells)
    (retained.targetCertified_integral (next := next) (Specification.Table.secondIndex coordinate))
  exact source.trans (certified.symm.trans
    (retained.occurrence_cells_eq (next := next) completed (Specification.Table.secondIndex coordinate) stage))

/-- Attach the SAME six original target programmes to the actual supplied positional completion family.

All six equations use owned pointwise integral readbacks. The retained
old attempts, checks and typed unpaid outcomes remain in completed; the
new positional admissions never relabel them as old successful checks.
-/
def occurrenceAttachment (completed : next.requested.request.attempt.OccurrenceFamily) :
    Attachment target (constantCycle next.requested.request.chain)
      (retained.sourceValue (next := next)) (retained.sourceFirst (next := next))
      (retained.sourceSecond (next := next)) where
  stages := fun stage => (completed stage).val.2.stage
  valueZero_eq := fun stage => retained.sourceValue_occurrence_cells (next := next) completed 0 stage
  valueOne_eq := fun stage => retained.sourceValue_occurrence_cells (next := next) completed 1 stage
  firstZero_eq := fun stage => retained.sourceFirst_occurrence_cells (next := next) completed 0 stage
  firstOne_eq := fun stage => retained.sourceFirst_occurrence_cells (next := next) completed 1 stage
  secondZero_eq := fun stage => retained.sourceSecond_occurrence_cells (next := next) completed 0 stage
  secondOne_eq := fun stage => retained.sourceSecond_occurrence_cells (next := next) completed 1 stage

/-- Construct a synchronized jet from the identical target programmes and positional source attachment. -/
def occurrenceJet (completed : next.requested.request.attempt.OccurrenceFamily) :
    SynchronizedPeriodJet target :=
  SynchronizedPeriodJet.ofSource (constantCycle next.requested.request.chain)
    (retained.sourceValue (next := next)) (retained.sourceFirst (next := next))
    (retained.sourceSecond (next := next)) (retained.occurrenceAttachment (next := next) completed)

/-- The same attached positional jet retains its original target value integral programme. -/
private theorem packaged_occurrenceJet_value_integral
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) :
    (((retained.occurrenceJet (next := next) completed).value coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.valueIndex coordinate) := by
  unfold occurrenceJet
  exact retained.sourceValue_integral (next := next) coordinate

/-- Read the exact retained target value programme through this same positional jet. -/
theorem occurrenceJet_value_integral
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) :
    (((retained.occurrenceJet (next := next) completed).value coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.valueIndex coordinate) :=
  packaged_occurrenceJet_value_integral retained completed coordinate

/-- The same attached positional jet retains its original target first integral programme. -/
private theorem packaged_occurrenceJet_first_integral
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) :
    (((retained.occurrenceJet (next := next) completed).first coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.firstIndex coordinate) := by
  unfold occurrenceJet
  exact retained.sourceFirst_integral (next := next) coordinate

/-- Read the exact retained target first programme through this same positional jet. -/
theorem occurrenceJet_first_integral
    (completed : next.requested.request.attempt.OccurrenceFamily) (coordinate : Fin 2) :
    (((retained.occurrenceJet (next := next) completed).first coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.firstIndex coordinate) :=
  packaged_occurrenceJet_first_integral retained completed coordinate

/-- Construct actual target source relations from the SAME retained request, without a supplied completion or bound.

The original geometry's signed root chain completes the selected attempt
once. The family retains that actual completion; other stages perform
their own original attempt and positional Common work. The same original
jet is bound before ofJet derives connection and residual comparisons.
The continuation retains the family and all actual relation owners.
-/
def withOccurrenceRelations {Result : Type u}
    (consume : (completed : next.requested.request.attempt.OccurrenceFamily) →
      (actual : SynchronizedPeriodJet target) →
      Connection.ConnectionCertificate actual → PicardFuchs.PicardFuchsCertificate actual →
      actual = retained.occurrenceJet (next := next) completed → Result) : Result :=
  let completed := Request.occurrenceFamily (parameter := parameter) (increment := increment) (target := target)
    (basis := basis) (count := count) (geometry := next.geometry)
    (index := next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
    next.requested.request
  let actual := retained.occurrenceJet (next := next) completed
  let connection := Connection.ConnectionCertificate.ofJet actual
  let residual := PicardFuchs.PicardFuchsCertificate.ofJet actual
  consume completed actual connection residual rfl

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
