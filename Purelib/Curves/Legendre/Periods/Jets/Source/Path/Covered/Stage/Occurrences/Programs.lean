module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Programs
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

/-! # Actual occurrence-family models on their original preparation stream

The original completed Stage and its exact source readback determine each
whole model. Given jets retain their original factory equations. These
pointwise laws neither rerun a completion nor construct a programme.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceFamily

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index floor rootStage : Nat} {attempt : StageAttempt covered chain index floor rootStage}
    (completed : attempt.OccurrenceFamily)

/-- The actual certified stage model is its SAME whole original preparation-family model. -/
theorem staged_model (channel : Fin 6) (stage : Nat) :
    (OccurrenceCompletion.staged (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val) channel).integral.model stage =
        model covered chain attempt.preparationFamily channel stage := by
  have stored := OccurrenceCompletion.staged_cells (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (floor := floor) (rootStage := rootStage)
    covered chain (fun selected => (completed selected).val) channel stage
  have source := stage_sources (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
    (attempt := attempt) completed stage
  exact congrArg PathModel.mk (stored.trans (congrArg (fun sources => sources.cells channel) source))

/-- The given occurrence jet's actual value model reads the SAME original preparation-family channel. -/
theorem value_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.value coordinate).integral.model stage =
      model covered chain attempt.preparationFamily (Specification.Table.valueIndex coordinate) stage := by
  have retained := congrArg (fun jet : SynchronizedPeriodJet frame =>
    (jet.value coordinate).integral.model stage) factory
  have selected := congrArg (fun programme : RefinementProgram => programme.model stage)
    (OccurrenceCompletion.jet_value_integral (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val) coordinate)
  exact retained.trans (selected.trans (staged_model (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (covered := covered) (chain := chain) (index := index) (floor := floor)
    (rootStage := rootStage) (attempt := attempt) completed (Specification.Table.valueIndex coordinate) stage))

/-- The given occurrence jet's actual first model reads the SAME original preparation-family channel. -/
theorem first_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.first coordinate).integral.model stage =
      model covered chain attempt.preparationFamily (Specification.Table.firstIndex coordinate) stage := by
  have retained := congrArg (fun jet : SynchronizedPeriodJet frame =>
    (jet.first coordinate).integral.model stage) factory
  have selected := congrArg (fun programme : RefinementProgram => programme.model stage)
    (OccurrenceCompletion.jet_first_integral (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val) coordinate)
  exact retained.trans (selected.trans (staged_model (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (covered := covered) (chain := chain) (index := index) (floor := floor)
    (rootStage := rootStage) (attempt := attempt) completed (Specification.Table.firstIndex coordinate) stage))

/-- The given occurrence jet's actual second model reads the SAME original preparation-family channel. -/
theorem second_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.second coordinate).integral.model stage =
      model covered chain attempt.preparationFamily (Specification.Table.secondIndex coordinate) stage := by
  have retained := congrArg (fun jet : SynchronizedPeriodJet frame =>
    (jet.second coordinate).integral.model stage) factory
  have selected := congrArg (fun programme : RefinementProgram => programme.model stage)
    (OccurrenceCompletion.jet_second_integral (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val) coordinate)
  exact retained.trans (selected.trans (staged_model (parameter := parameter) (frame := frame) (basis := basis)
    (count := count) (covered := covered) (chain := chain) (index := index) (floor := floor)
    (rootStage := rootStage) (attempt := attempt) completed (Specification.Table.secondIndex coordinate) stage))

/-- Every original six-table programme model is read from the SAME retained occurrence-family preparation.

The whole given jet factory identifies its original value, first or second
programme. Only the finite table entry is selected; no programme, source,
occurrence completion or sampling operation is reconstructed.
-/
theorem programme_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (channel : Fin 6) (stage : Nat) :
    (actual.programme channel).model stage = model covered chain attempt.preparationFamily channel stage := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_
    (fun c => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_
      (fun empty => Fin.elim0 empty) e) d) c) b) a) channel
  · exact value_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 0 stage
  · exact value_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 1 stage
  · exact first_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 0 stage
  · exact first_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 1 stage
  · exact second_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 0 stage
  · exact second_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory 1 stage

/-- The actual jet's base row retains its original value/derivative programme model at both finite orders. -/
theorem base_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (order coordinate : Fin 2) (stage : Nat) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((actual.value coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((actual.first coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
      model covered chain attempt.preparationFamily (Specification.Table.baseIndex order coordinate) stage := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact value_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory coordinate stage
  · exact first_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory coordinate stage

/-- The actual jet's slope row retains its original value/derivative programme model at both finite orders. -/
theorem slope_model (actual : SynchronizedPeriodJet frame)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (floor := floor) (rootStage := rootStage)
      covered chain (fun selected => (completed selected).val))
    (order coordinate : Fin 2) (stage : Nat) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((actual.first coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((actual.second coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
      model covered chain attempt.preparationFamily (Specification.Table.slopeIndex order coordinate) stage := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact first_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory coordinate stage
  · exact second_model (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (covered := covered) (chain := chain) (index := index) (floor := floor) (rootStage := rootStage)
      (attempt := attempt) completed actual factory coordinate stage

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.OccurrenceFamily

end
