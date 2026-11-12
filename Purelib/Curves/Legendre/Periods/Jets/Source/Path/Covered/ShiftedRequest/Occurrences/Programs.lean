module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Occurrences
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

/-! # Actual occurrence-jet models on the retained Request family

The whole given jet is identified by its original factory equation. Each
pointwise readback uses the supplied completion family's actual Stage and
source lists; no stage, completion or programme factory runs in the proof.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    {geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root}
    {index floor rootStage : Nat} (request : Request geometry index floor rootStage)
    (completed : request.attempt.OccurrenceFamily)

/-- The supplied positional completion family keeps the same entire original model at each literal stage. -/
theorem occurrence_staged_model (channel : Fin 6) (stage : Nat) :
    (StageAttempt.OccurrenceCompletion.staged (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val) channel).integral.model stage =
        (request.programme channel).model stage := by
  exact (StageAttempt.OccurrenceFamily.staged_model (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (covered := request.covered) (chain := request.chain)
    (index := index) (floor := floor) (rootStage := rootStage) (attempt := request.attempt)
    completed channel stage).trans
      (request.programme_model (parameter := parameter) (increment := increment) (basis := basis)
        (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
        (rootStage := rootStage) channel stage).symm

/-- A given occurrence jet's actual value model is the corresponding unchanged reference programme model. -/
theorem occurrence_value_model (actual : SynchronizedPeriodJet target)
    (factory : actual = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.value coordinate).integral.model stage =
      (request.programme (Specification.Table.valueIndex coordinate)).model stage := by
  exact (StageAttempt.OccurrenceFamily.value_model (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (covered := request.covered) (chain := request.chain)
    (index := index) (floor := floor) (rootStage := rootStage) (attempt := request.attempt)
    completed actual factory coordinate stage).trans
      (request.programme_model (parameter := parameter) (increment := increment) (basis := basis)
        (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
        (rootStage := rootStage) (Specification.Table.valueIndex coordinate) stage).symm

/-- A given occurrence jet's actual first model is the corresponding unchanged reference programme model. -/
theorem occurrence_first_model (actual : SynchronizedPeriodJet target)
    (factory : actual = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.first coordinate).integral.model stage =
      (request.programme (Specification.Table.firstIndex coordinate)).model stage := by
  exact (StageAttempt.OccurrenceFamily.first_model (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (covered := request.covered) (chain := request.chain)
    (index := index) (floor := floor) (rootStage := rootStage) (attempt := request.attempt)
    completed actual factory coordinate stage).trans
      (request.programme_model (parameter := parameter) (increment := increment) (basis := basis)
        (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
        (rootStage := rootStage) (Specification.Table.firstIndex coordinate) stage).symm

/-- A given occurrence jet's actual second model is the corresponding unchanged reference programme model. -/
theorem occurrence_second_model (actual : SynchronizedPeriodJet target)
    (factory : actual = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val))
    (coordinate : Fin 2) (stage : Nat) :
    (actual.second coordinate).integral.model stage =
      (request.programme (Specification.Table.secondIndex coordinate)).model stage := by
  exact (StageAttempt.OccurrenceFamily.second_model (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (covered := request.covered) (chain := request.chain)
    (index := index) (floor := floor) (rootStage := rootStage) (attempt := request.attempt)
    completed actual factory coordinate stage).trans
      (request.programme_model (parameter := parameter) (increment := increment) (basis := basis)
        (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
        (rootStage := rootStage) (Specification.Table.secondIndex coordinate) stage).symm

/-- Either adjacent-derivative row reads the given jet's same original value or first model. -/
theorem occurrence_base_model (actual : SynchronizedPeriodJet target)
    (factory : actual = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val))
    (order coordinate : Fin 2) (stage : Nat) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((actual.value coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((actual.first coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
      (request.programme (Specification.Table.baseIndex order coordinate)).model stage := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact request.occurrence_value_model (parameter := parameter) (increment := increment) (basis := basis)
      (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
      (rootStage := rootStage) completed actual factory coordinate stage
  · exact request.occurrence_first_model (parameter := parameter) (increment := increment) (basis := basis)
      (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
      (rootStage := rootStage) completed actual factory coordinate stage

/-- Either adjacent-derivative row reads the given jet's same original first or second model. -/
theorem occurrence_slope_model (actual : SynchronizedPeriodJet target)
    (factory : actual = StageAttempt.OccurrenceCompletion.jet (parameter := parameter + increment) (frame := target)
      (basis := basis) (count := count) (floor := floor) (rootStage := rootStage)
      request.covered request.chain (fun selected => (completed selected).val))
    (order coordinate : Fin 2) (stage : Nat) :
    (Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((actual.first coordinate).integral)
      (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((actual.second coordinate).integral)
        (fun index => Fin.elim0 index)) order).model stage =
      (request.programme (Specification.Table.slopeIndex order coordinate)).model stage := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact request.occurrence_first_model (parameter := parameter) (increment := increment) (basis := basis)
      (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
      (rootStage := rootStage) completed actual factory coordinate stage
  · exact request.occurrence_second_model (parameter := parameter) (increment := increment) (basis := basis)
      (target := target) (count := count) (geometry := geometry) (index := index) (floor := floor)
      (rootStage := rootStage) completed actual factory coordinate stage

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

end
