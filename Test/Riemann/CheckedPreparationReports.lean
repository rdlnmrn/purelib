module

import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Refinement.Basic
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation.Uniqueness
import Purelib.RootIsolation.Newton.Search.Execution.Uniqueness
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Gaussian.Basic

/-! The actual strengthened candidate is checked in diameter, clearance and
ambient order. These regressions inspect the checker itself, so selecting a
later failed guard or replacing the accepted owner changes their conclusions. -/

namespace Test.Riemann.CheckedPreparationReports

open Purelib.Polynomial.Geometry
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
open Purelib.RootIsolation

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (diameter : Coordinate)
    (accepted : Refinement owner.track.initial.raw (epsilon diameter))

/-- Diameter rejection precedes every later guard on the actual strengthened candidate. -/
example (failed : ¬ (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.diagonalSq <
      diameter) :
    Candidate.check segment parameter owner diameter (Candidate.capture segment parameter owner diameter accepted) =
      .error (.diameter failed) := by
  rw [Candidate.check, dif_neg failed]

/-- Clearance rejection retains the passed diameter test and precedes ambient containment. -/
example (small : (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.diagonalSq <
      diameter)
    (failed : ¬ UniformSquareRootPreparation.predictedClearance segment diameter ≤
      (Candidate.capture segment parameter owner diameter accepted).value.track.initial.clearance.bound) :
    Candidate.check segment parameter owner diameter (Candidate.capture segment parameter owner diameter accepted) =
      .error (.clearance small failed) := by
  rw [Candidate.check, dif_pos small, dif_neg failed]

/-- Ambient rejection occurs only after the actual candidate passes diameter and predicted clearance. -/
example (small : (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.diagonalSq <
      diameter)
    (clear : UniformSquareRootPreparation.predictedClearance segment diameter ≤
      (Candidate.capture segment parameter owner diameter accepted).value.track.initial.clearance.bound)
    (failed : ¬ (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.Refines
      (UniformSquareRootPreparation.rootAmbient segment)) :
    Candidate.check segment parameter owner diameter (Candidate.capture segment parameter owner diameter accepted) =
      .error (.ambient small clear failed) := by
  rw [Candidate.check, dif_pos small, dif_pos clear]
  exact dif_neg failed

/-- Successful checks preserve the exact strengthened owner selected from this accepted refinement. -/
example (small : (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.diagonalSq <
      diameter)
    (clear : UniformSquareRootPreparation.predictedClearance segment diameter ≤
      (Candidate.capture segment parameter owner diameter accepted).value.track.initial.clearance.bound)
    (within : (Candidate.capture segment parameter owner diameter accepted).value.track.initial.box.Refines
      (UniformSquareRootPreparation.rootAmbient segment)) :
    acceptedValue segment parameter owner diameter accepted = some
      { value := (Candidate.capture segment parameter owner diameter accepted).value
        strict := (Candidate.capture segment parameter owner diameter accepted).strict
        diameter := small, clearance := clear, within := within } := by
  rw [acceptedValue, Candidate.check, dif_pos small, dif_pos clear]
  rw [dif_pos within]
  rfl

/-- The produced report reads back the original finite search and exact first-accepted guard checks. -/
example : (attempt segment parameter owner diameter).value =
    match searchValue segment parameter owner diameter with
    | none => none
    | some selected => acceptedValue segment parameter owner diameter selected :=
  attempt_value_eq segment parameter owner diameter

/-- A zero derivative in the actual warm-up retains that inspected center and stops before a Newton update. -/
example (box : Box) (radius : Coordinate) (remaining : Nat) (center : Gaussian)
    (zero : Purelib.Data.Gaussian.Basic.value
      (Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial center) = 0) :
    (proposalTrace polynomial box radius (remaining + 1) center).steps = [.stationary center 0] ∧
      (proposalTrace polynomial box radius (remaining + 1) center).seed = center := by
  exact (proposalTrace polynomial box radius (remaining + 1) center).execution.unique
    (.stationary zero.symm rfl)

/-- A projected unavailable report retains exactly the original warm-up and searched numerical histories. -/
example (unavailable : (attempt segment parameter owner diameter).value = none) :
    let report := attempt segment parameter owner diameter
    let failure := Report.failure segment parameter owner diameter report unavailable
    failure.warmup = report.warmup ∧ failure.steps = report.search.steps ∧
      failure.warmup.steps.length ≤ 2 ∧ failure.steps.length ≤ 6 := by
  let report := attempt segment parameter owner diameter
  let failure := Report.failure segment parameter owner diameter report unavailable
  have execution := report.search.execution
  have equation : report.search.finished.value = searchValue segment parameter owner diameter :=
    report.search.finished.equation.symm
  rw [equation] at execution
  exact ⟨ProposalTrace.unique _ _, failure.execution.steps_unique execution,
    failure.warmup.execution.length_le, failure.execution.length_le⟩

section SearchTermination

open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Data

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {rootAmbient : Box}
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p rootAmbient) (radius : Coordinate)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (proposal : Gaussian)

/-- The actual six-search driver stops after its first rejected center has a zero derivative. -/
example
    (rejected : Newton.Search.Center.Basic.checkCenter elimination current radius
      (Grid.Box.roundedCenter current.box radius 0 proposal) clearances = none)
    (zero : Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval p
      (Grid.Box.roundedCenter current.box radius 0 proposal)) = 0) :
    (Newton.Search.Trace.run elimination current radius clearances proposal).steps =
      [.stationary 0 proposal (Grid.Box.roundedCenter current.box radius 0 proposal) 0] := by
  exact (Newton.Search.Trace.run elimination current radius clearances proposal).execution.steps_unique
    (.stationary rfl rejected zero.symm rfl)

/-- The final actual rejected nonstationary center records exhaustion without an unused next Newton proposal. -/
example (initial : Gaussian) (bits : Nat)
    (history : Newton.Search.Trace.Prefix elimination current radius clearances initial 1 bits proposal 5)
    (equation : Newton.Search.Iteration.search elimination current radius 6 0 initial clearances =
      Newton.Search.Iteration.search elimination current radius 1 bits proposal clearances)
    (rejected : Newton.Search.Center.Basic.checkCenter elimination current radius
      (Grid.Box.roundedCenter current.box radius bits proposal) clearances = none)
    (nonzero : Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval p
      (Grid.Box.roundedCenter current.box radius bits proposal)) ≠ 0) :
    (Newton.Search.Trace.runFrom elimination current radius clearances initial 1 bits proposal 5 history rfl
      equation).steps =
      [.exhausted bits proposal (Grid.Box.roundedCenter current.box radius bits proposal)
        (Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval p
          (Grid.Box.roundedCenter current.box radius bits proposal)))] := by
  exact (Newton.Search.Trace.runFrom elimination current radius clearances initial 1 bits proposal 5 history rfl
    equation).execution.steps_unique (.exhaustedAfter rfl rejected rfl nonzero)

end SearchTermination

end Test.Riemann.CheckedPreparationReports
