module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Newton.Check.Product
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Newton.Search.Replay.Input
public import Purelib.RootIsolation.Newton.Search.Trace
import Purelib.RootIsolation.Refinement.Basic

import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-!
# Exact saved-proposal replay for diameter preparation

Diameter preparation performs two rounded Newton warm-up updates before the
ordinary six-candidate checked search.  This module exposes that finite
equation without changing the canonical implementation or its callers.
The proposal witnesses remain untrusted; multiplication and rounding bounds
identify their exact canonical values.  No convergence premise is used.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay

open Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
  (Coordinate Gaussian GaussianPolynomial Box Owner Result)
open Purelib.Riemann.Integration Purelib.Riemann.Topology
open Purelib.Riemann.RootContinuation

section
open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
/-- Public finite specification of the original two-update warm-up. -/
def warmup (polynomial : Riemann.RootContinuation.CheckedSquareRootPreparation.GaussianPolynomial) (box :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Box) (epsilon :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate) :
    Nat → Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian →
      Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian
  | 0, center => center
  | steps + 1, center =>
      if Gaussian.Basic.value (Dense.Gaussian.Derivative.Evaluation.derivativeEval polynomial center) = 0 then
        center
      else Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay.warmup polynomial box epsilon steps
        (Grid.Box.roundedCenter box epsilon 0
          (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter polynomial center)))

-- Replay the exact exposed copy while retaining the original private helper.

/-- The finite replay warm-up equals the original centered Newton proposal at every displayed step count. -/
theorem warmup_eq (polynomial : Riemann.RootContinuation.CheckedSquareRootPreparation.GaussianPolynomial) (box :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Box) (epsilon :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate)
    (steps : Nat) (center : Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian) :
    Riemann.RootContinuation.CheckedSquareRootPreparation.centeredProposal
        polynomial box epsilon steps center = SquareRoot.Replay.CheckedDiameterReplay.warmup polynomial box epsilon
          steps center := by
  induction steps generalizing center with
  | zero => rfl
  | succ steps ih =>
      simp only [Riemann.RootContinuation.CheckedSquareRootPreparation.centeredProposal,
        SquareRoot.Replay.CheckedDiameterReplay.warmup]
      split
      · rfl
      · exact ih _

end

/-- One cached proposal is identified by a checked product, not a repeated
division.  The derivative value supplied here is already shared by the driver. -/
def checkNewton (polynomial : Riemann.RootContinuation.CheckedSquareRootPreparation.GaussianPolynomial) (center next
  derivative : Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian)
    (derivativeEq : derivative = (Dense.Derivative.derivative polynomial).eval center)
    (nonzero : derivative ≠ 0) :
    Except Newton.Search.Replay.Input.Invalid
      { value : Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian // value = Gaussian.Basic.value
        (Dense.Gaussian.Newton.Basic.newtonCenter polynomial center) } :=
  let value := polynomial.eval center
  if product : (center - next) * derivative = value then
    .ok ⟨next, Dense.Gaussian.Newton.Check.Product.newton_eq_of_product polynomial center next
      (by rw [← derivativeEq]; exact nonzero) (by rw [← derivativeEq]; exact product)⟩
  else .error (.newton center next derivative value product)

variable {polynomial : Riemann.RootContinuation.CheckedSquareRootPreparation.GaussianPolynomial} {ambient :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Box} {start finish :
  Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate)
  (owner : Riemann.RootContinuation.CheckedSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter)))
    (diameter : Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate)

/-- Compute the dyadic radius whose square is controlled by the requested diameter. -/
def epsilon : Fraction.Rational := Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius diameter

section
open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
/-- Perform the original two rounded Newton warm-up updates from the retained owner's box midpoint. -/
def initialProposal : Gaussian :=
  let box := owner.track.initial.box
  SquareRoot.Replay.CheckedDiameterReplay.warmup (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter)))
    box (epsilon diameter) 2
    ⟨(box.xLower + box.xUpper) / 2, (box.yLower + box.yUpper) / 2⟩

/-- Build the candidate owner from the accepted refinement and apply the original two clearance strengthenings. -/
def candidate
    (accepted : Refinement owner.track.initial.raw (epsilon diameter)) :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter)) :=
  SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      (Riemann.Topology.SquareRootContinuationChain.Owner.ofState owner.parameterNonzero accepted.state))

/-- Check the retained candidate's diameter, clearance and ambient refinement in their original order.

Success returns that same candidate with its exact certificates; a failed comparison returns no prepared result. -/
def finishCandidate
    (accepted : Refinement owner.track.initial.raw (epsilon diameter)) :
    Option (Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment parameter owner diameter) :=
  let value := SquareRoot.Replay.CheckedDiameterReplay.candidate segment parameter owner diameter accepted
  if small : value.track.initial.box.diagonalSq < diameter then
    if clear : Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment diameter ≤
        value.track.initial.clearance.bound then
      letI : Decidable (value.track.initial.box.Refines
        (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)) := by
        unfold Box.Refines
        infer_instance
      if within : value.track.initial.box.Refines (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient
        segment) then
        some
          { value := value
            strict := by
              dsimp only [value, SquareRoot.Replay.CheckedDiameterReplay.candidate]
              rw [SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen_box,
                SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
              exact accepted.strict
            diameter := small
            clearance := clear
            within := within }
      else none
    else none
  else none

/-- Exact equation for the original preparation, including the warm-up,
first accepted search result and all three final preparation checks. -/
theorem attempt_eq :
    (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =

    match Newton.Search.Iteration.search
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination _)
        owner.track.initial.raw (epsilon diameter) 6 0
        (SquareRoot.Replay.CheckedDiameterReplay.initialProposal segment parameter owner diameter)
        (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances _) with
    | none => none
    | some accepted => SquareRoot.Replay.CheckedDiameterReplay.finishCandidate segment parameter owner diameter accepted
      := by
  rw [Riemann.RootContinuation.CheckedSquareRootPreparation.attempt_value_eq]
  unfold Riemann.RootContinuation.CheckedSquareRootPreparation.searchValue
    Riemann.RootContinuation.CheckedSquareRootPreparation.initialProposal
    Riemann.RootContinuation.CheckedSquareRootPreparation.epsilon
  unfold SquareRoot.Replay.CheckedDiameterReplay.initialProposal epsilon
  rw [SquareRoot.Replay.CheckedDiameterReplay.warmup_eq]
  dsimp only
  split <;> rename_i found <;> rw [found]
  unfold Riemann.RootContinuation.CheckedSquareRootPreparation.acceptedValue
      Riemann.RootContinuation.CheckedSquareRootPreparation.Candidate.check
      Riemann.RootContinuation.CheckedSquareRootPreparation.Candidate.capture
      SquareRoot.Replay.CheckedDiameterReplay.finishCandidate SquareRoot.Replay.CheckedDiameterReplay.candidate
  dsimp only
  split <;> (first | (split <;> (first | (split <;> rfl) | rfl)) | rfl)

end

open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay in
set_option genInjectivity false in
/-- Cache the proposed owner and the operands of all final preparation
checks, so rejection reports do not repeat their calculation. -/
structure Window (accepted : Refinement owner.track.initial.raw (epsilon diameter)) where
  /-- The actual strengthened candidate built from the retained accepted refinement. -/ value :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter))
  /-- The cached candidate equals the original candidate construction. -/ value_eq : value =
    SquareRoot.Replay.CheckedDiameterReplay.candidate segment parameter owner diameter accepted
  /-- The retained squared diagonal of the candidate box. -/ width :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate
  /-- The cached width is exactly the candidate box's squared diagonal. -/ width_eq : width =
    value.track.initial.box.diagonalSq
  /-- The original predicted-clearance target for this diameter request. -/ requiredFloor :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate
  /-- The retained required floor equals the original prediction. -/ requiredFloor_eq : requiredFloor =
    Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment diameter
  /-- The retained candidate's actual boundary-clearance bound. -/ actualFloor :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Coordinate
  /-- The retained actual floor equals the candidate's clearance. -/ actualFloor_eq : actualFloor =
    value.track.initial.clearance.bound
  /-- The retained ambient box required by the preparation. -/ requiredAmbient :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Box
  /-- The retained ambient box equals the original root-ambient computation. -/ requiredAmbient_eq : requiredAmbient =
    Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment

constructive_injectivity Window

section
open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
/-- Cache the exact candidate and all three final preparation comparisons.

Retain equalities for the measured width, required and actual clearance floors, and required ambient box. -/
def Window.capture (accepted : Refinement owner.track.initial.raw (epsilon diameter)) :
    SquareRoot.Replay.CheckedDiameterReplay.Window segment parameter owner diameter accepted :=
  let value := SquareRoot.Replay.CheckedDiameterReplay.candidate segment parameter owner diameter accepted
  ⟨value, rfl, value.track.initial.box.diagonalSq, rfl,
    Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment diameter, rfl,
    value.track.initial.clearance.bound, rfl, Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment,
      rfl⟩

/-- The first failed final comparison for a retained candidate window.

Later failures retain the successful preceding comparisons, preserving the original check order. -/
inductive Miss {accepted : Refinement owner.track.initial.raw (epsilon diameter)}
    (window : SquareRoot.Replay.CheckedDiameterReplay.Window segment parameter owner diameter accepted) where
  /-- The candidate fails the requested strict diameter bound. -/ | diameter (failed : ¬ window.width < diameter)
  /-- The diameter passes, but the candidate clearance does not cover the required floor. -/ | clearance (small :
    window.width < diameter) (failed : ¬ window.requiredFloor ≤ window.actualFloor)
  /-- The diameter and clearance pass, but the candidate box fails required ambient refinement. -/ | ambient (small :
    window.width < diameter) (clear : window.requiredFloor ≤ window.actualFloor)
      (failed : ¬ window.value.track.initial.box.Refines window.requiredAmbient)

end

open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay in
set_option genInjectivity false in
/-- A prepared result together with its exact association to the original diameter attempt. -/
structure Accepted where
  /-- The actual accepted preparation result on the original segment and owner. -/ result :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment parameter owner diameter
  /-- The original diameter attempt returns this exact accepted result. -/ equation :
    (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
      some result

constructive_injectivity Accepted

variable (proposal : Riemann.RootContinuation.CheckedSquareRootPreparation.Gaussian)
  (trace : Newton.Search.Trace.Finished
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (epsilon diameter)
    (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances _) proposal)

open Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay in
set_option genInjectivity false in
/-- Finite failure of the original checked diameter attempt.

Retain either the exhausted search result or its accepted refinement, cached comparison window and first failing
postcheck. -/
inductive Failure where
  /-- The retained search found no refinement, and the original attempt returns no result. -/ | search (empty :
    trace.value = none)
      (equation :
        (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
      none)
  /-- The retained accepted refinement fails its recorded postcheck, making the original attempt return no result. -/ |
    postcheck (accepted : Refinement owner.track.initial.raw (epsilon diameter))
      (found : trace.value = some accepted)
      (window : SquareRoot.Replay.CheckedDiameterReplay.Window segment parameter owner diameter accepted)
      (miss : SquareRoot.Replay.CheckedDiameterReplay.Miss segment parameter owner diameter window)
      (equation :
        (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
      none)

constructive_injectivity Failure

/-- Every retained replay failure identifies the original diameter attempt with no result. -/
theorem Failure.equation (failure : SquareRoot.Replay.CheckedDiameterReplay.Failure segment parameter owner diameter
  proposal trace) :
    (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
      none := by
  cases failure with
  | search _ equation => exact equation
  | postcheck _ _ _ _ equation => exact equation

/-- Consume the verified warm-up and saved search.  Success and each finite
miss identify the unchanged canonical attempt, with no fallback execution. -/
def complete (proposalEq : proposal = SquareRoot.Replay.CheckedDiameterReplay.initialProposal segment parameter owner
  diameter) :
    Except (SquareRoot.Replay.CheckedDiameterReplay.Failure segment parameter owner diameter proposal trace)
      (SquareRoot.Replay.CheckedDiameterReplay.Accepted segment parameter owner diameter) := by
  have attempt :
      (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
      match trace.value with
      | none => none
      | some accepted => SquareRoot.Replay.CheckedDiameterReplay.finishCandidate segment parameter owner diameter
        accepted := by
    rw [SquareRoot.Replay.CheckedDiameterReplay.attempt_eq, ← proposalEq, trace.equation]
  match found : trace.value with
  | none => exact .error (.search found (by rw [attempt, found]))
  | some accepted =>
      let window := SquareRoot.Replay.CheckedDiameterReplay.Window.capture segment parameter owner diameter accepted
      if small : window.width < diameter then
        if clear : window.requiredFloor ≤ window.actualFloor then
          letI : Decidable (window.value.track.initial.box.Refines window.requiredAmbient) := by
            unfold Box.Refines
            infer_instance
          if within : window.value.track.initial.box.Refines window.requiredAmbient then
            let result : Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment parameter owner diameter
              :=
              { value := window.value
                strict := by
                  change (SquareRoot.Replay.CheckedDiameterReplay.candidate segment parameter owner diameter
                    accepted).track.initial.box.StrictInterior _
                  unfold SquareRoot.Replay.CheckedDiameterReplay.candidate
                  rw [SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen_box,
                    SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
                  exact accepted.strict
                diameter := small
                clearance := clear
                within := within }
            exact .ok ⟨result, by
              rw [attempt, found]
              dsimp only [SquareRoot.Replay.CheckedDiameterReplay.finishCandidate]
              dsimp only [window, SquareRoot.Replay.CheckedDiameterReplay.Window.capture] at small clear within
              rw [dif_pos small, dif_pos clear, dif_pos within]
              rfl⟩
          else
            exact .error (.postcheck accepted found window (.ambient small clear within) (by
              rw [attempt, found]
              dsimp only [SquareRoot.Replay.CheckedDiameterReplay.finishCandidate]
              dsimp only [window, SquareRoot.Replay.CheckedDiameterReplay.Window.capture] at small clear within
              rw [dif_pos small, dif_pos clear, dif_neg within]))
        else
          exact .error (.postcheck accepted found window (.clearance small clear) (by
            rw [attempt, found]
            dsimp only [SquareRoot.Replay.CheckedDiameterReplay.finishCandidate]
            dsimp only [window, SquareRoot.Replay.CheckedDiameterReplay.Window.capture] at small clear
            rw [dif_pos small, dif_neg clear]))
      else
        exact .error (.postcheck accepted found window (.diameter small) (by
          rw [attempt, found]
          dsimp only [SquareRoot.Replay.CheckedDiameterReplay.finishCandidate]
          dsimp only [window, SquareRoot.Replay.CheckedDiameterReplay.Window.capture] at small
          rw [dif_neg small]))

/-- Retain a checked saved failure's actual two-proposal and six-search data without rerunning either procedure.

The saved candidate window supplies the original strengthened owner and all
passed guards. Its failed guard is transported to that exact retained owner. -/
def Failure.diagnostic (proposal : Gaussian)
    (retained : Newton.Search.Trace.Retained
      (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (epsilon diameter)
      (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances _) proposal 6 0 proposal)
    (proposalEq : proposal = SquareRoot.Replay.CheckedDiameterReplay.initialProposal segment parameter owner diameter)
    (warmup : Riemann.RootContinuation.CheckedSquareRootPreparation.Warmup segment parameter owner diameter)
    (failure : Failure segment parameter owner diameter proposal retained.finished) :
    Riemann.RootContinuation.CheckedSquareRootPreparation.Failure segment parameter owner diameter := by
  have seedEq : proposal =
      Riemann.RootContinuation.CheckedSquareRootPreparation.initialProposal segment parameter owner diameter := by
    rw [proposalEq]
    unfold initialProposal Riemann.RootContinuation.CheckedSquareRootPreparation.initialProposal
    rw [SquareRoot.Replay.CheckedDiameterReplay.warmup_eq]
    rfl
  have equation : Riemann.RootContinuation.CheckedSquareRootPreparation.searchValue
      segment parameter owner diameter = retained.finished.value := by
    unfold Riemann.RootContinuation.CheckedSquareRootPreparation.searchValue
    rw [← seedEq]
    exact retained.finished.equation
  refine ⟨warmup, retained.steps, ?_, ?_⟩
  · rw [← seedEq, equation]
    exact retained.execution
  · cases failure with
    | search empty unavailable =>
        have execution : ∃ inspected, Newton.Search.Trace.Execution
            (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination _)
            owner.track.initial.raw (epsilon diameter)
            (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances _) proposal inspected none := by
          cases retained with
          | mk finished steps dataExecution =>
              cases finished with
              | accepted => cases empty
              | exhausted inspected budget equation execution => exact ⟨inspected, execution⟩
              | zeroDerivative center derivative inspected budget derivativeEq zero equation execution =>
                  exact ⟨inspected, execution⟩
        exact .search (equation.trans empty) (seedEq ▸ execution)
    | postcheck accepted found window miss unavailable =>
        let candidate : Riemann.RootContinuation.CheckedSquareRootPreparation.Candidate
            segment parameter owner diameter accepted :=
          ⟨window.value, window.value_eq, by
            rw [window.value_eq]
            unfold SquareRoot.Replay.CheckedDiameterReplay.candidate
            rw [SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen_box,
              SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
            exact accepted.strict⟩
        refine .candidate accepted (equation.trans found) candidate ?_
        cases miss with
        | diameter failed =>
            rw [window.width_eq] at failed
            exact .diameter failed
        | clearance small failed =>
            rw [window.width_eq] at small
            rw [window.requiredFloor_eq, window.actualFloor_eq] at failed
            exact .clearance small failed
        | ambient small clear failed =>
            rw [window.width_eq] at small
            rw [window.requiredFloor_eq, window.actualFloor_eq] at clear
            rw [window.requiredAmbient_eq] at failed
            exact .ambient small clear failed

end Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
