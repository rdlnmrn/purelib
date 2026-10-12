module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.Newton.Search.Execution

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
public import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.SquareRootDegree

@[expose] public section

/-!
# Checked shortcuts for diameter preparation

Proposals use a dyadic radius at the scale of the requested squared
diameter.  Every accepted owner retains strict occurrence containment,
the requested diameter, the existing uniform clearance floor and the
path-wide root ambient.  Rejection leaves the total uniform construction
available; Newton convergence is never an assumption.
-/

namespace Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation

open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Integration Purelib.Riemann.Topology

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained prepared owner with strict original containment and checked diameter, clearance and ambient bounds.

The returned owner keeps the same segment-parameter radicand. Its certificates refer to its exact initial box and the
original uniform preparation request. -/
structure Result {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) where
  /-- The retained prepared owner of the exact original segment-parameter radicand. -/ value : Owner (polynomial.eval
    (segment.pointAt parameter))
  /-- The prepared initial box lies strictly inside the original owner's initial box. -/ strict :
    value.track.initial.box.StrictInterior owner.track.initial.box
  /-- The prepared initial box's squared diagonal is below the original target. -/ diameter :
    value.track.initial.box.diagonalSq < rootDiameter
  /-- The exact prepared clearance meets the retained uniform predicted bound. -/ clearance :
    UniformSquareRootPreparation.predictedClearance segment rootDiameter ≤
    value.track.initial.clearance.bound
  /-- The exact prepared initial box refines the common segment root ambient box. -/ within :
    value.track.initial.box.Refines
    (UniformSquareRootPreparation.rootAmbient segment)

constructive_injectivity Result

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- Perform finitely many rounded Newton proposals within the retained source box and grid.

A zero derivative stops at the current center; otherwise the exact Newton center is rounded using the same box and
epsilon before the next step. -/
public def centeredProposal (polynomial : GaussianPolynomial) (box : Box)
    (epsilon : Coordinate) : Nat → Gaussian → Gaussian
  | 0, center => center
  | steps + 1, center =>
      if Basic.value
          (Derivative.Evaluation.derivativeEval polynomial center) = 0 then
        center
      else centeredProposal polynomial box epsilon steps
        (Grid.Box.roundedCenter box epsilon 0
          (Basic.value
            (Newton.Basic.newtonCenter polynomial center)))

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian

set_option genInjectivity false in
/-- The numerical data of one actually inspected initial Newton proposal. -/
inductive ProposalStep where
  /-- A zero derivative retains its current center and stops immediately. -/
  | stationary (center derivative : Gaussian)
  /-- A nonzero derivative retains the exact Newton center and its rounded successor. -/
  | updated (center derivative newton rounded : Gaussian)

set_option genInjectivity false in
/-- The retained initial proposal steps follow the original rounded Newton procedure exactly. -/
inductive ProposalExecution (polynomial : GaussianPolynomial) (box : Box) (radius : Coordinate) :
    Nat → Gaussian → List ProposalStep → Gaussian → Prop where
  /-- Exhausting the initial proposal budget retains the current center. -/
  | done {center} : ProposalExecution polynomial box radius 0 center [] center
  /-- A zero derivative terminates without computing an unused Newton center. -/
  | stationary {remaining center derivative}
      (derivative_eq : derivative = Basic.value (Derivative.Evaluation.derivativeEval polynomial center))
      (zero : derivative = 0) :
      ProposalExecution polynomial box radius (remaining + 1) center [.stationary center derivative] center
  /-- A nonzero derivative rounds the actual Newton center before continuing the retained tail. -/
  | updated {remaining center derivative newton rounded steps seed}
      (derivative_eq : derivative = Basic.value (Derivative.Evaluation.derivativeEval polynomial center))
      (nonzero : derivative ≠ 0)
      (newton_eq : newton = Basic.value (Newton.Basic.newtonCenter polynomial center))
      (rounded_eq : rounded = Grid.Box.roundedCenter box radius 0 newton)
      (tail : ProposalExecution polynomial box radius remaining rounded steps seed) :
      ProposalExecution polynomial box radius (remaining + 1) center
        (.updated center derivative newton rounded :: steps) seed

set_option genInjectivity false in
/-- The cached initial Newton seed, its actual ordered steps and original proposal equation. -/
structure ProposalTrace (polynomial : GaussianPolynomial) (box : Box) (radius : Coordinate)
    (remaining : Nat) (center : Gaussian) where
  /-- The actual retained seed after the initial bounded proposal steps. -/
  seed : Gaussian
  /-- Every center, derivative, Newton update and rounding actually performed. -/
  steps : List ProposalStep
  /-- The retained runtime data follows this exact original proposal cursor. -/
  execution : ProposalExecution polynomial box radius remaining center steps seed
  /-- The cached seed is the unchanged original proposal result. -/
  seed_eq : seed = centeredProposal polynomial box radius remaining center

/-- Execute the original bounded initial proposals once, retaining their actual numerical data. -/
def proposalTrace (polynomial : GaussianPolynomial) (box : Box) (radius : Coordinate) :
    (remaining : Nat) → (center : Gaussian) → ProposalTrace polynomial box radius remaining center
  | 0, center => ⟨center, [], .done, rfl⟩
  | remaining + 1, center => by
      let derivative := Basic.value (Derivative.Evaluation.derivativeEval polynomial center)
      if zero : derivative = 0 then
        exact ⟨center, [.stationary center derivative], .stationary rfl zero, by
          rw [centeredProposal, if_pos zero]⟩
      else
        let newton := Basic.value (Newton.Basic.newtonCenter polynomial center)
        let rounded := Grid.Box.roundedCenter box radius 0 newton
        let tail := proposalTrace polynomial box radius remaining rounded
        exact ⟨tail.seed, .updated center derivative newton rounded :: tail.steps,
          .updated rfl zero rfl rfl tail.execution, by
            rw [centeredProposal, if_neg zero]
            exact tail.seed_eq⟩

open Purelib.Approximation.Rational
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- The exact positive dyadic search radius for the requested squared diameter. -/
def epsilon (rootDiameter : Coordinate) : Coordinate :=
  SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius rootDiameter

/-- The exact seed after the original two rounded Newton proposal steps. -/
def initialProposal {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  let box := owner.track.initial.box
  centeredProposal (SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt parameter)))
    box (epsilon rootDiameter) 2 ⟨(box.xLower + box.xUpper) / 2, (box.yLower + box.yUpper) / 2⟩

/-- The actual original two-step initial proposal cache, before the six-search attempt. -/
abbrev Warmup {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :=
  ProposalTrace (SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt parameter)))
    owner.track.initial.box (epsilon rootDiameter) 2
    ⟨(owner.track.initial.box.xLower + owner.track.initial.box.xUpper) / 2,
      (owner.track.initial.box.yLower + owner.track.initial.box.yUpper) / 2⟩

/-- The retained original six-search execution, including its terminal reason and exact search equation. -/
abbrev Search {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :=
  Newton.Search.Trace.Retained (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (epsilon rootDiameter)
    (QuadraticLineClearance.Owner.quadraticAxisClearances _)
    (initialProposal segment parameter owner rootDiameter) 6 0
    (initialProposal segment parameter owner rootDiameter)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
  (parameter : Coordinate) (owner : Owner (polynomial.eval (segment.pointAt parameter)))
  (rootDiameter : Coordinate)

/-- The exact original finite search result used to identify accepted refinements and unavailable proposals. -/
def searchValue :=
  Newton.Search.Iteration.search (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (epsilon rootDiameter) 6 0
    (initialProposal segment parameter owner rootDiameter)
    (QuadraticLineClearance.Owner.quadraticAxisClearances _)

set_option genInjectivity false in
/-- The strengthened candidate retained before testing diameter, clearance and ambient containment. -/
structure Candidate (accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)) where
  /-- The actual strengthened root owner. -/
  value : Owner (polynomial.eval (segment.pointAt parameter))
  /-- The retained value is exactly the original double-strengthening operation. -/
  value_eq : value = QuadraticCoefficientClearance.strengthen
    (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      (SquareRootContinuationChain.Owner.ofState owner.parameterNonzero accepted.state))
  /-- The retained candidate lies strictly inside the original owner box. -/
  strict : value.track.initial.box.StrictInterior owner.track.initial.box

/-- Retain the strengthened candidate and original strict containment before any final guard. -/
def Candidate.capture (accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)) :
    Candidate segment parameter owner rootDiameter accepted where
  value := QuadraticCoefficientClearance.strengthen
    (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      (SquareRootContinuationChain.Owner.ofState owner.parameterNonzero accepted.state))
  value_eq := rfl
  strict := by
    rw [QuadraticCoefficientClearance.strengthen_box,
      ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
    exact accepted.strict

set_option genInjectivity false in
/-- The first failed final guard, together with every earlier passed guard.

These finite rejections concern the retained candidate and preserve the
original diameter, predicted-clearance, ambient order. -/
inductive GuardMiss {accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)}
    (candidate : Candidate segment parameter owner rootDiameter accepted) where
  /-- The retained candidate fails the strict requested diameter. -/
  | diameter (failed : ¬ candidate.value.track.initial.box.diagonalSq < rootDiameter)
  /-- Diameter passes and the predicted clearance fails. -/
  | clearance (diameter : candidate.value.track.initial.box.diagonalSq < rootDiameter)
      (failed : ¬ UniformSquareRootPreparation.predictedClearance segment rootDiameter ≤
        candidate.value.track.initial.clearance.bound)
  /-- Diameter and clearance pass; original ambient containment fails. -/
  | ambient (diameter : candidate.value.track.initial.box.diagonalSq < rootDiameter)
      (clearance : UniformSquareRootPreparation.predictedClearance segment rootDiameter ≤
        candidate.value.track.initial.clearance.bound)
      (failed : ¬ candidate.value.track.initial.box.Refines (UniformSquareRootPreparation.rootAmbient segment))

/-- Test the three original guards once against the supplied retained candidate. -/
def Candidate.check {accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)}
    (candidate : Candidate segment parameter owner rootDiameter accepted) :
    Except (GuardMiss segment parameter owner rootDiameter candidate) (Result segment parameter owner rootDiameter) :=
  if diameter : candidate.value.track.initial.box.diagonalSq < rootDiameter then
    if clearance : UniformSquareRootPreparation.predictedClearance segment rootDiameter ≤
        candidate.value.track.initial.clearance.bound then
      letI : Decidable (candidate.value.track.initial.box.Refines
          (UniformSquareRootPreparation.rootAmbient segment)) := by
        unfold Box.Refines
        infer_instance
      if within : candidate.value.track.initial.box.Refines (UniformSquareRootPreparation.rootAmbient segment) then
        .ok ⟨candidate.value, candidate.strict, diameter, clearance, within⟩
      else .error (.ambient diameter clearance within)
    else .error (.clearance diameter clearance)
  else .error (.diameter diameter)

/-- Read the accepted value of one retained refinement's ordered final checks. -/
def acceptedValue (accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)) :
    Option (Result segment parameter owner rootDiameter) :=
  (Candidate.check segment parameter owner rootDiameter
    (Candidate.capture segment parameter owner rootDiameter accepted)).toOption

set_option genInjectivity false in
/-- A bounded search miss or the actual strengthened candidate's first rejected guard.

Search failure retains evidence from that search's actual finite execution;
it establishes no absence of a root or failure of another finite attempt. -/
inductive FailureReason where
  /-- The original search returned no refinement, with its actual certified finite execution. -/
  | search (unavailable : searchValue segment parameter owner rootDiameter = none)
      (execution : ∃ inspected, Newton.Search.Trace.Execution
        (QuadraticAxisElimination.quadraticAxisElimination _)
        owner.track.initial.raw (epsilon rootDiameter)
        (QuadraticLineClearance.Owner.quadraticAxisClearances _)
        (initialProposal segment parameter owner rootDiameter) inspected none)
  /-- The first accepted refinement produces this exact strengthened candidate and failed guard. -/
  | candidate (accepted : Refinement owner.track.initial.raw (epsilon rootDiameter))
      (found : searchValue segment parameter owner rootDiameter = some accepted)
      (value : Candidate segment parameter owner rootDiameter accepted)
      (miss : GuardMiss segment parameter owner rootDiameter value)

set_option genInjectivity false in
/-- The actual attempted numerical steps and first stopped branch of the original bounded preparation.

Every retained center, derivative and update belongs to the same original
six-search execution. Its failure reason retains the accepted candidate when
one exists, rather than reacquiring that candidate on inspection or replay. -/
structure Failure where
  /-- The retained original two-step initial proposal execution and exact seed. -/
  warmup : Warmup segment parameter owner rootDiameter
  /-- The exact ordered attempted numerical search data. -/
  steps : List (Newton.Search.Trace.Attempted owner.track.initial.raw (epsilon rootDiameter))
  /-- The retained steps execute the original search and return its exact selected refinement. -/
  execution : Newton.Search.Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (epsilon rootDiameter)
    (QuadraticLineClearance.Owner.quadraticAxisClearances _) 6 0
    (initialProposal segment parameter owner rootDiameter) steps (searchValue segment parameter owner rootDiameter)
  /-- The actual first unavailable-search or rejected-candidate branch. -/
  reason : FailureReason segment parameter owner rootDiameter

set_option genInjectivity false in
/-- The original two-proposal/six-search attempt with its actual search history and typed final outcome. -/
structure Report where
  /-- The retained original two-step initial proposal execution feeding this search. -/
  warmup : Warmup segment parameter owner rootDiameter
  /-- The actual finite search execution from the original proposal. -/
  search : Search segment parameter owner rootDiameter
  /-- Success or the actual first failed branch of this finite attempt. -/
  outcome : Except (Failure segment parameter owner rootDiameter) (Result segment parameter owner rootDiameter)
  /-- The accepted output is the ordered final-check result of this exact retained search. -/
  outcome_eq : outcome.toOption = match search.finished.value with
    | none => none
    | some accepted => acceptedValue segment parameter owner rootDiameter accepted

/-- Read a report's optional accepted value without acquiring or checking the candidate again. -/
def Report.value (report : Report segment parameter owner rootDiameter) :
    Option (Result segment parameter owner rootDiameter) :=
  report.outcome.toOption

/-- Consume an already retained search and check its candidate, preserving its exact original search identity. -/
def complete (warmup : Warmup segment parameter owner rootDiameter)
    (search : Search segment parameter owner rootDiameter) : Report segment parameter owner rootDiameter := by
  have equation : searchValue segment parameter owner rootDiameter= search.finished.value := search.finished.equation
  match found : search.finished.value with
  | none =>
      have execution : ∃ inspected, Newton.Search.Trace.Execution
          (QuadraticAxisElimination.quadraticAxisElimination _)
          owner.track.initial.raw (epsilon rootDiameter)
          (QuadraticLineClearance.Owner.quadraticAxisClearances _)
          (initialProposal segment parameter owner rootDiameter) inspected none := by
        cases search with
        | mk finished steps executed =>
            cases finished with
            | accepted value inspected budget equation execution => cases found
            | exhausted inspected budget equation execution => exact ⟨inspected, execution⟩
            | zeroDerivative center derivative inspected budget derivativeEq zero equation execution =>
                exact ⟨inspected, execution⟩
      let failure : Failure segment parameter owner rootDiameter :=
        ⟨warmup, search.steps, equation.symm ▸ search.execution, .search (equation.trans found) execution⟩
      exact ⟨warmup, search, .error failure, by
        change none = _
        rw [found]⟩
  | some accepted =>
      let candidate := Candidate.capture segment parameter owner rootDiameter accepted
      match checked : candidate.check segment parameter owner rootDiameter with
      | .ok result => exact ⟨warmup, search, .ok result, by
          change some result = _
          rw [found]
          unfold acceptedValue
          change some result = (Candidate.check segment parameter owner rootDiameter candidate).toOption
          rw [checked]
          rfl⟩
      | .error miss =>
        let failure : Failure segment parameter owner rootDiameter :=
          ⟨warmup, search.steps, equation.symm ▸ search.execution,
            .candidate accepted (equation.trans found) candidate miss⟩
        exact ⟨warmup, search, .error failure, by
          change none = _
          rw [found]
          unfold acceptedValue
          change none = (Candidate.check segment parameter owner rootDiameter candidate).toOption
          rw [checked]
          rfl⟩

/-- Execute the unchanged bounded preparation once and retain its actual search and first failed guard. -/
@[irreducible] def attempt : Report segment parameter owner rootDiameter :=
  let warmup : Warmup segment parameter owner rootDiameter :=
    proposalTrace (SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt parameter)))
      owner.track.initial.box (epsilon rootDiameter) 2
      ⟨(owner.track.initial.box.xLower + owner.track.initial.box.xUpper) / 2,
        (owner.track.initial.box.yLower + owner.track.initial.box.yUpper) / 2⟩
  let retained := Newton.Search.Trace.run (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (epsilon rootDiameter)
    (QuadraticLineClearance.Owner.quadraticAxisClearances _) warmup.seed
  have seedEq : warmup.seed = initialProposal segment parameter owner rootDiameter := warmup.seed_eq
  let search : Search segment parameter owner rootDiameter :=
    Eq.rec (motive := fun seed _ => Newton.Search.Trace.Retained
      (QuadraticAxisElimination.quadraticAxisElimination _) owner.track.initial.raw (epsilon rootDiameter)
      (QuadraticLineClearance.Owner.quadraticAxisClearances _) seed 6 0 seed) retained seedEq
  complete segment parameter owner rootDiameter warmup search

/-- Completing retained search data preserves that exact search cache. -/
theorem complete_search (warmup : Warmup segment parameter owner rootDiameter)
    (search : Search segment parameter owner rootDiameter) :
    (complete segment parameter owner rootDiameter warmup search).search = search := by
  unfold complete
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- A report's value obeys the original first-accepted search and ordered final-guard specification. -/
theorem complete_value (warmup : Warmup segment parameter owner rootDiameter)
    (search : Search segment parameter owner rootDiameter) :
    (complete segment parameter owner rootDiameter warmup search).value =
      match searchValue segment parameter owner rootDiameter with
      | none => none
      | some accepted => acceptedValue segment parameter owner rootDiameter accepted := by
  change (complete segment parameter owner rootDiameter warmup search).outcome.toOption = _
  rw [(complete segment parameter owner rootDiameter warmup search).outcome_eq, complete_search]
  rw [show searchValue segment parameter owner rootDiameter = search.finished.value from search.finished.equation]

/-- The typed bounded attempt preserves the original optional acceptance and exact selected owner. -/
theorem attempt_value_eq : (attempt segment parameter owner rootDiameter).value =
    match searchValue segment parameter owner rootDiameter with
    | none => none
    | some accepted => acceptedValue segment parameter owner rootDiameter accepted := by
  unfold attempt
  exact complete_value segment parameter owner rootDiameter _ _

/-- Read the retained first failed branch from an unavailable report, without another search. -/
def Report.failure (report : Report segment parameter owner rootDiameter)
    (unavailable : report.value = none) : Failure segment parameter owner rootDiameter := by
  cases report with
  | mk warmup search outcome outcomeEq =>
      cases outcome with
      | ok result => cases unavailable
      | error failure => exact failure

/-- Two first failed guards of the same retained candidate agree. -/
theorem GuardMiss.unique {accepted : Refinement owner.track.initial.raw (epsilon rootDiameter)}
    {candidate : Candidate segment parameter owner rootDiameter accepted}
    (left right : GuardMiss segment parameter owner rootDiameter candidate) : left = right := by
  cases left <;> cases right <;> first | rfl | contradiction

/-- The ordered finite attempt determines its failure certificate's retained candidate and guard uniquely. -/
theorem FailureReason.unique (left right : FailureReason segment parameter owner rootDiameter) : left = right := by
  cases left with
  | search unavailable execution =>
      cases right with
      | search => rfl
      | candidate accepted found value miss => cases unavailable.symm.trans found
  | candidate accepted found value miss =>
      cases right with
      | search unavailable execution => cases unavailable.symm.trans found
      | candidate accepted' found' value' miss' =>
          have same : accepted = accepted' := Option.some.inj (found.symm.trans found')
          cases same
          have sameValue : value = value' := by
            cases value with
            | mk first firstEq firstStrict =>
                cases value' with
                | mk second secondEq secondStrict =>
                    have sameOwner := firstEq.trans secondEq.symm
                    cases sameOwner
                    rfl
          cases sameValue
          have sameMiss := GuardMiss.unique segment parameter owner rootDiameter miss miss'
          cases sameMiss
          rfl

end Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
