module
import Purelib.System.IO
import Purelib.Data.String.Basic
import Purelib.Data.String.Parsing
import Purelib.Data.Int.Decimal
import Purelib.Data.List.ToString
import Purelib.Data.Task.Parallel
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily

set_option backward.match.sparseCases false

/-!
Prepare the first canonical cycle for the squarefree reduction of `x²(x³+1)`.
Try its four complete path banks at one supplied dyadic depth, sharing the
canonical branch and endpoint owners. A finite miss reports the failed prefix
and retained obstruction; it does not trigger a search for a successful depth.
-/

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.List

namespace CanonicalPeriodPreparationHarness

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Preparation
open Purelib.Data.Task
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Branches
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.BoundedPreparedBanks
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest)

/-- The repeated-factor Gaussian polynomial `x²(x³+1)`. -/
def polynomial : GaussianPolynomial := ⟨[1, 0, 0, 1, 0, 0]⟩

/-- Print and flush one preparation diagnostic message. -/
def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining the timing boundary. -/
@[noinline] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Time the forced retained computation and print its supplied summary. -/
def timed {α : Type u} (label : String) (work : Thunk α) (summarize : α → String) : IO Unit := do
  report s!"starting {label}"
  let start ← IO.monoMsNow
  let summary ← evaluate fun _ => summarize work.get
  report s!"finished {label}: {(← IO.monoMsNow) - start} ms; {summary}"

/-- Render the exact numerator and denominator of each Gaussian coordinate. -/
def parameterText (parameter : Gaussian) : String :=
  s!"{parameter.re.num} {parameter.re.den} {parameter.im.num} {parameter.im.den}"

/-- Summarize the original owner's anchor and clearance representation sizes. -/
def ownerText {parameter : Gaussian} (owner : Owner parameter) : String :=
  let box := owner.track.initial.box
  let bound := owner.track.initial.clearance.bound

  s!"anchor={parameterText box.anchor}; clearance numerator/denominator \
      bits={bound.num.natAbs.log2 + 1}/{bound.den.log2 + 1}"

/-- Summarize the two original independent sheet owners in index order. -/
def familyText {parameter : Gaussian} (family : SquareRootOwnerFamily.IndependentFamily parameter) : String :=
  s!"sheet 0 {ownerText (family.owner 0)}; sheet 1 {ownerText (family.owner 1)}"

/-- Describe the retained moving-proposal absence, readiness failure or carrying failure. -/
def moveMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.MoveMiss segment current owner request variation → String
  | .unavailable _ => "moving proposal unavailable"
  | .notReady candidate _ _ => s!"moving proposal not ready; {ownerText candidate.owner}"
  | .notCarrying candidate _ _ _ => s!"moving proposal ready but does not carry; {ownerText candidate.owner}"

/-- Describe the retained second-moving-reset obstruction. -/
def laterMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.LaterMiss segment current owner request variation → String
  | .notReady _ => "second move skipped: first owner not ready"
  | .exhausted _ strengthened _ _ moving =>
      s!"first-reset strengthening misses: {ownerText strengthened}; second: {moveMissText moving}"

/-- Describe the retained coefficient-refresh readiness or carrying obstruction. -/
def movedCoefficientMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.MovedCoefficientMiss segment current owner request variation → String
  | .notReady _ => "first-reset coefficient refresh skipped: owner not ready"
  | .notCarrying _ value _ _ => s!"first-reset coefficient bound misses: {ownerText value}"

/-- Describe the retained finite source-preparation obstruction and variation bound. -/
def sourceMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest}
    (report : BoundedPreparedSource.Inconclusive segment current owner request) : String :=
  let reason := match report.reason with
    | .strengthened _ _ _ _ _ coefficient _ _ moving later movedCoefficient =>
        s!"inherited, direct and coefficient bounds miss; first: {moveMissText moving}; {laterMissText later}; \
          coefficient: {ownerText coefficient}; {movedCoefficientMissText movedCoefficient}"
    | .proposalUnavailable _ _ diagnostic =>
        let stopped := match diagnostic.reason with
          | .search .. => "bounded search unavailable"
          | .candidate _ _ _ miss => match miss with
              | .diameter _ => "candidate diameter fails"
              | .clearance _ _ => "diameter passes; predicted clearance fails"
              | .ambient _ _ _ => "diameter and clearance pass; ambient containment fails"
        s!"{stopped}; retained warmup={diagnostic.warmup.steps.length}/2; search={diagnostic.steps.length}/6"
    | .proposalMiss .. => "bounded diameter proposal does not carry"
  s!"{reason}; moving budget={report.movingBudget}; variation={report.variation.num}/{report.variation.den}"

/-- Locate the failed edge within the retained request prefix and report its actual obstruction. -/
def stepFailureText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {requests : List StepRequest} (index : Nat)
    (failure : BoundedPreparedBanks.StepFailure segment within current owner requests) : String :=
  StepFailure.casesOn
    (motive := fun _ _ _ _ => Nat → String) failure
    (fun current _ request _ _ index =>
        s!"edge={index}; unordered parameters {current.parameter.num}/{current.parameter.den} -> \
          {request.endpoint.parameter.num}/{request.endpoint.parameter.den}")
    (fun current owner request _ _ failure index =>
        s!"edge={index}; parameters {current.parameter.num}/{current.parameter.den} -> \
          {request.endpoint.parameter.num}/{request.endpoint.parameter.den}; {ownerText owner}; \
          {sourceMissText failure}")
    (fun _ _ _ _ _ _ _ rest index => stepFailureText (index + 1) rest) index
termination_by structural failure

/-- Locate the failed segment within the retained prepared-path prefix. -/
def pathFailureText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {depth : Nat} {diameter : PreparedSheetContinuation.Coordinate}
    {positive : 0 < diameter}
    {start finish : Gaussian} {path : ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)} (index : Nat)
    (failure : BoundedPreparedBanks.PathFailure depth diameter positive path within owner) : String :=
  PathFailure.casesOn
    (motive := fun {_ _} _ _ _ _ => Nat → String) failure
    (fun _ _ _ _ failure index => s!"segment={index}; {stepFailureText 0 failure}")
    (fun _ _ _ _ _ _ rest index => pathFailureText (index + 1) rest) index
termination_by structural failure

/-- Try a complete bank at the supplied depth and report its accepted size or failed prefix. -/
def bankText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} (depth : Nat)
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) : String :=
  have positive : (0 : PreparedSheetContinuation.Coordinate) < 1 := by decide
  let outcome : Except
      (BoundedPreparedBanks.Inconclusive depth 1 positive path within owner)
      (BoundedPreparedBanks.PathSuccess depth 1 positive path within owner) :=
    BoundedPreparedBanks.attempt depth 1 positive path within owner
  match outcome with
  | .error failure => s!"inconclusive: {pathFailureText 0 failure.failure}"
  | .ok accepted => s!"accepted; cells={accepted.prepared.stepCount}"

/-- Prepare the first cycle's canonical owners and attempt all four complete banks at one depth. -/
def prepared {source : GaussianPolynomial}
    (input : Polynomial.Prepared source) (cycle : Fin input.genus) (depth : Nat) : IO Unit := do
  let curve := input.curve
  let branchesCache := Thunk.mk fun _ => BranchIsolation.data curve
  timed "canonical cubic branch isolation" branchesCache fun branches =>
      s!"sites={branches.siteCount}; \
        anchors={List.ofFn fun index : Fin branches.siteCount => parameterText (branches.anchorAt index)}"
  let branches := branchesCache.get
  let higher := BranchCutLifts.degreeGtOne_of_cycleIndex curve cycle
  let geometry := (BranchConfiguration.configurationOfData curve branches).branches
  let left := BranchConfiguration.basisPairLeftIndexOfData curve branches cycle
  let right := BranchConfiguration.basisPairRightIndexOfData curve branches cycle
  let leftStateCache := Thunk.mk fun _ => Cuts.refinedState geometry higher left 0
  let rightStateCache := Thunk.mk fun _ => Cuts.refinedState geometry higher right 0
  let connectorCache := Thunk.mk fun _ => Cuts.connectorAt geometry higher left right 0
  timed "left branch state" leftStateCache fun state => s!"anchor={parameterText state.box.anchor}"
  timed "right branch state" rightStateCache fun state => s!"anchor={parameterText state.box.anchor}"
  timed "canonical connector" connectorCache fun path => s!"segments={path.segmentCount}"
  let leftState := leftStateCache.get
  let rightState := rightStateCache.get
  let connector := connectorCache.get
  let within := Cuts.connectorAt_withinAmbient geometry higher left right 0
  let leftNonzero := Cuts.connectorAt_start_eval_ne_zero geometry higher left right 0
  let rightNonzero := Cuts.connectorAt_finish_eval_ne_zero geometry higher left right 0
  let leftFamily := Thunk.mk fun _ => SquareRootOwnerFamily.independentFamily leftNonzero
  let rightFamily := Thunk.mk fun _ => SquareRootOwnerFamily.independentFamily rightNonzero
  let families := Thunk.mk fun _ => Parallel.two
    (fun _ => leftFamily.get) (fun _ => rightFamily.get)
  timed "joined endpoint families" families fun pair => s!"left: {familyText pair.1}; right: {familyText pair.2}"
  let rightPath := BranchCutLifts.ownerBoundaryPath rightState
  let leftPath := BranchCutLifts.ownerBoundaryPath leftState
  let attempts := Thunk.mk fun _ => Parallel.four
    (fun _ => bankText depth connector within (families.get.1.owner 0))
    (fun _ => bankText depth rightPath
      (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) (families.get.2.owner 0))
    (fun _ => bankText depth (BranchCutLifts.ClearPath.reverse connector)
      (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) (families.get.2.owner 1))
    (fun _ => bankText depth leftPath
      (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) (families.get.1.owner 1))
  timed s!"four complete banks at depth {depth}; cells per segment={2 ^ depth}" attempts fun result =>
    s!"forward: {result.1}; right: {result.2.1}; backward: {result.2.2.1}; left: {result.2.2.2}"

/-- Reduce the polynomial and attempt its first standard cycle at the supplied finite depth. -/
def run (depth : Nat) : IO Unit := do
  match Polynomial.prepare polynomial with
  | .regular _ input =>
      if valid : 0 < input.genus then
        report s!"computed genus={input.genus}; normalized standard differential dx/z"
        prepared input ⟨0, valid⟩ depth
      else throw (IO.userError "computed curve has no standard cycle")
  | _ => throw (IO.userError "raw repeated-factor input did not produce a regular curve")

end CanonicalPeriodPreparationHarness

/-- Parse one finite dyadic depth for the canonical cycle-preparation attempt. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | [depthText] =>
      let some depth := Purelib.Data.String.toNat? depthText | throw (IO.userError
        "depth must be a natural number")
      CanonicalPeriodPreparationHarness.run depth
  | _ => throw (IO.userError "usage: canonical_period_preparation_harness DEPTH")
