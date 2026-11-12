module

public import scripts.checkpoint.InitialExtraction
public import Purelib.RootIsolation.FTA.Squarefree.Build
public import Purelib.RootIsolation.Multiplicity.Circle.Argument
public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Samples
public import Purelib.Polynomial.Dense.Division.Synthetic.Replay
import Purelib.Data.List.DependentProduct
import Purelib.System.FilePath
import Purelib.System.IO
-- The marked generator equality needs the original proof-only dbgTrace identity body.
import all Init.Util
meta import Purelib.Elab.Deriving.Json
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked original circle-inventory checkpoints

The original isolation and Newton checkpoint procedures restore complete
original states. Retained radial and sample constructors consume those same
states. Every synthetic interpolation division is saved atomically and checked
by literal coefficient reconstruction before its retained tail is resumed.
-/

public section

namespace CircleCheckpoint

open Purelib
open Purelib.System.FilePath (join)
open Purelib.Data
open Data.Json (toJson)
open Data.Gaussian.Basic (Canonical)
open Data.Rat.Fraction (Rational)
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)
open Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Polynomial.Dense.Division
open Polynomial.Dense.Gaussian
open Polynomial.Clearance.Circle (Certificate)
open RootIsolation.State.WindingOne.Basic (WindingOneState)
open RootIsolation.Track.Basic (WindingOneTrack)
open RootIsolation
open RootIsolation.FTA.Squarefree
open RootIsolation.Multiplicity.Circle
open CenterProduct (Sample)
open IntegrationCheckpoint
open RootRefinementCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]
variable [MonadStateOf Counts m] [MonadStateOf PolynomialInverseCheckpoint.Counts m]

/-- Error-preserving execution retaining both original proposal and polynomial-inverse counters. -/
abbrev Execution := ExceptT IO.Error (StateT PolynomialInverseCheckpoint.Counts (StateT Counts BaseIO))

/-- Execute original IO once while preserving both original counter owners across successful and failed results. -/
@[expose] def Execution.liftIO {Alpha : Type} (action : IO Alpha) : Execution Alpha :=
  fun inverseCounts rootCounts => do
    let result ← action.toBaseIO
    return ((result, inverseCounts), rootCounts)

/-- Lift original IO effects into the two retained counter states. -/
instance : MonadLift IO Execution := ⟨Execution.liftIO⟩

/-- Run a circle checkpoint with both original counter records retained even when an IO action fails. -/
@[expose] def Execution.run {Alpha : Type} (action : Execution Alpha) :
    BaseIO ((Except IO.Error Alpha × PolynomialInverseCheckpoint.Counts) × Counts) :=
  ExceptT.run action {} {}

/-- Retain and check the complete exact request independently of its numerical result. -/
@[expose] def request (control : Control) (directory : System.FilePath) (expected : Json) : m Unit := do
  IO.FS.createDirAll directory
  let path := join directory (.mk "request.json")
  if ← path.pathExists then
    let actual : Json ← loadJson path
    unless actual == expected do
      saveJson (join directory (.mk "invalid-request.json")) (Json.mkObj [("saved", actual), ("expected", expected)])
      throw (IO.userError s!"circle checkpoint request mismatch: {path}")
  else
    if control.savedOnly then
      saveJson (join directory (.mk "missing-request.json")) expected
      throw (IO.userError s!"circle checkpoint request absent; generation forbidden: {path}")
    saveJson path expected

/-- Restore the same two original refinement calls and their complete original radial result. -/
@[expose] def radial {polynomial : CoefficientPolynomial} {ambient : Geometry.Rational.Box}
    (degreeAtLeastTwo : 2 ≤ polynomial.natDegree) (squarefree : SquarefreeCertificate polynomial)
    {degreeBound : Nat} (elimination : AxisEliminationCertificate polynomial degreeBound)
    (track : WindingOneTrack polynomial ambient)
    (refineEq : track.refine = Track.Newton.Refinement.refineState
      degreeAtLeastTwo squarefree elimination)
    (current : WindingOneState polynomial ambient) {clearance : Certificate polynomial}
    (shared : Track.Circle.Request clearance ambient)
    (degreePositive : 0 < polynomial.natDegree) (control : Control) (directory : System.FilePath) :
    m {result : Track.Circle.Refinement shared track current //
      result = Track.Circle.Refinement.prepare shared track current degreePositive} := do
  request control directory (Json.mkObj
    [("format", toJson "circle-radial-v1"), ("current", InitialExtractionCheckpoint.stateData current),
     ("residualRadius", toJson (fractionData shared.residualRadius)),
     ("signAccuracy", toJson (fractionData shared.accuracy))])
  let small ← NewtonExtractionCheckpoint.refineState degreeAtLeastTwo squarefree elimination current
    shared.residualRadius shared.residualRadius_positive
    { savedOnly := control.savedOnly, killAfterWrites := none } (join directory (.mk "residual"))
  have smallEq : small.val = track.refine current shared.residualRadius shared.residualRadius_positive :=
    small.property.trans (congrArg (fun refine => refine current shared.residualRadius shared.residualRadius_positive)
      refineEq).symm
  profile directory "circle radial residual state ready"
  let next ← NewtonExtractionCheckpoint.refineState degreeAtLeastTwo squarefree elimination small.val
    shared.accuracy shared.accuracy_positive
    { savedOnly := control.savedOnly, killAfterWrites := none } (join directory (.mk "sign"))
  have nextEq : next.val = track.refine small.val shared.accuracy shared.accuracy_positive :=
    next.property.trans
      (congrArg (fun refine => refine small.val shared.accuracy shared.accuracy_positive) refineEq).symm
  let result := Track.Circle.Refinement.ofStates shared track current degreePositive
    small.val smallEq next.val nextEq
  saveJson (join directory (.mk "radial.json")) (Json.mkObj
    [("small", InitialExtractionCheckpoint.stateData result.small),
     ("next", InitialExtractionCheckpoint.stateData result.next),
     ("sample", toJson (gaussianData result.sample))])
  profile directory "circle radial sign ready"
  return ⟨result, Track.Circle.Refinement.ofStates_eq_prepare
    shared track current degreePositive small.val smallEq next.val nextEq⟩

/-- Restore the sufficient radial result at every same original bounded isolation occurrence. -/
@[expose] def locations {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) (clearance : Certificate polynomial)
    (control : Control) (directory : System.FilePath) :
    m {result : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared) //
      result = HigherLocations.prepare clearance (Build.BoxFTA.ofPrepared prepared) input.degreePositive} := do
  let boxes := Build.BoxFTA.ofPrepared prepared
  let shared := Track.Circle.Request.prepare clearance (largeSquareBox polynomial)
  let entries ← List.DependentProduct.ofFnM boxes.isolation.tracks
    (fun index => Track.Circle.Refinement.prepare shared (boxes.isolation.tracks.get index)
      (boxes.isolation.tracks.get index).initial input.degreePositive)
    (fun index => radial input.degreeAtLeastTwo input.squarefree prepared.elimination
      (boxes.isolation.tracks.get index) (prepared.refine _ (List.get_mem _ index))
      (boxes.isolation.tracks.get index).initial shared input.degreePositive control
      (join directory (.mk s!"owner-{index.val}")))
  return ⟨HigherLocations.ofRefinements clearance boxes input.degreePositive shared rfl entries.val entries.property,
    HigherLocations.ofRefinements_eq_prepare clearance boxes input.degreePositive shared rfl
      entries.val entries.property⟩

/-- Restore one original sufficient interpolation sample from its same retained radial state. -/
@[expose] def sample {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    (locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared))
    (shared : CenterProduct.Request clearance (Build.BoxFTA.ofPrepared prepared))
    (index : Fin shared.regions.length) (control : Control) (directory : System.FilePath) :
    m {result : Sample locations shared index //
      result = Sample.prepare locations shared index} := do
  let track := prepared.isolation.tracks.get (shared.trackIndex index)
  let current := (locations.refinementAt (shared.trackIndex index)).next
  request control (join directory (.mk "selection-v2")) (Json.mkObj
    [("format", toJson "circle-sample-v2"), ("current", InitialExtractionCheckpoint.stateData current),
     ("residualRadius", toJson (fractionData shared.residualRadius)),
     ("threshold", toJson (fractionData shared.threshold))])
  let selected ← if accurate : current.box.diagonalSq ≤ shared.residualRadius ^ 2 then
      pure (Sample.ofState locations shared index current (.reused accurate))
    else do
      let state ← NewtonExtractionCheckpoint.refineState input.degreeAtLeastTwo input.squarefree prepared.elimination
        current shared.residualRadius shared.residualRadius_positive
        { savedOnly := control.savedOnly, killAfterWrites := none } directory
      have stateEq : state.val = track.refine current shared.residualRadius shared.residualRadius_positive :=
        state.property.trans (congrArg
          (fun refine => refine current shared.residualRadius shared.residualRadius_positive)
          (prepared.refine track (List.get_mem _ (shared.trackIndex index)))).symm
      let selection : Sample.Selection track current shared.residualRadius
          shared.residualRadius_positive state.val := stateEq.symm ▸ .refined accurate
      pure (Sample.ofState locations shared index state.val selection)
  saveJson (join directory (.mk "sample-v2.json")) (Json.mkObj
    [("state", InitialExtractionCheckpoint.stateData selected.state),
     ("point", toJson (gaussianData selected.point)), ("reused", toJson selected.selection.isReused)])
  profile directory "circle interpolation sample ready"
  have retained : Sample.ofState locations shared index selected.state selected.selection = selected := by
    cases selected with
    | mk state selection point equation => cases equation; rfl
  return ⟨selected, retained.symm.trans
    (Sample.ofState_eq_prepare locations shared index selected.state selected.selection)⟩

/-- Restore a requested continuation from its same retained original sample state and point.

A sufficient state is reused. Otherwise the original bounded certified Newton
attempt is saved and restored before the unchanged total strict fallback.
Versioned selection data retain the original preceding point and state.
-/
@[expose] def refineSample {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    {locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared)}
    {original : CenterProduct.Request clearance (Build.BoxFTA.ofPrepared prepared)}
    {index : Fin original.regions.length} (sample : Sample locations original index)
    {target : Rational} (shared : Sample.Request locations target)
    (control : Control) (directory : System.FilePath) :
    m {result : Sample.Refinement sample shared //
      result = Sample.Refinement.prepare sample shared} := do
  let directory := join directory (.mk "selection-v2")
  let track := prepared.isolation.tracks.get (original.trackIndex index)
  request control directory (Json.mkObj
    [("format", toJson "circle-source-sample-v2"), ("current", InitialExtractionCheckpoint.stateData sample.state),
     ("previousPoint", toJson (gaussianData sample.point)), ("owner", toJson index.val),
     ("track", toJson (original.trackIndex index).val), ("target", toJson (fractionData target)),
     ("radius", toJson (fractionData shared.radius)), ("attempts", toJson (6 : Nat))])
  let selected ← if accurate : sample.state.box.diagonalSq ≤ shared.radius ^ 2 then
      pure (⟨sample.state, .reused accurate⟩ : (state : WindingOneState polynomial (largeSquareBox polynomial)) ×
        Sample.Refinement.Selection prepared.elimination track sample.state
          shared.radius shared.positive state)
    else do
      let loader : ClearanceLoader prepared.elimination (.canonical prepared.elimination) m := by
        rw [prepared.elimination_eq]
        exact ClearanceLoader.separated { savedOnly := control.savedOnly, afterSave := pure () }
          polynomial input.nonzero input.degreePositive
      let proposal : Canonical :=
        ⟨(sample.state.box.xLower + sample.state.box.xUpper) / 2,
          (sample.state.box.yLower + sample.state.box.yUpper) / 2⟩
      let attempt ← RootRefinementCheckpoint.runWithHeader prepared.elimination sample.state.raw shared.radius
        (.canonical prepared.elimination) proposal loader control (join directory (.mk "attempt"))
        (RootRefinementCheckpoint.requestHeader sample.state.raw shared.radius none)
      match found : attempt.finished.value with
      | some accepted =>
          pure ⟨accepted.state, .accepted accurate attempt accepted found⟩
      | none => do
          let state ← NewtonExtractionCheckpoint.refineState input.degreeAtLeastTwo input.squarefree
            prepared.elimination sample.state shared.radius shared.positive
            { savedOnly := control.savedOnly, killAfterWrites := none } (join directory (.mk "refinement"))
          have stateEq : state.val = track.refine sample.state shared.radius shared.positive :=
            state.property.trans (congrArg (fun refine => refine sample.state shared.radius shared.positive)
              (prepared.refine track (List.get_mem _ (original.trackIndex index)))).symm
          let selection : Sample.Refinement.Selection prepared.elimination track sample.state
              shared.radius shared.positive state.val := stateEq.symm ▸ .refined accurate attempt found
          pure ⟨state.val, selection⟩
  let result := Sample.Refinement.ofSelection sample shared selected.1 selected.2
  let branch := match result.state, result.selection with
    | _, .reused _ => "reused"
    | _, .accepted _ _ _ _ => "accepted"
    | _, .refined _ _ _ => "fallback"
  saveJson (join directory (.mk "sample.json")) (Json.mkObj
    [("state", InitialExtractionCheckpoint.stateData result.state), ("branch", toJson branch),
     ("point", toJson (gaussianData result.point)), ("reused", toJson result.selection.isReused)])
  profile directory "circle scheduled source sample ready"
  return ⟨result, Sample.Refinement.ofSelection_eq_prepare sample shared selected.1 selected.2⟩

/-- Restore the same original sufficient sample bank, preserving each certified reuse or refinement selection. -/
@[expose] def samples {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    (locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared))
    (shared : CenterProduct.Request clearance (Build.BoxFTA.ofPrepared prepared))
    (control : Control) (directory : System.FilePath) :
    m {result : CenterProduct.Samples locations shared // result = CenterProduct.Samples.prepare locations shared} := do
  let entries ← List.DependentProduct.ofFnM shared.regions (Sample.prepare locations shared)
    (fun index => sample prepared locations shared index control (join directory (.mk s!"sample-{index.val}")))
  let result := CenterProduct.Samples.ofEntries locations shared entries.val entries.property
  return ⟨result, CenterProduct.Samples.ofEntries_eq_prepare locations shared entries.val entries.property⟩

set_option genInjectivity false in
/-- Serialized original synthetic quotient and scalar remainder data. -/
structure SyntheticData where
  /-- The exact original ordered quotient coordinates. -/ quotient : List GaussianData
  /-- The exact original scalar remainder coordinates. -/ remainder : GaussianData
deriving Json.ToJson, Json.FromJson

constructive_injectivity SyntheticData

/-- Decode exact retained synthetic data without executing synthetic division. -/
@[expose] def SyntheticData.decode (data : SyntheticData) :
    Except InvalidData (Synthetic.Replay.Witness Canonical) := do
  return ⟨⟨← data.quotient.mapM decodeGaussian⟩, ← decodeGaussian data.remainder⟩

/-- Serialize the actual retained fields of one original complete synthetic result. -/
@[expose] def SyntheticData.ofResult {polynomial : CoefficientPolynomial} {root : Canonical}
    (result : Synthetic.Result polynomial root) : SyntheticData :=
  ⟨result.quotient.coeffs.map gaussianData, gaussianData result.remainder⟩

/-- Generate one original synthetic division once, with its diagnostic marker. -/
@[expose, noinline] def generateDivision (polynomial : CoefficientPolynomial) (root : Canonical) :
    Synthetic.Result polynomial root :=
  dbg_trace "CIRCLE_SYNTHETIC_DIVISION_GENERATOR_FORCED"
  Synthetic.divide polynomial root

/-- The diagnostic marker preserves the complete original synthetic result for every source and node. -/
theorem generateDivision_eq (polynomial : CoefficientPolynomial) (root : Canonical) :
    generateDivision polynomial root = Synthetic.divide polynomial root := by with_unfolding_all rfl

/-- Restore one original complete synthetic result or retain its failed data and violated condition. -/
@[expose] def division (polynomial : CoefficientPolynomial) (root : Canonical)
    (control : Control) (directory : System.FilePath) :
    m {result : Synthetic.Result polynomial root // result = Synthetic.divide polynomial root} := do
  request control directory (Json.mkObj
    [("format", toJson "circle-synthetic-v1"), ("coefficients", toJson (polynomial.coeffs.map gaussianData)),
     ("root", toJson (gaussianData root))])
  let path := join directory (.mk "result.json")
  if ← path.pathExists then
    let raw : SyntheticData ← loadJson path
    match raw.decode with
    | .error failure =>
      saveJson (join directory (.mk "invalid.json")) (Json.mkObj [("condition", toJson failure.message)])
      throw (IO.userError s!"invalid saved synthetic scalar: {path}")
    | .ok witness =>
      match Synthetic.Replay.check polynomial root witness with
      | .ok restored =>
        profile directory "circle synthetic division reused"
        return ⟨restored.val, restored.property.1⟩
      | .error failure =>
        let condition := match failure with
          | .length _ => "wrong original quotient slot count"
          | .emptyRemainder _ _ => "nonzero remainder for empty original source"
          | .reconstruction _ _ _ => "reassembled coefficients differ from original source"
        saveJson (join directory (.mk "invalid.json"))
          (Json.mkObj [("condition", toJson condition), ("data", toJson raw)])
        throw (IO.userError s!"invalid saved synthetic coefficients: {path}")
  if control.savedOnly then
    saveJson (join directory (.mk "missing.json")) (Json.mkObj [("condition", toJson "synthetic generation forbidden")])
    throw (IO.userError s!"missing original synthetic division; generation forbidden: {path}")
  let result := generateDivision polynomial root
  saveJson path (SyntheticData.ofResult result)
  profile directory "circle synthetic division saved"
  return ⟨result, generateDivision_eq polynomial root⟩

/-- Restore the original complete synthetic expansion, consuming each same retained quotient in order. -/
@[expose] def expansion (control : Control) (directory : System.FilePath) :
    (polynomial : CoefficientPolynomial) → (nodes : List Canonical) → (index : Nat) →
      m {result : Interpolation.Expansion polynomial nodes // result = Interpolation.Expansion.prepare polynomial nodes}
  | _, [], _ => pure ⟨.nil, rfl⟩
  | polynomial, node :: remaining, index => do
    let first ← division polynomial node control (join directory (.mk s!"division-{index}"))
    let tail ← expansion control directory first.val.quotient remaining (index + 1)
    return ⟨.cons first.val first.property tail.val, by
      cases first with
      | mk result equation =>
        cases equation
        exact congrArg (fun retained => Interpolation.Expansion.cons (Synthetic.divide polynomial node) rfl retained)
          tail.property⟩

/-- Restore the same complete sufficient original center approximation without repeating any track refinement. -/
@[expose] def approximation {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    (locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared))
    (control : Control) (directory : System.FilePath) :
    m {result : CenterProduct.Approximation locations // result = CenterProduct.Approximation.prepare locations} := do
  let shared := CenterProduct.Request.prepare clearance (Build.BoxFTA.ofPrepared prepared)
  request control directory (Json.mkObj
    [("format", toJson "circle-approximation-v1"), ("gap", toJson (fractionData shared.gaps.bound)),
     ("amplification", toJson (fractionData shared.amplification)),
     ("threshold", toJson (fractionData shared.threshold)),
     ("residualRadius", toJson (fractionData shared.residualRadius))])
  let restored ← samples prepared locations shared control directory
  let samples := restored.val
  have samplesEq := restored.property
  let monic := Split.splitPolynomial samples.points
  let target := DensePolynomial.scale polynomial.leadingCoeff monic
  let difference := polynomial.normalize - target
  let retained ← expansion control (join directory (.mk "expansion")) difference samples.points 0
  let result := CenterProduct.Approximation.ofExpansion locations shared rfl samples samplesEq
    monic rfl target rfl difference rfl retained.val retained.property
  saveJson (join directory (.mk "approximation.json")) (Json.mkObj
    [("points", toJson (samples.points.map gaussianData)), ("monic", toJson (monic.coeffs.map gaussianData)),
     ("target", toJson (target.coeffs.map gaussianData)), ("difference", toJson (difference.coeffs.map gaussianData))])
  profile directory "circle original sufficient approximation ready"
  return ⟨result, CenterProduct.Approximation.ofExpansion_eq_prepare locations shared rfl samples samplesEq
    monic rfl target rfl difference rfl retained.val retained.property⟩

/-- Read every retained incoming schedule value in its original occurrence order. -/
@[expose] def scheduleIncoming {targets : List Rational} : Interpolation.Schedule targets → List Rational
  | .nil => []
  | .cons incoming tail => incoming :: scheduleIncoming tail

/-- Encode the original source, preceding nodes and every retained incoming scheduled tolerance. -/
@[expose] def sourceSamplesHeader (polynomial : CoefficientPolynomial) (previousPoints : List Canonical)
    {targets : List Rational} (schedule : Interpolation.Schedule targets) (separation radius : Rational) : Json :=
  Json.mkObj
    [("format", toJson "circle-source-samples-v1"), ("coefficients", toJson (polynomial.coeffs.map gaussianData)),
     ("previousPoints", toJson (previousPoints.map gaussianData)), ("targets", toJson (targets.map fractionData)),
     ("incoming", toJson ((scheduleIncoming schedule).map fractionData)),
     ("separation", toJson (fractionData separation)), ("radius", toJson (fractionData radius))]

/-- Restore continuations paying the same original factor schedule and one original-factor expansion.

The original approximation's sample bank is the sole starting owner. Its
error-polynomial expansion remains separate: the new versioned subtree
stores a checked expansion of the original factor at one retained node list.
-/
@[expose] def sourceSamples {polynomial : CoefficientPolynomial} {input : Input polynomial}
    (prepared : Input.Prepared input) {clearance : Certificate polynomial}
    (locations : HigherLocations clearance (Build.BoxFTA.ofPrepared prepared))
    (argument : CenterProduct.Approximation locations) {targets : List Rational}
    (schedule : Interpolation.Schedule targets) (paid : schedule.Paid argument.request.gaps.bound)
    (count : targets.length = polynomial.natDegree) (control : Control) (directory : System.FilePath) :
    m {result : Roots.Samples argument schedule // result = Roots.Samples.prepare argument schedule paid count} := do
  let directory := join directory (.mk "scheduled-source-v1")
  let shared := Sample.Request.prepare locations schedule.initial paid.positive
  request control directory (sourceSamplesHeader polynomial argument.samples.points schedule
    argument.request.gaps.bound shared.radius)
  let entries ← List.DependentProduct.ofFnM argument.request.regions
    (fun index => Sample.Refinement.prepare (argument.samples.sampleAt index) shared)
    (fun index => refineSample prepared (argument.samples.sampleAt index) shared control
      (join directory (.mk s!"sample-{index.val}")))
  let nodes := List.ofFn (fun index : Fin argument.request.regions.length =>
    (List.DependentProduct.get argument.request.regions entries.val index).point)
  let retained ← expansion control (join directory (.mk "source-expansion")) polynomial nodes 0
  let result := Roots.Samples.ofExpansion argument schedule paid count shared rfl
    entries.val entries.property nodes rfl retained.val retained.property
  saveJson (join directory (.mk "samples.json")) (Json.mkObj
    [("nodes", toJson (nodes.map gaussianData)),
     ("reused", toJson (List.ofFn (fun index : Fin argument.request.regions.length =>
       (List.DependentProduct.get argument.request.regions entries.val index).selection.isReused)))])
  profile directory "circle original scheduled source samples ready"
  return ⟨result, Roots.Samples.ofExpansion_eq_prepare argument schedule paid count shared rfl
    entries.val entries.property nodes rfl retained.val retained.property⟩

end CircleCheckpoint

end
