module

import scripts.checkpoint.Circle
import TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher
import TestPurelib.Polynomial.Laurent.Toeplitz.Higher
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import Purelib.Polynomial.Winding.Circle
import Purelib.Data.Int.Arithmetic
import Purelib.System.IO

/-!
# Original higher-degree circle construction regression

The original coefficient-derived quadratic isolation supplies both irrational
root owners. Checked saved Newton states feed their sufficient radial and
interpolation requests, and the same retained expansion proves agreement with
the independently computed chart-event winding. Rational centers remain
samples of the original owners throughout this construction.
-/

namespace TestPurelib.RootIsolation.Multiplicity.Circle.Checkpoint

open Purelib
open Purelib.System.FilePath (join)
open Data (Json)
open Data.Json (toJson)
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Polynomial.Dense.Gaussian.Bounds.RootRadius.Box (largeSquareBox)
open Polynomial.Dense.Gaussian.Bounds.Box
open Polynomial.Dense.Division
open Polynomial.Clearance.Circle (Margin)
open RationalFunctions.Curve.Canonical.Circle
open RootIsolation.FTA.Squarefree
open RootIsolation.Multiplicity.Circle
open IntegrationCheckpoint
open RootRefinementCheckpoint
open TestPurelib.Polynomial.Laurent.Toeplitz

/-- The original positive quadratic degree. -/
private def degree : Data.Nat.Positive.RootDegree := ⟨2, by decide⟩

/-- The original descending coefficient polynomial `z²-2`. -/
private def polynomial : CoefficientPolynomial := Polynomial.Power.Gaussian.rootPolynomial 2 degree

/-- The same original coefficient polynomial is normalized before its formal adjunction tower is prepared. -/
private theorem normalized : polynomial.normalize = polynomial := by decide +kernel

/-- The original automatically derived finite squarefree isolation input. -/
private def input : Input polynomial :=
  RootIsolation.Power.Isolation.isolationInput (show (2 : Canonical) ≠ 0 by decide) degree (by decide)

/-- Run one retained higher construction with the original complete numerical procedures. -/
private def higher (directory : System.FilePath) (mode : String) : CircleCheckpoint.Execution Unit := do
  let control ← Control.create
    (mode == "replay" || mode == "reuse-replay" || mode == "reading-replay" || mode == "headline-replay")
    (if mode == "crash" || mode == "resume-probe" then some 1 else none)
  let attempt := Boundary.prepare polynomial 5
  match attempt.2 with
  | .contact _ _ _ => throw (IO.userError "the higher circle fixture met the unit boundary")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "the higher circle fixture lacked sufficient chart clearance")
  | .clear boundary =>
    let paths := attempt.1.paths
    let margin := Margin.prepare paths boundary
    let reading := Polynomial.Winding.Circle.Reading.prepare paths boundary
    CircleCheckpoint.request control directory (Json.mkObj
      [("format", toJson "original-higher-circle-v1"),
       ("coefficients", toJson (polynomial.coeffs.map gaussianData)), ("boundaryDepth", toJson (5 : Nat)),
       ("margin", toJson (fractionData margin.bound))])
    saveJson (join directory (.mk "boundary.json")) (Json.mkObj
      [("winding", toJson reading.winding), ("raw", toJson (Polynomial.Winding.Circle.raw paths)),
       ("margin", toJson (fractionData margin.bound))])
    profile directory "higher circle independent boundary ready"
    let elimination := input.elimination
    let saved ← InitialExtractionCheckpoint.isolateLargeSquare elimination
      (.separated { savedOnly := control.savedOnly, afterSave := pure () }
        _ input.nonzero input.degreePositive)
      input.degreeAtLeastTwo input.squarefree control (join directory (.mk "isolation"))
    let prepared := Input.Prepared.ofIsolation input elimination rfl saved.val saved.property
    profile directory "higher circle original complete isolation ready"
    let radial ← CircleCheckpoint.locations prepared margin.toCertificate control (join directory (.mk "radial"))
    if mode == "reuse-probe" || mode == "reuse-replay" then
      let shared := CenterProduct.Request.prepare margin.toCertificate (Build.BoxFTA.ofPrepared prepared)
      let selected ← CircleCheckpoint.samples prepared radial.val shared control (join directory (.mk "centers"))
      let reuseFlags := List.ofFn (fun index : Fin shared.regions.length =>
        (selected.val.sampleAt index).selection.isReused)
      unless reuseFlags == [true, true] do
        throw (IO.userError "the retained sufficient radial states were unexpectedly refined")
      let counts ← Execution.counts
      let inverseCounts ← PolynomialInverseCheckpoint.Execution.counts
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 && inverseCounts.generated == 0 do
        throw (IO.userError "sample reuse probe regenerated an original numerical proposal")
      saveJson (join directory (.mk s!"sample-{mode}.json")) (Json.mkObj
        [("reused", toJson reuseFlags), ("points", toJson (selected.val.points.map gaussianData)),
         ("counts", toJson counts), ("inverseCounts", toJson inverseCounts)])
      profile directory "checked original sample reuse probe ready"
    else
      let approximation ← CircleCheckpoint.approximation prepared radial.val control (join directory (.mk "centers"))
      have rawEq := approximation.val.raw_eq_insideCount paths
      have windingEq : reading.winding = (radial.val.insideCount : Int) :=
        Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0)
          (reading.raw_eq.symm.trans rawEq)
      unless prepared.isolation.tracks.length == 2 && radial.val.insideCount == 0 && radial.val.outsideCount == 2 &&
          reading.winding == 0 && Polynomial.Winding.Circle.raw paths == 0 &&
          approximation.val.samples.points.length == 2 do
        throw (IO.userError "the original higher inventory or independent chart winding changed")
      if mode == "reading" || mode == "reading-replay" then
        let _ ← TestPurelib.RootIsolation.Multiplicity.Circle.Roots.Reading.Higher.run prepared radial.val
          approximation.val normalized control (join directory (.mk "reading"))
        Purelib.System.IO.println
          "Original higher formal-root reading saved; error<1 and same indexed exterior bounds checked."
      if mode == "headline-replay" then
        profile directory "public irrational original geometry restored without numerical generation"
        let comparison := Higher.ofGeometry prepared paths boundary margin rfl reading rfl
          radial.val radial.property approximation.val approximation.property
        Higher.run comparison
        profile directory "public irrational original Laurent Toeplitz comparison checked"
      let counts ← Execution.counts
      let inverseCounts ← PolynomialInverseCheckpoint.Execution.counts
      if control.savedOnly then
        unless counts.generatedNewton == 0 && counts.generatedRounding == 0 && inverseCounts.generated == 0 do
          throw (IO.userError "saved-only higher replay regenerated an original proposal")
      saveJson (join directory (.mk s!"result-{mode}.json")) (Json.mkObj
        [("inside", toJson radial.val.insideCount), ("outside", toJson radial.val.outsideCount),
         ("winding", toJson reading.winding), ("counts", toJson counts), ("inverseCounts", toJson inverseCounts),
         ("points", toJson (approximation.val.samples.points.map gaussianData))])
      let linked : {value : Int // value = (radial.val.insideCount : Int)} := ⟨reading.winding, windingEq⟩
      Purelib.System.IO.println s!"Original higher circle winding {linked.val}; {(toJson counts).compress}"

/-- Restore the original cubic synthetic chain for a short independent checkpoint-recovery fixture. -/
private def synthetic (directory : System.FilePath) (savedOnly : Bool) : CircleCheckpoint.Execution Unit := do
  let control ← Control.create savedOnly
  let source : CoefficientPolynomial := ⟨[1, 2, 3, 4]⟩
  let first ← CircleCheckpoint.division source 2 control (join directory (.mk "first"))
  let tail ← CircleCheckpoint.expansion control (join directory (.mk "tail")) first.val.quotient [0, 1] 0
  unless first.val.quotient.coeffs == [1, 4, 11] && first.val.remainder == 26 && tail.val.first.remainder == 11 do
    throw (IO.userError "checked original synthetic reconstruction changed")
  Purelib.System.IO.println "Original synthetic checkpoint restored."

/-- Exercise original-source checkpoint recovery separately from an existing zero error-polynomial expansion. -/
private def sourceSynthetic (directory : System.FilePath) (savedOnly interrupted : Bool) :
    CircleCheckpoint.Execution Unit := do
  let control ← Control.create savedOnly
  let source : CoefficientPolynomial := ⟨[1, 0, -1 / 4]⟩
  let nodes : List Canonical := [1 / 2, -1 / 2]
  let scheduled := Polynomial.Dense.Gaussian.Interpolation.Schedule.prepare 1 (by decide) [1, 1] (by
    intro target member
    cases member with
    | head => decide
    | tail _ member =>
        cases member with
        | head => decide
        | tail _ impossible => cases impossible)
  let error : CoefficientPolynomial := ⟨[]⟩
  let oldExpansion ← CircleCheckpoint.expansion control (join directory (.mk "centers/expansion")) error nodes 0
  unless oldExpansion.val.first.quotient.coeffs == [] && oldExpansion.val.first.remainder == 0 do
    throw (IO.userError "the separately retained error-polynomial expansion changed")
  let directory := join directory (.mk "scheduled-source-v1")
  let radius := Target.uniformResidualRadius source (largeSquareBox source) scheduled.val.initial
  CircleCheckpoint.request control directory (CircleCheckpoint.sourceSamplesHeader source nodes scheduled.val 1 radius)
  let sourceDirectory := join directory (.mk "source-expansion")
  if interrupted then
    let first ← CircleCheckpoint.division source (1 / 2) control (join sourceDirectory (.mk "division-0"))
    unless first.val.quotient.coeffs == [1, 1 / 2] && first.val.remainder == 0 do
      throw (IO.userError "the interrupted original-source division lost its exact retained result")
    throw (IO.userError "CIRCLE_SOURCE_CHECKPOINT_INTERRUPTED_AFTER_FIRST_SAVE")
  let restored ← CircleCheckpoint.expansion control sourceDirectory source nodes 0
  unless restored.val.first.quotient.coeffs == [1, 1 / 2] && restored.val.first.remainder == 0 &&
      restored.val.next.first.quotient.coeffs == [1] && restored.val.next.first.remainder == 0 &&
      CircleCheckpoint.scheduleIncoming scheduled.val == [1 / 16, 1 / 4] do
    throw (IO.userError "the original source expansion or complete retained incoming schedule changed")
  Purelib.System.IO.println "Original scheduled-source checkpoint restored; separate error expansion retained."

/-- Execute a selected retained higher or synthetic checkpoint phase without external resource limits. -/
public def run (directory : System.FilePath) (mode : String := "resume") : IO Unit := do
  unless mode == "resume" || mode == "replay" || mode == "crash" || mode == "resume-probe" ||
      mode == "synthetic" || mode == "synthetic-replay" || mode == "reuse-probe" || mode == "reuse-replay" ||
      mode == "source-synthetic" || mode == "source-synthetic-replay" || mode == "source-synthetic-crash" ||
      mode == "reading" || mode == "reading-replay" || mode == "headline-replay" do
    throw (IO.userError "unknown original circle checkpoint phase")
  let action := if mode == "source-synthetic" || mode == "source-synthetic-replay" ||
      mode == "source-synthetic-crash" then
      sourceSynthetic directory (mode == "source-synthetic-replay") (mode == "source-synthetic-crash")
    else if mode == "synthetic" || mode == "synthetic-replay" then
      synthetic directory (mode == "synthetic-replay")
    else higher directory mode
  let ((result, inverseCounts), rootCounts) ← CircleCheckpoint.Execution.run action
  saveJson (join directory (.mk s!"execution-counts-{mode}.json"))
    (Json.mkObj [("proposals", toJson rootCounts), ("polynomialStages", toJson inverseCounts)])
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

end TestPurelib.RootIsolation.Multiplicity.Circle.Checkpoint
