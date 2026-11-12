module

import Purelib.Data.Json.Basic
import Purelib.Data.Json.Codec
import Purelib.System.FilePath
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import scripts.checkpoint.InitialExtraction
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Exact.Step
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.Integration
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.RootIsolation.Sturm.Track.Interface
import Purelib.RootIsolation.Newton.Extraction.Initial.Search
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.System.IO

/-!
# Checked initial Newton proposals from a finite real-axis event

The displayed region has two irrational roots and excludes its rational
root. A finite original Sturm request proposes a seed, which the original
Newton checker must independently accept with its complete geometry.
-/

namespace TestPurelib.RootIsolation.Newton.InitialSeeds

open Purelib.Polynomial.Dense.Gaussian

open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Geometry.Rational
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The displayed cubic has its original ordered real coefficient table. -/
private def polynomial : CoefficientPolynomial := ⟨[1, -3, -2, 6]⟩

/-- The original coefficient-sized ambient square surrounds the retained region. -/
private def ambient : Box :=
  let radius := Cast.fromInt 241
  ⟨-radius, radius, -radius, radius, by decide +kernel, by decide +kernel⟩

/-- The asymmetric remaining region contains the two irrational roots and excludes three. -/
private def region : Box :=
  ⟨-(Cast.fromInt 241), Cast.fromInt 3797 / Cast.fromInt 1360,
    -(Cast.fromInt 283) / Cast.fromInt 1360, Cast.fromInt 227 / Cast.fromInt 1360,
    by decide +kernel, by decide +kernel⟩

/-- The same original polynomial and ambient square provide exact line clearances for the region. -/
private def current : State.Raw.RawWindingState polynomial ambient :=
  let left := Clearance.Box.Line.Bezout.verticalOfCoprime polynomial ambient region.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial region.xLower)
      (Path.Axis.verticalPathImag polynomial region.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Clearance.Box.Line.Bezout.verticalOfCoprime polynomial ambient region.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal polynomial region.xUpper)
      (Path.Axis.verticalPathImag polynomial region.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Clearance.Box.Line.Bezout.horizontalOfCoprime polynomial ambient region.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial region.yLower)
      (Path.Axis.horizontalPathImag polynomial region.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Clearance.Box.Line.Bezout.horizontalOfCoprime polynomial ambient region.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal polynomial region.yUpper)
      (Path.Axis.horizontalPathImag polynomial region.yUpper)
      (by decide +kernel) (by decide +kernel))
  let nested : region.Refines ambient :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  { box := region
    refinesAmbient := nested
    proper := by constructor <;> decide +kernel
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
      (left.restrict nested) (right.restrict nested) (bottom.restrict nested) (top.restrict nested)
    rawWinding_ne := by decide +kernel }

/-- The original real-axis coefficient operation supplies the event polynomial. -/
private def realPolynomial := Path.Axis.horizontalPathReal polynomial 0

/-- The actual region's real endpoints define the same finite proper event cell. -/
private def cell : Data.Rat.Interval.Proper.Cell :=
  ⟨⟨region.xLower, region.xUpper, by decide +kernel⟩, by decide +kernel⟩

/-- The displayed nonzero original Sturm count supplies a retained event track. -/
private def event : Sturm.Track.Interface.ZeroEventTrack realPolynomial where
  polynomialNonzero := by decide +kernel
  current := ⟨cell, by decide +kernel⟩

/-- The original separated coordinate construction is retained once for checking the proposed center. -/
private def elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate polynomial
  (by decide +kernel) (by decide +kernel)

/-- The original cached Euclidean result certifies the displayed cubic as squarefree. -/
private def squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial :=
  let derivative := Dense.Gaussian.GCD.derivative polynomial
  let result := Dense.Gaussian.GCD.extendedGCD polynomial derivative
  Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD polynomial derivative result rfl
    (by decide +kernel) (by decide +kernel)

/-- Execute and replay the opt-in extraction through the original partition step.

All five canonical seeds must miss before the actual retained event seed
succeeds. The result retains equality to the same opt-in pure step, never
to a previously admitted default root family. Exact snapshots and counters
check interruption recovery and cold reuse of the original proposal files.
-/
public def checkExtraction (directory : System.FilePath) (mode : String) : IO Unit := do
  let selected : Clearance.Box.Region.ClearRegion polynomial ambient :=
    ⟨current.box, current.refinesAmbient, current.proper, current.clearance⟩
  let state := Exact.State.IsolationState.initial selected
  have nonnegative : ∀ part ∈ state.regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding polynomial part.box := by
    intro part _member
    exact Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
      (by decide +kernel) squarefree elimination part.refinesAmbient part.proper part.clearance
  have positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions := by decide +kernel
  let request : Option Fraction.Rational := some (1 / Cast.fromInt 256)
  let action : RootRefinementCheckpoint.Execution Unit := do
    let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
      (if mode == "crash" then some 1 else none)
    let retained ← InitialExtractionCheckpoint.step elimination
      (.direct elimination (.canonical elimination)) (by decide +kernel) squarefree
      state nonnegative positive control directory request
    unless retained.val.next.tracks.length == 1 do
      throw (IO.userError "the opt-in original partition step lost its retained track")
    let snapshot := Purelib.Data.Json.toJson
      (retained.val.next.tracks.map fun track => InitialExtractionCheckpoint.stateData track.initial)
    let snapshotPath := Purelib.System.FilePath.join directory "opt-in-snapshot.json"
    if ← snapshotPath.pathExists then
      let saved : Purelib.Data.Json ← IntegrationCheckpoint.loadJson snapshotPath
      unless snapshot == saved do throw (IO.userError "opt-in replay changed the complete retained track")
    else
      if control.savedOnly then throw (IO.userError "missing opt-in snapshot; generation forbidden")
      IntegrationCheckpoint.saveJson snapshotPath snapshot
    let first : Purelib.Data.Json ← IntegrationCheckpoint.loadJson
      (Purelib.System.FilePath.join directory "result.json")
    let extra : Purelib.Data.Json ← IntegrationCheckpoint.loadJson
      (Purelib.System.FilePath.join directory "sturm-result.json")
    let firstTried ← match first.getObjValAs? Nat "tried" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    let extraTried ← match extra.getObjValAs? Nat "tried" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    unless firstTried == 5 && extraTried == 1 do
      throw (IO.userError "opt-in acceptance did not exercise five misses followed by one actual event seed")
    let counts ← RootRefinementCheckpoint.Execution.counts
    if control.savedOnly then
      unless counts.generatedNewton == 0 && counts.generatedRounding == 0 && 0 < counts.reusedRounding do
        throw (IO.userError "cold opt-in replay regenerated original Newton/rounding work")
    IntegrationCheckpoint.saveJson (Purelib.System.FilePath.join directory ("counts-" ++ mode ++ ".json")) counts
    System.IO.println
      "Sturm extraction: five original misses, one checked event seed, complete original opt-in step retained"
  let (outcome, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) outcome

/-- Execute the complete cubic isolation for the explicit event-width request.

The original input and once-retained elimination certificate determine the
actual ordered degree-three output. Complete support, track and remainder
snapshots bind cold replay to this new request, without identifying any
previously admitted default channel or changing its cached producer.
-/
public def checkIsolation (directory : System.FilePath) (mode : String) : IO Unit := do
  let input : FTA.Squarefree.Input polynomial := ⟨squarefree, by decide +kernel⟩
  let cachedElimination := input.elimination
  let control ← RootRefinementCheckpoint.Control.create (mode == "replay")
    (if mode == "crash" then some 1 else none)
  let request : Option Fraction.Rational := some (1 / Cast.fromInt 256)
  let output ← InitialExtractionCheckpoint.separatedLargeSquareWithElimination
    input cachedElimination rfl ⟨control.savedOnly, pure (), false⟩ ⟨control.savedOnly, pure (), control.inputDigest⟩
    control directory request
  unless output.val.tracks.length == 3 do
    throw (IO.userError "the opt-in original cubic isolation lost its exact degree-sized track list")
  for track in output.val.tracks do
    unless Winding.Box.Basic.quadrupledBoxWinding polynomial track.initial.box == 4 do
      throw (IO.userError "an opt-in original cubic track lost its actual winding-one state")
  let snapshot := Purelib.Data.Json.mkObj
    [("support", Purelib.Data.Json.toJson (RootStateCheckpoint.boxData output.val.support)),
     ("tracks", Purelib.Data.Json.toJson
       (output.val.tracks.map fun track => InitialExtractionCheckpoint.stateData track.initial)),
     ("remainder", Purelib.Data.Json.toJson (output.val.remainder.map fun part =>
       (RootStateCheckpoint.boxData part.box, IntegrationCheckpoint.fractionData part.clearance.bound)))]
  let snapshotPath := Purelib.System.FilePath.join directory "opt-in-family.json"
  if ← snapshotPath.pathExists then
    let saved : Purelib.Data.Json ← IntegrationCheckpoint.loadJson snapshotPath
    unless snapshot == saved do throw (IO.userError "opt-in replay changed the complete ordered cubic output")
  else
    if control.savedOnly then throw (IO.userError "missing opt-in cubic snapshot; generation forbidden")
    IntegrationCheckpoint.saveJson snapshotPath snapshot
  let counts : RootRefinementCheckpoint.Counts ← IntegrationCheckpoint.loadCounts
    (Purelib.System.FilePath.join directory "proposal-counts.json")
  if control.savedOnly then
    unless counts.generatedNewton == 0 && counts.generatedRounding == 0 && 0 < counts.reusedRounding do
      throw (IO.userError "cold opt-in cubic replay regenerated original finite Newton work")
  System.IO.println "Sturm isolation: complete original new-request cubic output and exact cached elimination retained"

/-- Demand a finite event seed and require acceptance by the same original six-proposal Newton checker.

The original polynomial, ambient, current region and accuracy stay fixed.
The Sturm count names no Gaussian root; all returned winding, clearance,
strictness and accuracy are supplied by the actual original checker.
-/
public def check : IO Unit := do
  let initialCount := Sturm.Count.Basic.sturmRootCount2 realPolynomial cell.interval.lower cell.interval.upper
  unless initialCount ≠ 0 ∧ ¬ region.Contains (3 : Canonical) do
    throw (IO.userError "the finite event lost its actual nonzero count or rational-root exclusion")
  let width : Fraction.Rational := 1 / Cast.fromInt 256
  let depth := Sturm.Track.Request.requestDepth event.current width
  System.IO.println s!"Sturm seed: retain original event count {initialCount}, computed request depth {depth}"
  (← IO.getStdout).flush
  let refined := event.request width
  unless Data.Rat.Interval.Bounds.width refined.current.cell.interval ≤ width do
    throw (IO.userError "the actual original Sturm request missed its retained width budget")
  let seed : Canonical := ⟨Data.Rat.Interval.Bisection.midpoint refined.current.cell.interval, 0⟩
  System.IO.println "Sturm seed: finite event request returned; check its actual proposed Gaussian center"
  (← IO.getStdout).flush
  match Purelib.RootIsolation.Newton.Extraction.Initial.Search.search elimination current 1 [seed] with
  | none => throw (IO.userError "the original finite Newton checker did not accept the event proposal")
  | some accepted =>
      unless accepted.state.box.diagonalSq ≤ 1 ∧ accepted.state.box.StrictInterior region ∧
          Winding.Box.Basic.quadrupledBoxWinding polynomial accepted.state.box = 4 do
        throw (IO.userError "the original accepted event proposal lost complete winding/strictness/accuracy")
      System.IO.println "Sturm seed: actual original checked winding-one refinement retained"

end TestPurelib.RootIsolation.Newton.InitialSeeds
