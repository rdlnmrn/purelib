module

import TestPurelib.RootIsolation.Power
import scripts.checkpoint.RawSubdivision
import scripts.checkpoint.RawRefinement
import scripts.checkpoint.CoherentRootSamples
import Purelib.System.IO
import Purelib.System.FilePath
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# One adversarial-denominator dyadic checkpoint request

The original positive square-root fixture supplies the polynomial, ambient
owner and elimination cache. A runtime-checked narrow nested winding-one box
has 1024-bit endpoint denominators but modest numerical width. One original
accuracy request is produced and then replayed independently in saved-only
mode; no existing numerical store or continued-root request is used.
-/

namespace TestPurelib.RootIsolation.Checkpoint.Dyadic

open Purelib
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
open Purelib.Geometry.Rational
open Purelib.Data.Rat
open IntegrationCheckpoint
open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open Purelib.System.FilePath (join)
open TestPurelib.RootIsolation.Power

/-- A complete cache hit returns the supplied certificate without a refinement call. -/
example {polynomial : CoherentRoot.GaussianPolynomial} {box : Box}
    (track : CoherentRoot.WindingOneTrack polynomial box)
    (entry : Track.Observation.CachedRefinement track) (remaining : List (Track.Observation.CachedRefinement track)) :
    Track.Observation.readRefinement track entry.current entry.epsilon entry.positive (entry :: remaining) =
      entry.result := Track.Observation.readRefinement_head track entry remaining

/-- Loaded numerical roots retain exact pure-policy states at arbitrary natural indices. -/
example {polynomial : CoherentRoot.GaussianPolynomial} {box : Box}
    {input : FTA.Squarefree.Input polynomial} {track : CoherentRoot.WindingOneTrack polynomial box}
    (prepared : CoherentRoot.Accelerated.Initial input track) (index : Nat) :
    prepared.root.stateAt index =
      CoherentRoot.state
        (CoherentRoot.Accelerated.dyadicTrack input prepared.elimination.certificate track.initial) index :=
  prepared.stateAt_eq index

/-- The compared algebraic program reads the same actual loaded numerical cache. -/
example {polynomial : CoherentRoot.GaussianPolynomial} {box : Box}
    {input : FTA.Squarefree.Input polynomial} {track : CoherentRoot.WindingOneTrack polynomial box}
    (prepared : CoherentRoot.Accelerated.Initial input track) (index : Nat) :
    prepared.algebraic.residual.source.sample index = prepared.root.approximation.sample index :=
  prepared.algebraic_sample index

/-- Construct one narrow certified child with large coprime endpoint denominators. -/
private def adversarial
    (input : FTA.Squarefree.Input squarePolynomial)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      squarePolynomial input.eliminationDegree) :
    IO (State.WindingOne.Basic.WindingOneState squarePolynomial ambient) := do
  let delta : Fraction.Rational := 1 / Fraction.Cast.fromInt (Int.ofNat (2 ^ 1024 + 1))
  let xLower := 181 / 128 + delta
  let xUpper := 363 / 256 - delta
  let yLower := -1 / 1024 + delta
  let yUpper := 1 / 1024 - delta
  if xProper : xLower < xUpper then
    if yProper : yLower < yUpper then
      let box : Box := ⟨xLower, xUpper, yLower, yUpper, xProper.le, yProper.le⟩
      if strict : box.StrictInterior squareInitial.box then
        have nested : box.Refines ambient := by
          rewrite [squareInitial_box] at strict
          exact Box.Refinement.StrictInterior.refines strict
        if leftSafe : elimination.vertical.eval xLower ≠ 0 then
          if rightSafe : elimination.vertical.eval xUpper ≠ 0 then
            if bottomSafe : elimination.horizontal.eval yLower ≠ 0 then
              if topSafe : elimination.horizontal.eval yUpper ≠ 0 then
                if four : Winding.Box.Basic.quadrupledBoxWinding squarePolynomial box = 4 then
                  let provider := Clearance.Box.Line.Elimination.Provider.AxisClearances.canonical elimination
                  let left := provider.vertical ambient xLower leftSafe
                  let right := provider.vertical ambient xUpper rightSafe
                  let bottom := provider.horizontal ambient yLower bottomSafe
                  let top := provider.horizontal ambient yUpper topSafe
                  return {
                    box := box
                    refinesAmbient := nested
                    proper := ⟨xProper, yProper⟩
                    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
                      (left.restrict nested) (right.restrict nested)
                      (bottom.restrict nested) (top.restrict nested)
                    rawWindingFour := four
                    ambientLeftClearance := left
                    ambientRightClearance := right
                    ambientBottomClearance := bottom
                    ambientTopClearance := top }
                else throw (IO.userError "adversarial fixture winding differs from four")
              else throw (IO.userError "adversarial fixture top eliminant vanishes")
            else throw (IO.userError "adversarial fixture bottom eliminant vanishes")
          else throw (IO.userError "adversarial fixture right eliminant vanishes")
        else throw (IO.userError "adversarial fixture left eliminant vanishes")
      else throw (IO.userError "adversarial fixture is not strictly inside the original owner")
    else throw (IO.userError "adversarial fixture imaginary interval is improper")
  else throw (IO.userError "adversarial fixture real interval is improper")

/-- Read the actual retained endpoint widths without printing their large values. -/
private def coordinateBits (box : Box) : Nat :=
  [box.xLower, box.xUpper, box.yLower, box.yUpper].foldl
    (fun prior value => max prior (max (value.num.natAbs.log2 + 1) (value.den.log2 + 1))) 0

/-- Run the single exact request under its explicit producer or saved-only stage policy. -/
private def run (mode : String) (directory : System.FilePath) : IO Unit := do
  unless mode == "produce" || mode == "saved-only" do throw (IO.userError "expected produce or saved-only")
  let savedOnly := mode == "saved-only"
  let input := powerInput ⟨2, by decide⟩ (by decide)
  let elimination := input.elimination
  let current ← adversarial input elimination
  unless 1024 ≤ coordinateBits current.box do throw (IO.userError "adversarial denominator fixture became small")
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := savedOnly }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly }
  let started ← IO.monoMsNow
  let saved ← RawSubdivisionCheckpoint.dyadicResult input elimination
    (.separated columns _ input.nonzero input.degreePositive) winding savedOnly directory current
    (1 / 16) (by decide)
  let result := saved.val
  let policy := CoherentRoot.Accelerated.dyadicTrack input elimination current
  let entry : Track.Observation.CachedRefinement policy :=
    ⟨current, 1 / 16, by decide, result, saved.property⟩
  let hit := Track.Observation.readRefinement policy current (1 / 16) (by decide) [entry]
  unless hit.state = result.state do throw (IO.userError "retained complete refinement cache hit changed")
  let elapsed := (← IO.monoMsNow) - started
  unless decide (result.state.box.StrictInterior current.box) &&
      decide (result.state.box.diagonalSq ≤ (1 / 16 : Fraction.Rational) ^ 2) do
    throw (IO.userError "dyadic fixture strictness or original accuracy failed")
  let snapshot := Json.mkObj
    [("box", toJson (RootStateCheckpoint.boxData result.state.box)),
      ("clearance", toJson (fractionData result.state.clearance.bound)),
      ("ambientLines", toJson ([result.state.ambientLeftClearance.bound, result.state.ambientRightClearance.bound,
        result.state.ambientBottomClearance.bound, result.state.ambientTopClearance.bound].map fractionData))]
  let path := join directory "completed.json"
  if ← path.pathExists then
    let old : Json ← loadJson path
    unless old == snapshot do throw (IO.userError "dyadic fixture completed readbacks changed")
  else if savedOnly then throw (IO.userError "missing dyadic fixture completed readbacks")
  else saveJson path snapshot
  Purelib.System.IO.println ("dyadic-checkpoint-complete mode=" ++ mode ++
    " stateMs=" ++ toString elapsed ++ " inputCoordinateBits=" ++ toString (coordinateBits current.box) ++
    " outputCoordinateBits=" ++ toString (coordinateBits result.state.box) ++
    " strict=true accurate=true original-owner=true")

/-- Interrupt, resume or replay one original raw request through the same checked controller.

The interruption hook runs only after an atomic column or winding save. A
successful continuation retains the full state readbacks at the same source
and accuracy; saved replay requires those exact bytes and all checkpoints.
-/
private def runRaw (mode : String) (directory : System.FilePath) : IO Unit := do
  unless mode == "raw-produce" || mode == "raw-saved-only" || mode == "raw-interrupt" do
    throw (IO.userError "expected raw-produce, raw-saved-only or raw-interrupt")
  let savedOnly := mode == "raw-saved-only"
  let input := powerInput ⟨2, by decide⟩ (by decide)
  let elimination := input.elimination
  let current ← adversarial input elimination
  let afterSave : IO Unit := if mode == "raw-interrupt" then
    throw (IO.userError "raw checkpoint interruption after atomic save") else pure ()
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := savedOnly, afterSave := afterSave }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly, afterSave := afterSave }
  let saved ← RawRefinementCheckpoint.refine input elimination rfl
    (.separated columns _ input.nonzero input.degreePositive) columns winding savedOnly directory
    current.raw (1 / 16) (by decide)
  let result := saved.val
  unless decide (result.state.box.StrictInterior current.box) &&
      decide (result.state.box.diagonalSq ≤ (1 / 16 : Fraction.Rational) ^ 2) do
    throw (IO.userError "raw fixture strictness or original accuracy failed")
  let snapshot := Json.mkObj
    [("box", toJson (RootStateCheckpoint.boxData result.state.box)),
      ("clearance", toJson (fractionData result.state.clearance.bound)),
      ("ambientLines", toJson ([result.state.ambientLeftClearance.bound, result.state.ambientRightClearance.bound,
        result.state.ambientBottomClearance.bound, result.state.ambientTopClearance.bound].map fractionData))]
  let path := join directory "completed-raw.json"
  if ← path.pathExists then
    let old : Json ← loadJson path
    unless old == snapshot do throw (IO.userError "raw fixture completed readbacks changed")
  else if savedOnly then throw (IO.userError "missing raw fixture completed readbacks")
  else saveJson path snapshot
  Purelib.System.IO.println ("raw-dyadic-checkpoint-complete mode=" ++ mode ++
    " inputCoordinateBits=" ++ toString (coordinateBits current.box) ++
    " outputCoordinateBits=" ++ toString (coordinateBits result.state.box) ++
    " strict=true accurate=true original-owner=true")

end TestPurelib.RootIsolation.Checkpoint.Dyadic

/-- Run exactly one adversarial-denominator request under the selected checkpoint policy. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["raw-produce", directory] => TestPurelib.RootIsolation.Checkpoint.Dyadic.runRaw "raw-produce" directory
  | ["raw-saved-only", directory] => TestPurelib.RootIsolation.Checkpoint.Dyadic.runRaw "raw-saved-only" directory
  | ["raw-interrupt", directory] => TestPurelib.RootIsolation.Checkpoint.Dyadic.runRaw "raw-interrupt" directory
  | [mode, directory] => TestPurelib.RootIsolation.Checkpoint.Dyadic.run mode directory
  | _ => throw (IO.userError "expected MODE DIRECTORY")
