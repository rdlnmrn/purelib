module

import TestPurelib.RootIsolation.Power
import scripts.checkpoint.RawSubdivision
import TestPurelib.RootIsolation.Subdivision.Lines
import Purelib.System.IO
import Purelib.System.FilePath

/-!
# Atomic saved-column and winding replay for the subdivision policy

A single square-root request uses the original local fixture and epsilon one
sixteenth. The explicit modes interrupt only after an atomic column or winding
save, resume the same exact request, and replay its completed tree saved-only.
-/

namespace TestPurelib.RootIsolation.Checkpoint.Subdivision

open Purelib
open Purelib.RootIsolation
open Purelib.Geometry.Rational
open IntegrationCheckpoint
open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open Purelib.System.FilePath (join)
open TestPurelib.RootIsolation.Power

/-- Run the selected short checkpoint phase against its explicit private fixture directory. -/
private def run (mode : String) (directory : System.FilePath) : IO Unit := do
  unless ["interrupt-column", "interrupt-winding", "resume", "saved-only"].contains mode do
    throw (IO.userError "unknown subdivision checkpoint mode")
  let savedOnly := mode == "saved-only"
  let input := powerInput ⟨2, by decide⟩ (by decide)
  let elimination := input.elimination
  let columns : ClearanceCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if mode == "interrupt-column" then
        throw (IO.userError "subdivision regression interrupted after atomic column save") else pure () }
  let winding : WindingCheckpoint.Control IO :=
    { savedOnly := savedOnly
      afterSave := if mode == "interrupt-winding" then
        throw (IO.userError "subdivision regression interrupted after atomic winding save") else pure () }
  Purelib.System.IO.println ("subdivision-checkpoint-start mode=" ++ mode)
  let saved ← RawSubdivisionCheckpoint.subdivisionResult input elimination
    (.separated columns _ input.nonzero input.degreePositive) winding savedOnly directory squareInitial
    (1 / 16) (by decide)
  let current := saved.val.state
  unless decide (current.box.StrictInterior squareInitial.box) &&
      decide (current.box.diagonalSq ≤ (1 / 16 : Data.Rat.Fraction.Rational) ^ 2) &&
      saved.val.steps == saved.val.trace.length do
    throw (IO.userError "subdivision strict/accuracy/trace readback failed")
  let result := Json.mkObj
    [("box", toJson (RootStateCheckpoint.boxData current.box)),
      ("clearance", toJson (fractionData current.clearance.bound)),
      ("ambientLines", toJson ([current.ambientLeftClearance.bound, current.ambientRightClearance.bound,
        current.ambientBottomClearance.bound, current.ambientTopClearance.bound].map fractionData)),
      ("steps", toJson saved.val.steps),
      ("depthBound", toJson (Subdivision.WindingOne.depthBound squareInitial (1 / 16)))]
  let path := join directory "completed.json"
  if ← path.pathExists then
    let expected : Json ← loadJson path
    unless expected == result do throw (IO.userError "saved subdivision result changed")
  else if savedOnly then
    throw (IO.userError "missing completed regression result")
  else saveJson path result
  Purelib.System.IO.println ("subdivision-checkpoint-complete mode=" ++ mode ++
    " steps=" ++ toString saved.val.steps ++ " strict=true accurate=true trace=true")

end TestPurelib.RootIsolation.Checkpoint.Subdivision

/-- Exercise exactly the requested short checkpoint mode on one explicit fixture directory. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | [mode, directory] => TestPurelib.RootIsolation.Checkpoint.Subdivision.run mode directory
  | _ => throw (IO.userError "expected MODE DIRECTORY")
