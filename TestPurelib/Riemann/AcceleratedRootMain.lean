module

import TestPurelib.RootIsolation.Power
import TestPurelib.Approximation.Gaussian.Acquisition.Expression.Reciprocal
import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
import Purelib.Approximation.Gaussian.Acquisition.Annotated.RootContinuation
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.System.IO
import scripts.checkpoint.CoherentRoot
import Init.Data.Nat.Log2

open TestPurelib.RootIsolation

/-!
# Checked accelerated refinements on original root channels

The positive square and cube roots of two share their checked local fixtures
with the separate dyadic-clearance diagnostic. One actual paid original state
initializes the existing total accelerated track. Its computed nested-root
comparison transports the new algebraic samples to the retained old owner.
-/

namespace TestPurelib.Riemann.AcceleratedRootMain

open Purelib
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
open Purelib.Geometry.Rational
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open TestPurelib.RootIsolation.Power
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open TestPurelib.Approximation.Gaussian.Acquisition.Expression

/-- Force one retained mathematical value through an explicit native IO boundary. -/
@[noinline] private def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- The exact binary width of a natural number, with zero assigned width zero. -/
private def bits (value : Nat) : Nat := if value = 0 then 0 else value.log2 + 1

/-- The actual numerator and denominator bit lengths without rendering their decimal payloads. -/
private def widths (value : Rational) : String :=
  s!"[{bits value.num.natAbs},{bits value.den}]"

/-- Emit and flush one durable measurement before the next refinement starts. -/
private def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Read the requested new states through the same retained comparison and algebraic source.

Only the original cache's index one is paid. An optional checkpoint directory
restores that same state with producers forbidden. The accelerator retains
that state as its initial state, checks bounded rounded-center candidates and
falls back to total winding-one subdivision when none is accepted. Its API
does not report which branch supplied the resulting state.
-/
private def run (label : String) (indices : List Nat)
    {polynomial : CoherentRoot.GaussianPolynomial}
    (input : Input polynomial) (initial : WindingOneState polynomial ambient)
    (initialEq : initial.box = ambient) (acquire : Bool := false)
    (savedOriginal : Option System.FilePath := none) (checkElimination : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  report ("accelerated-start root=" ++ label)
  let elimination := input.elimination
  let retainedElimination := Thunk.mk fun _ =>
    let retained := Input.Elimination.ofCertificate input elimination rfl
    if checkElimination then
      dbg_trace "ORIGINAL_ELIMINATION_CACHE_FORCED"
      retained
    else retained
  let track := Track.Newton.Build.ofInitial
    input.degreeAtLeastTwo input.squarefree elimination initial
  let original := CoherentRoot.certifiedName track input.degreePositive
  if checkElimination then
    match savedOriginal with
    | none => throw (IO.userError "elimination-cache regression requires saved original states")
    | some directory =>
        report "accelerated-original-zero-begin"
        let zero ← CoherentRootCheckpoint.stateAt original input retainedElimination (fun _ _ _ => rfl)
          ⟨true, pure (), false⟩ ⟨true, pure (), none⟩ directory 0
        unless zero.val.box.anchor = initial.box.anchor do
          throw (IO.userError "original state zero lost its unchanged initial reading")
        report "accelerated-original-zero-end"
  let originalFirst ←
    match savedOriginal with
    | none => evaluate fun _ =>
        (⟨original.stateAt 1, rfl⟩ :
          { current : WindingOneState polynomial ambient // current = original.stateAt 1 })
    | some directory => do
        let restored ← CoherentRootCheckpoint.stateAt original input retainedElimination (fun _ _ _ => rfl)
          ⟨true, pure (), false⟩ ⟨true, pure (), none⟩ directory 1
        report ("accelerated-original-reused root=" ++ label ++ " index=1 producers=forbidden")
        pure restored
  let paid := CoherentRoot.Refinement.ofTargetFromState original 1 1 (by decide)
    originalFirst.val originalFirst.property (by
      have contained := CoherentRoot.state_refines_of_le track (Nat.zero_le 1)
      have bound := Box.diagonalSq_le_of_refines contained
      change (CoherentRoot.state track 1).box.diagonalSq ≤ initial.box.diagonalSq at bound
      rewrite [← original.stateAt_eq 1, ← originalFirst.property] at bound
      apply bound.trans_lt
      rewrite [initialEq]
      decide +kernel)
  let bridge := CoherentRoot.Accelerated.ofRefinement input original 0 paid retainedElimination.get
  let annotation := Annotated.ofAccelerated bridge
  match annotation.provenance with
  | some (.algebraic sidecar) =>
    let schedule ← evaluate fun _ => bridge.comparison.compare 0 0 1 (by decide)
    report ("accelerated-paid root=" ++ label ++ " oldIndex=" ++ toString paid.index ++
      " targetSq=1 newComparisonIndices=" ++ toString schedule.leftIndex ++ "/" ++
      toString schedule.rightIndex ++ " elapsedMs=" ++ toString ((← IO.monoMsNow) - started))
    for index in indices do
      report ("accelerated-step-start root=" ++ label ++ " index=" ++ toString index)
      let begin ← IO.monoMsNow
      let current ← evaluate fun _ => bridge.root.stateAt index
      let computed ← IO.monoMsNow
      let sample ← evaluate fun _ => sidecar.residual.source.sample index
      unless sample = current.box.anchor do
        throw (IO.userError "transported sample lost the same retained accelerated root cache")
      report ("{\"root\":\"" ++ label ++ "\",\"index\":" ++ toString index ++
        ",\"stateMs\":" ++ toString (computed - begin) ++
        ",\"totalMs\":" ++ toString ((← IO.monoMsNow) - started) ++
        ",\"transportedSampleChecked\":true,\"clearanceBits\":" ++ widths current.clearance.bound ++
        ",\"xLowerBits\":" ++ widths current.box.xLower ++
        ",\"xUpperBits\":" ++ widths current.box.xUpper ++
        ",\"yLowerBits\":" ++ widths current.box.yLower ++
        ",\"yUpperBits\":" ++ widths current.box.yUpper ++ "}")
    if acquire then
      Reciprocal.check annotation sidecar
    report ("accelerated-complete root=" ++ label ++ " newStates=" ++ toString indices.length ++
      " oldStates=1 elapsedMs=" ++ toString ((← IO.monoMsNow) - started))
  | _ => throw (IO.userError "the accelerated annotation lost its actual algebraic source")

end TestPurelib.Riemann.AcceleratedRootMain

open TestPurelib.Riemann

/-- Measure only the selected finite root prefix without scheduling another case. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["--sqrt2-one"] =>
      AcceleratedRootMain.run "sqrt2" [1]
        (Power.powerInput ⟨2, by decide⟩ (by decide))
        Power.squareInitial Power.squareInitial_box
  | ["--sqrt2-seven"] =>
      AcceleratedRootMain.run "sqrt2" [1, 2, 3, 4, 5, 6, 7]
        (Power.powerInput ⟨2, by decide⟩ (by decide))
        Power.squareInitial Power.squareInitial_box
  | ["--cbrt2-seven"] =>
      AcceleratedRootMain.run "cbrt2" [1, 2, 3, 4, 5, 6, 7]
        (Power.powerInput ⟨3, by decide⟩ (by decide))
        Power.cubeInitial Power.cubeInitial_box
  | ["--cbrt2-seven-acquire"] =>
      AcceleratedRootMain.run "cbrt2" [1, 2, 3, 4, 5, 6, 7]
        (Power.powerInput ⟨3, by decide⟩ (by decide))
        Power.cubeInitial Power.cubeInitial_box true
  | ["--cbrt2-seven-acquire", directory] =>
      AcceleratedRootMain.run "cbrt2" [1, 2, 3, 4, 5, 6, 7]
        (Power.powerInput ⟨3, by decide⟩ (by decide))
        Power.cubeInitial Power.cubeInitial_box true (some (System.FilePath.mk directory))
  | ["--cbrt2-seven-acquire-cache", directory] =>
      AcceleratedRootMain.run "cbrt2" [1, 2, 3, 4, 5, 6, 7]
        (Power.powerInput ⟨3, by decide⟩ (by decide))
        Power.cubeInitial Power.cubeInitial_box true (some (System.FilePath.mk directory)) true
  | _ => throw (IO.userError
      "expected --sqrt2-one, --sqrt2-seven, --cbrt2-seven, --cbrt2-seven-acquire [SAVED_ORIGINAL_DIRECTORY] or \
        --cbrt2-seven-acquire-cache SAVED_ORIGINAL_DIRECTORY")
