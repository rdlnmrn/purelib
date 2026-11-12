module

import scripts.checkpoint.Multiplicity
-- The complete former-action verifier reduces the original unexposed prefix body.
import all scripts.checkpoint.RawSubdivision
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Dense.Gaussian.Unit
import Purelib.System.IO
import Purelib.System.FilePath

/-! # Original multiplicity-source replay through exact finite branches -/

namespace TestPurelib.RootIsolation.Checkpoint.Multiplicity

open Purelib.Riemann.RootContinuation

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Multiplicity

section

open Purelib
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open RawSubdivisionCheckpoint (refine)
open Purelib.System.FilePath (join)

variable {p : CoefficientPolynomial} {ambient : Box}

/-- The complete former root-prefix action used only for a quantified default regression.

This verifier retains the bound original loop before the supplied-cache API.
Production uses only the original amended checkpoint operation.
-/
private def formerRootPrefix
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat) : IO (List (CoherentRoot.StateCache.Entry track)) := do
  let rec restore : (remaining index : Nat) → (current : State.WindingOne.Basic.WindingOneState p ambient) →
      current = CoherentRoot.state track index →
      IO (List (CoherentRoot.StateCache.Entry track))
    | 0, _, _, _ => pure []
    | remaining + 1, index, current, currentEq => do
        let entry := CoherentRoot.StateCache.Entry.ofState track index current currentEq
        match remaining with
        | 0 => pure [entry]
        | _ + 1 =>
            let epsilon := Data.Rat.Bounds.AccuracyRadius.accuracyRadius
              (CoherentRoot.stepTarget track index)
            let positive := Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos
              (CoherentRoot.stepTarget_positive track index)
            let next ← refine input input.elimination rfl loader columns winding
              (join directory s!"state-{index + 1}") current epsilon positive
            have nextEq : next.val = CoherentRoot.state track (index + 1) :=
              next.property.trans ((refinement current epsilon positive).symm.trans
                (congrArg (fun state => track.refine state epsilon positive) currentEq))
            let tail ← restore remaining (index + 1) next.val nextEq
            pure (entry :: tail)
  restore count 0 track.initial rfl

/-- The absent cache preserves the complete former action at every original input and count. -/
private theorem rootPrefix_default
    (input : FTA.Squarefree.Input p)
    (loader : RootRefinementCheckpoint.ClearanceLoader input.elimination (.canonical input.elimination) IO)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (track : Track.Basic.WindingOneTrack p ambient)
    (refinement : ∀ current epsilon positive, track.refine current epsilon positive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive)
    (count : Nat) :
    RawSubdivisionCheckpoint.rootPrefix input loader columns winding directory track refinement count none =
      formerRootPrefix input loader columns winding directory track refinement count := by
  unfold RawSubdivisionCheckpoint.rootPrefix formerRootPrefix
  delta RawSubdivisionCheckpoint.rootPrefix.restore formerRootPrefix.restore
  rfl

end

/-- Check the retained original root-site count, multiplicity and actual exact numerical readings. -/
private def checkRoots (source : CoefficientPolynomial) (multiplicity count : Nat)
    (directory : System.FilePath) (retain : Bool := false) : IO Unit := do
  let saved ← MultiplicityCheckpoint.polynomial source
    { savedOnly := true } { savedOnly := true } { savedOnly := true } directory none retain
  match MultiplicityCheckpoint.Retained.value retain saved with
  | .zeroNumerator _ _ => throw (IO.userError "nonzero source replay returned a zero numerator")
  | .nonzero result =>
      let indices := CCL.Polynomial.Index.NonzeroResult.rootIndices result
      unless indices.length = count do
        throw (IO.userError "original replay lost or duplicated a root site")
      for index in indices do
        let admission := CCL.Polynomial.Admission.ofResult result index
        unless admission.multiplicity = multiplicity do
          throw (IO.userError "original replay lost source multiplicity")
        let numerical := admission.numericalResidual
        unless numerical.2.source.sample 0 = 2 ∧ numerical.2.source.sample 3 = 2 do
          throw (IO.userError "original replay replaced exact root readings")

/-- Execute zero, constant, linear and repeated-linear original polynomial-source branches with generators prohibited.

The linear and repeated source retain one geometric site and their distinct
source multiplicities. Both original numerical caches read their same exact
root at separate sample indices. Enabled retained views exercise the same
branches and complete original cache hierarchy. No higher isolation is supplied.
-/
public def check (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then
    throw (IO.userError "multiplicity replay self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let zero ← MultiplicityCheckpoint.polynomial 0
    { savedOnly := true } { savedOnly := true } { savedOnly := true }
    (Purelib.System.FilePath.join directory "zero")
  match zero.val with
  | .zeroNumerator _ _ => pure ()
  | .nonzero _ => throw (IO.userError "zero source replay lost its explicit zero outcome")
  checkRoots Dense.Gaussian.Unit.unitDenominator 0 0 (Purelib.System.FilePath.join directory "constant")
  let linear := Power.Gaussian.rootPolynomial 2 ⟨1, by decide⟩
  checkRoots linear 1 1 (Purelib.System.FilePath.join directory "linear")
  checkRoots (linear * linear) 2 1 (Purelib.System.FilePath.join directory "repeated")
  let retainedZero ← MultiplicityCheckpoint.polynomial 0
    { savedOnly := true } { savedOnly := true } { savedOnly := true }
    (Purelib.System.FilePath.join directory "retained-zero") none true
  match retainedZero.val.1 with
  | .zeroNumerator _ _ => pure ()
  | .nonzero _ => throw (IO.userError "retained zero source replay lost its explicit zero outcome")
  checkRoots Dense.Gaussian.Unit.unitDenominator 0 0
    (Purelib.System.FilePath.join directory "retained-constant") true
  checkRoots linear 1 1 (Purelib.System.FilePath.join directory "retained-linear") true
  checkRoots (linear * linear) 2 1 (Purelib.System.FilePath.join directory "retained-repeated") true
  Purelib.System.IO.println
    "original default/retained zero/constant/linear/repeated CCL replay and numerical cache readings passed"

end TestPurelib.RootIsolation.Checkpoint.Multiplicity
