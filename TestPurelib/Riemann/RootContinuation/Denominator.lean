module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

namespace TestPurelib.Riemann.RootContinuation.Denominator

open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm

section

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}
    (piece : InteriorStep step index source target) (time : Purelib.Data.Rat.Fraction.Rational)
    (inside : InteriorStep.Inside time)

/-- The complete cached track view reads back the actual supplied original root cache. -/
example : (pointAt piece time inside).originalRoot = (piece.caches time inside).original :=
  (pointAt piece time inside).originalRoot_eq

/-- Canonical construction still retains the exact original numerical root. -/
example : (pointAt piece time inside).root = (piece.caches time inside).root :=
  Point.pointAt_root piece time inside

/-- A different certified point program uses one same actual root for its geometry and polynomial channel. -/
example (cache : { value : InteriorStep.Cached piece.bridge.val piece.inputs time inside //
      value = piece.caches time inside }) (program : InteriorStep.Cached.Program cache.val) :
    (Point.ofProgram cache program).atom.channel = program.root.value := rfl

/-- Any supplied point program preserves containment of every actual sample in the original bridge. -/
example (cache : { value : InteriorStep.Cached piece.bridge.val piece.inputs time inside //
      value = piece.caches time inside }) (program : InteriorStep.Cached.Program cache.val) (stage : Nat) :
    piece.bridge.val.box.Contains ((Point.ofProgram cache program).root.geometric.sample stage) :=
  (Point.ofProgram cache program).sample_inside stage

/-- Supplied regularity and elimination caches preserve the entire canonical point record. -/
example
    (input : { value : Purelib.RootIsolation.FTA.Squarefree.Input (piece.bridge.val.connection.polynomialAt time) //
      value = piece.inputs time inside })
    (elimination : Purelib.RootIsolation.FTA.Squarefree.Input.Elimination input.val) :
    InteriorStep.Cached.buildWithElimination piece.bridge.val piece.inputs time inside input elimination =
      InteriorStep.Cached.build piece.bridge.val piece.inputs time inside :=
  InteriorStep.Cached.buildWithElimination_eq piece.bridge.val piece.inputs time inside input elimination

/-- Configured point construction uses the same retained actual program for the arithmetic channel. -/
example : (pointFromProgram piece time inside).root.value = (piece.programs time inside).root.value :=
  Point.pointFromProgram_value piece time inside

/-- Configured point samples retain the original bridge containment at every sample index. -/
example (stage : Nat) :
    piece.bridge.val.box.Contains ((pointFromProgram piece time inside).root.geometric.sample stage) :=
  (pointFromProgram piece time inside).sample_inside stage

/-- The root reciprocal's bound is derived from actual cache containment in the original bridge box. -/
example (clearance : Box.OutsideSide.Prepared piece.bridge.val.box Kind.root.pole) (stage : Nat) :
    clearance.margin ≤ Basic.normSq ((pointAt piece time inside).root.geometric.sample stage) :=
  (pointAt piece time inside).lower .root clearance stage

/-- The ordered one-plus-root denominator gets its bound from that same original box and its pole at minus one. -/
example (clearance : Box.OutsideSide.Prepared piece.bridge.val.box Kind.oneAddRoot.pole) (stage : Nat) :
    clearance.margin ≤ Basic.normSq (1 + (pointAt piece time inside).root.geometric.sample stage) :=
  (pointAt piece time inside).lower .oneAddRoot clearance stage

/-- The literal root reciprocal retains the actual original denominator and computed residual cache. -/
example (clearance : Box.OutsideSide.Prepared piece.bridge.val.box Kind.root.pole) :
    let inverse := (pointAt piece time inside).prepare .root clearance
    inverse.cache.input = ((pointAt piece time inside).completed Kind.root).sidecar.residual :=
  ((pointAt piece time inside).prepare .root clearance).cache.input_eq

/-- The ordered affine reciprocal pays exactly half the computed original coordinate margin. -/
example (clearance : Box.OutsideSide.Prepared piece.bridge.val.box Kind.oneAddRoot.pole) :
    ((pointAt piece time inside).prepare .oneAddRoot clearance).paid.target = clearance.margin / 2 :=
  ((pointAt piece time inside).prepare .oneAddRoot clearance).paid.target_eq

/-- The exact-zero obstruction is the existing invalid inverse on the same retained original completed child. -/
example (kind : Kind) (pole : Pole (pointAt piece time inside) kind) :
    pole.invalid.denominator.2.1 = pole.child.toResult := rfl

end

/-- A small retained box excludes both rational pole points by original coordinate gaps. -/
private def separatedBox : Box := ⟨2, 4, -1, 1, by decide +kernel, by decide +kernel⟩

/-- The original bounded environment retains the exact numerical atom used by the arithmetic regression. -/
private def environment : Fin 1 → Annotated := fun _ => Annotated.rational 3

/-- One original admitted atom provides a cheap actual residual for native reciprocal cache checks. -/
private def originalAtom : Checked.Completed environment (.atom Point.atomIndex) :=
  Checked.Completed.atom environment Point.atomIndex (Algebraic.Sidecar.ofRational (RationalSidecar.exact 3))

/-- The displayed constant sample belongs to the retained separated box. -/
private theorem sample_inside (stage : Nat) :
    separatedBox.Contains ((GeometricApproximation.exact 3).sample stage) := by
  change separatedBox.Contains (3 : Canonical)
  decide +kernel

/-- Exercise both actual ordered arithmetic channels and their paid original residual reciprocal caches. -/
private def checkKind (kind : Kind) (expected : Canonical) : IO Unit := do
  match Box.inspectPoint separatedBox kind.pole with
  | .inconclusive _ => throw (IO.userError "The retained box must exclude both displayed rational poles")
  | .apart clearance =>
      let source := kind.samples (GeometricApproximation.exact 3)
      let child := kind.complete originalAtom
      let equivalent := kind.agrees originalAtom (GeometricApproximation.exact 3)
        (Purelib.Polynomial.Approximation.CoherentEvaluation.exact_agrees 3)
      have lower : ∀ stage, clearance.margin ≤ Basic.normSq (source.sample stage) := by
        intro stage
        rewrite [kind.sample_norm]
        exact clearance.lower (sample_inside stage)
      let inverse := Checked.Geometric.fromLower child source equivalent
        (Refinement.State.initial (Geometric.Preparation.sampledChannel source))
        clearance.margin clearance.positive lower
      unless inverse.source.sample 0 == expected && inverse.paid.selection.stage == 0 &&
          inverse.paid.target == clearance.margin / 2 && inverse.cache.tail.sample 0 == expected &&
          inverse.cache.result.sample 0 == expected⁻¹ do
        throw (IO.userError "The retained actual denominator/payment/reciprocal cache changed")

/-- Check the two spatial reciprocal routes and the distinct finite-inconclusive condition. -/
public def check : IO Unit := do
  checkKind .root 3
  checkKind .oneAddRoot 4
  let coarse : Box := ⟨-1, 1, -1, 1, by decide +kernel, by decide +kernel⟩
  match Box.inspectPoint coarse 0 with
  | .inconclusive _ => pure ()
  | .apart _ => throw (IO.userError "Containment of zero must remain only spatial inconclusivity")
  Purelib.System.IO.println
    "Root and ordered one-plus-root spatial denominators: retained payments and inverse caches passed"

end TestPurelib.Riemann.RootContinuation.Denominator
