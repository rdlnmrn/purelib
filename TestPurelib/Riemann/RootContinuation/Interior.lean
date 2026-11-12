module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Interior
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction

namespace TestPurelib.Riemann.RootContinuation.Interior

open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat.Fraction (Rational)

section

variable {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : InteriorStep.Inputs bridge.val) (caches : InteriorStep.Caches bridge.val inputs)
    (left : NamedEquivalent (caches 0 InteriorStep.zero_inside).root.value.name source.certificate.value.name)
    (right : NamedEquivalent (caches 1 InteriorStep.one_inside).root.value.name target.certificate.value.name)
    (tail : Trace.Interior rest)

/-- A complete genuine step/family construction consumes the exact supplied parameter cache. -/
example (time : Rational) (inside : InteriorStep.Inside time) :
    (Trace.Interior.ofStep (InteriorStep.ofCaches source target bridge inputs caches left right) tail).first.caches
      time inside = caches time inside := rfl

/-- The supplied parameter cache's samples remain in the complete original selected bridge box. -/
example (time : Rational) (inside : InteriorStep.Inside time) (stage : Nat) :
    (step.bridge index).box.Contains ((caches time inside).root.approximation.sample stage) := by
  have contained :=
    (InteriorStep.ofCaches source target bridge inputs caches left right).sample_inside time inside stage
  exact (congrArg (fun box => box.Contains ((caches time inside).root.approximation.sample stage))
    (congrArg OwnerBridge.box bridge.property)).mp contained

/-- A genuine step/family construction retains its complete actual remaining family. -/
example :
    (Trace.Interior.ofStep (InteriorStep.ofCaches source target bridge inputs caches left right) tail).remaining =
      tail :=
  Trace.Interior.ofStep_remaining _ _

/-- Same-parameter handoffs remain the actual supplied comparison records. -/
example : (InteriorStep.ofCaches source target bridge inputs caches left right).left = left := rfl

end

section

open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.RootIsolation
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)

variable {left right : GaussianPolynomial} {bridge : OwnerBridge left right}
    {inputs : InteriorStep.Inputs bridge} {time : Rational} {inside : InteriorStep.Inside time}
    (input : FTA.Squarefree.Input (bridge.connection.polynomialAt time)) (inputEq : input = inputs time inside)
    (owner : LocalOwner (bridge.connection.polynomialAt time)) (ownerEq : owner = bridge.ownerAt time inside)
    (track : WindingOneTrack (bridge.connection.polynomialAt time) owner.box)
    (trackEq : track = owner.track input.degreeAtLeastTwo input.squarefree)
    (root : CertifiedName track)
    (elimination : FTA.Squarefree.Input.Elimination input)

/-- The genuine cache constructor retains the complete actual track already used by its root producer. -/
example : (InteriorStep.Cached.ofRoot (bridge.connection.polynomialAt time) rfl
    input inputEq owner ownerEq track trackEq root elimination).track.val = track := rfl

/-- The genuine cache constructor retains the complete actual certified root rather than rebuilding its program. -/
example : (InteriorStep.Cached.ofRoot (bridge.connection.polynomialAt time) rfl
    input inputEq owner ownerEq track trackEq root elimination).root = root := rfl

/-- The genuine cache constructor retains the original regularity input already used by the same track. -/
example : (InteriorStep.Cached.ofRoot (bridge.connection.polynomialAt time) rfl
    input inputEq owner ownerEq track trackEq root elimination).input = input := rfl

/-- The cache constructor retains the exact supplied elimination value without calling its producer. -/
example : (InteriorStep.Cached.ofRoot (bridge.connection.polynomialAt time) rfl
    input inputEq owner ownerEq track trackEq root elimination).elimination = elimination := rfl

end

section

variable {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
    {bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index }}
    {inputs : InteriorStep.Inputs bridge.val} {caches : InteriorStep.Caches bridge.val inputs}
    (handoffs : InteriorStep.Handoffs step index source target bridge inputs caches)

/-- The prepared adapter preserves the complete original source cache, including its literal ambient and track. -/
example : handoffs.interior.source = source := handoffs.source_eq

/-- The selected target remains its independent complete original cache. -/
example : handoffs.interior.target = target := handoffs.target_eq

/-- The actual original selected bridge and regularity input family remain unchanged. -/
example : handoffs.interior.bridge = bridge ∧ handoffs.interior.inputs = inputs := ⟨rfl, rfl⟩

/-- Zero-parameter interpretation consumes the actual retained endpoint cache without a second family call. -/
example : handoffs.interior.caches 0 InteriorStep.zero_inside = handoffs.initial.val := handoffs.caches_zero

/-- Unit-parameter interpretation consumes the actual retained endpoint cache without a second family call. -/
example : handoffs.interior.caches 1 InteriorStep.one_inside = handoffs.terminal.val := handoffs.caches_one

/-- The zero-endpoint program is the complete retained object used by protection, not a rebuilt root. -/
example : handoffs.interior.programs 0 InteriorStep.zero_inside =
    (show InteriorStep.Cached.Program (handoffs.caches 0 InteriorStep.zero_inside) from
      handoffs.caches_zero.symm ▸ handoffs.initialProgram) := handoffs.programs_zero

/-- The unit-endpoint program is the complete retained object used by protection. -/
example : handoffs.interior.programs 1 InteriorStep.one_inside =
    (show InteriorStep.Cached.Program (handoffs.caches 1 InteriorStep.one_inside) from
      handoffs.caches_one.symm ▸ handoffs.terminalProgram) := handoffs.programs_one

/-- Every rational parameter preserves the complete original cache by scalar readback alone. -/
example (time : Rational) (inside : InteriorStep.Inside time) :
    handoffs.interior.caches time inside = caches time inside := handoffs.caches_eq time inside

/-- The initial protected region retains the exact original point root state used by its comparison. -/
example : handoffs.leftRegion.current = handoffs.initialProgram.root.stateAt handoffs.leftRegion.index :=
  handoffs.leftRegion.current_eq

/-- The terminal protected region retains the exact independent target point state used by its comparison. -/
example : handoffs.rightRegion.current = handoffs.terminalProgram.root.stateAt handoffs.rightRegion.index :=
  handoffs.rightRegion.current_eq

/-- The source handoff retains containment in its literal original owner across distinct ambients. -/
example : handoffs.leftRegion.current.box.Refines handoffs.source.track.initial.box := handoffs.left_nested

/-- The target handoff retains containment in its own literal selected target owner. -/
example : handoffs.rightRegion.current.box.Refines handoffs.target.track.initial.box := handoffs.right_nested

/-- Every pointwise original sample remains inside the same original selected bridge. -/
example (time : Rational) (inside : InteriorStep.Inside time) (stage : Nat) :
    bridge.val.box.Contains ((handoffs.interior.caches time inside).root.approximation.sample stage) :=
  handoffs.interior.sample_inside time inside stage

/-- Extending the original trace retains its actual complete remaining family and the original endpoint cache. -/
example (tail : Trace.Interior rest) :
    (Trace.Interior.ofStep handoffs.interior tail).remaining = tail ∧
      (Trace.Interior.ofStep handoffs.interior tail).first.caches 1 InteriorStep.one_inside = handoffs.terminal.val :=
  ⟨Trace.Interior.ofStep_remaining _ _, handoffs.caches_one⟩

/-- Preparing the adapter authenticates its actual retained zero-parameter cache against the original callback. -/
example (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : InteriorStep.Inputs bridge.val) (caches : InteriorStep.Caches bridge.val inputs) :
    let actual := InteriorStep.Handoffs.ofCaches source target bridge inputs caches
    actual.initial.val = caches 0 InteriorStep.zero_inside := by
  let actual := InteriorStep.Handoffs.ofCaches source target bridge inputs caches
  exact actual.initial.property.trans
    (congrArg (fun family : InteriorStep.Caches bridge.val inputs => family 0 InteriorStep.zero_inside)
      actual.original_eq)

end

section

variable {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source)

/-- A missing-family request retains the complete original trace and source cache for retry. -/
example : Trace.acquireInterior trace none =
    Trace.InteriorOutcome.requested ⟨trace, rfl, source, rfl, rfl⟩ := rfl

/-- Supplying genuine evidence on the retained original trace resumes without building another numerical trace. -/
example (interior : Trace.Interior trace) :
    (Trace.InteriorRequest.resume
      (⟨trace, rfl, source, rfl, rfl⟩ : Trace.InteriorRequest trace none) interior).original = trace :=
  interior.original_eq

end

end TestPurelib.Riemann.RootContinuation.Interior
