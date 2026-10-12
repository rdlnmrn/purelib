module

public import Purelib.Data.CCL.Encoding.Prefix.Enclosure
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Input
public import Purelib.Geometry.CCL.Parser.Formula.Input
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Neighborhood
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Proper rational placement of one exact raw CCL bit

Both incremental child formulas use the original cached inverse matrix.
A finite regular sample avoids their boundaries and the actual terminal
inputs. Its retained signed neighbourhood admits one unique next bit
uniformly, so the exact exposed word extends without a terminal convention
change or a new assumed realization.
-/

public section

namespace Purelib.Geometry.CCL.Prefix

open Purelib.Data
open Purelib.Data.CCL
open Purelib.Geometry
open Purelib.Geometry.Projective
open Purelib.Geometry.Projective.Hermitian.Formula

namespace ChildForms

/-- Collect the original child atom forms and exact input-distance guards in their retained order.

The initial guard excludes the zero input. The two original child lists
preserve all atom occurrences, and every displayed terminal input contributes
its own squared-distance guard.
-/
@[expose] def guardForms (falseFormula trueFormula : BoundaryFormula)
    (terminalInputs : List Gaussian.Basic.Canonical) : List Hermitian.HermitianForm :=
  Hermitian.distanceSqForm 0 ::
    ((falseFormula.atoms.map (fun atom => atom.form) ++ trueFormula.atoms.map (fun atom => atom.form)) ++
      terminalInputs.map Hermitian.distanceSqForm)

end ChildForms

set_option genInjectivity false in
/-- Retain both exact incremental child formulas and their finite input-guard family for one original prefix enclosure.

The original inverse-matrix cache is used directly in both pullbacks. The
actual terminal-image list, original atom occurrences and distance guards
are cached before sampling or sign-clearance preparation begins.
-/
structure ChildForms (previous : Encoding.Prefix.Enclosure) where
  /-- The cached false-child formula in the original input coordinate. -/ falseFormula : BoundaryFormula
  /-- The false-child pullback consumes the exact original inverse cache. -/ falseSpec :
    falseFormula = (Parser.Formula.incrementalAdvanceFormula previous.state false).pullback previous.inverseMatrix
  /-- The cached true-child formula in the original input coordinate. -/ trueFormula : BoundaryFormula
  /-- The true-child pullback consumes the exact original inverse cache. -/ trueSpec :
    trueFormula = (Parser.Formula.incrementalAdvanceFormula previous.state true).pullback previous.inverseMatrix
  /-- The exact finite terminal-input images computed from the original state. -/ terminalInputs :
    List Gaussian.Basic.Canonical
  /-- The terminal-input cache belongs to the same retained parser state. -/ terminalSpec :
    terminalInputs = Encoding.Parser.Terminal.inputs previous.state
  /-- The actual ordered family of child forms and input guards. -/ forms : List Hermitian.HermitianForm
  /-- The guard family uses the original cached child formulas and terminal inputs. -/ formsSpec :
    forms = ChildForms.guardForms falseFormula trueFormula terminalInputs

namespace ChildForms

/-- Compute both child pullbacks once using the exact retained inverse chart and cache their original input guards. -/
def ofEnclosure (previous : Encoding.Prefix.Enclosure) : ChildForms previous := by
  let falseFormula := (Parser.Formula.incrementalAdvanceFormula previous.state false).pullback previous.inverseMatrix
  let trueFormula := (Parser.Formula.incrementalAdvanceFormula previous.state true).pullback previous.inverseMatrix
  let terminalInputs := Encoding.Parser.Terminal.inputs previous.state
  exact ⟨falseFormula, rfl, trueFormula, rfl, terminalInputs, rfl,
    guardForms falseFormula trueFormula terminalInputs, rfl⟩

/-- Read the actual cached formula for the supplied Boolean child. -/
@[expose] def atBit {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous) (bit : Bool) :
    BoundaryFormula := if bit then children.trueFormula else children.falseFormula

/-- The selected cached formula agrees with the original incremental input predicate at that same Boolean. -/
theorem atBit_spec {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous) (bit : Bool) :
    children.atBit bit = Parser.Formula.inputIncrementalAdvanceFormula previous.state bit := by
  cases bit with
  | false =>
      exact children.falseSpec.trans
        (congrArg (fun matrix =>
          (Parser.Formula.incrementalAdvanceFormula previous.state false).pullback matrix) previous.inverseSpec)
  | true =>
      exact children.trueSpec.trans
        (congrArg (fun matrix =>
          (Parser.Formula.incrementalAdvanceFormula previous.state true).pullback matrix) previous.inverseSpec)

/-- Every original atom of either cached child keeps its same form occurrence in the actual guard family. -/
theorem formMember {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous) (bit : Bool)
    (atom : Hermitian.Atom) (member : atom ∈ (children.atBit bit).atoms) : atom.form ∈ children.forms := by
  have mapped : atom.form ∈ (children.atBit bit).atoms.map (fun entry => entry.form) :=
    List.Map.mem_map_of_mem (f := fun entry => entry.form) member
  rewrite [children.formsSpec]
  apply List.Mem.tail
  apply List.Membership.mem_append.mpr
  left
  apply List.Membership.mem_append.mpr
  cases bit with
  | false => exact Or.inl mapped
  | true => exact Or.inr mapped

/-- The original zero-input guard occurs in the actual retained family. -/
theorem zeroFormMember {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous) :
    Hermitian.distanceSqForm 0 ∈ children.forms := by
  rewrite [children.formsSpec]
  exact List.Mem.head _

/-- Every actual cached terminal input keeps its original squared-distance guard in the family. -/
theorem terminalFormMember {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous)
    (input : Gaussian.Basic.Canonical) (member : input ∈ children.terminalInputs) :
    Hermitian.distanceSqForm input ∈ children.forms := by
  rewrite [children.formsSpec]
  exact List.Mem.tail _ (List.Membership.mem_append.mpr
    (Or.inr (List.Map.mem_map_of_mem (f := Hermitian.distanceSqForm) member)))

/-- A regular sample of the exact guard family excludes every terminal input of the same original state. -/
theorem terminalExcluded {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous)
    (sample : Hermitian.Box.Sample children.forms previous.box) :
    sample.point ∉ Encoding.Parser.Terminal.inputs previous.state := by
  intro member
  have cachedMember : sample.point ∈ children.terminalInputs := children.terminalSpec.symm ▸ member
  exact sample.ne_center sample.point (children.terminalFormMember sample.point cachedMember) rfl

/-- The cached child predicate exactly characterizes admissibility of its original next bit.

The point lies in the retained earlier enclosure, whose full representation
supplies every earlier history and active-phase condition.
-/
theorem canStep_iff {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous)
    (bit : Bool) {point : Gaussian.Basic.Canonical} (inside : previous.box.Contains point) :
    (children.atBit bit).Holds point ↔ Encoding.Parser.Semantics.Prefix.CanStep previous.state point bit := by
  have original := Parser.Formula.inputIncrementalAdvanceFormula_canStep_iff previous.state point
    (previous.tail point) previous.determinant (previous.tail_represents inside) bit
  constructor
  · intro holds
    exact original.mp (children.atBit_spec bit ▸ holds)
  · intro possible
    exact (children.atBit_spec bit).symm ▸ original.mpr possible

/-- Certify either original child formula on one exact signed neighbourhood of the retained guard family. -/
def stableAt {previous : Encoding.Prefix.Enclosure} (children : ChildForms previous)
    (signs : Hermitian.Box.SignNeighborhood children.forms previous.box) (bit : Bool) :
    Hermitian.Formula.Box.Stable previous.box signs.box (children.atBit bit) :=
  Hermitian.Formula.Box.Stable.ofAtoms (children.atBit bit) fun atom member =>
    (signs.formStability atom.form (children.formMember bit atom member)).toAtom

end ChildForms

set_option genInjectivity false in
/-- Retain one computed proper-box extension of an exact original raw CCL prefix.

The original child formulas, regular sample, sign clearances and affine tail
are cached. One original local decision selects a unique next bit, and the
exact prefix-extension builder consumes the resulting uniform certificate
on that same strictly nested box.
-/
structure Step (previous : Encoding.Prefix.Enclosure) where
  /-- The original cached children and finite terminal-input guard family. -/ children : ChildForms previous
  /-- The actual retained proper sign neighbourhood and its exact sampling caches. -/ signs :
    Hermitian.Box.SignNeighborhood children.forms previous.box
  /-- The exact affine tail computed from the earlier inverse-matrix cache. -/ sampleTail : Gaussian.Basic.Canonical
  /-- The tail uses the same actual retained sample and original inverse chart. -/ sampleTailSpec :
    sampleTail = previous.tail signs.sample.point
  /-- The cached affine tail satisfies the complete original representation. -/ sampleRepresents :
    Encoding.Parser.Semantics.State.Represents previous.state signs.sample.point sampleTail
  /-- The actual sample excludes all original terminal-input candidates. -/ terminalExcluded :
    signs.sample.point ∉ Encoding.Parser.Terminal.inputs previous.state
  /-- The actual unique admissible bit at the original represented sample. -/ choice :
    Encoding.Parser.Next.AdmissibleBit previous.state signs.sample.point
  /-- The original false-child formula is stable throughout the computed box. -/ falseStable :
    Hermitian.Formula.Box.Stable previous.box signs.box children.falseFormula
  /-- The original true-child formula is stable throughout the computed box. -/ trueStable :
    Hermitian.Formula.Box.Stable previous.box signs.box children.trueFormula
  /-- Every point of the actual computed box admits this same selected next bit. -/ uniformStep :
    ∀ point, signs.box.Contains point → Encoding.Parser.Semantics.Prefix.CanStep previous.state point choice.bit
  /-- The actual retained exact-word extension on the same computed box. -/ extension :
    Encoding.Prefix.Enclosure.BitExtension previous signs.box
  /-- The extension is the original builder applied to these same retained data and certificates. -/ extensionSpec :
    extension = previous.appendWithBox choice.bit signs.box signs.proper signs.nested uniformStep

namespace Step

/-- Compute one proper nested enclosure extending the exact retained raw prefix by its actual unique next bit.

The original inverse chart is reused in both child pullbacks and sample-tail
readback. Finite polynomial sampling excludes the exact terminal inputs;
the retained sign-clearance minimum supplies the proper box on which the
selected child remains admissible. No extension certificate is assumed.
-/
def build (previous : Encoding.Prefix.Enclosure) : Step previous := by
  let children := ChildForms.ofEnclosure previous
  let sample := Hermitian.Box.sampleAvoidingForms children.forms previous.box previous.proper
  let signs := (Hermitian.Box.signNeighborhoodOfSample sample).1
  let sampleTail := previous.tail signs.sample.point
  have sampleInside : previous.box.Contains signs.sample.point :=
    ⟨signs.sample.inside.1.le, signs.sample.inside.2.1.le,
      signs.sample.inside.2.2.1.le, signs.sample.inside.2.2.2.le⟩
  have sampleRepresents := previous.tail_represents sampleInside
  have terminalExcluded := children.terminalExcluded signs.sample
  let choice := Encoding.Parser.Next.admissibleBitOfExcluded previous.state signs.sample.point sampleTail
    previous.determinant sampleRepresents terminalExcluded
  let falseStable := children.stableAt signs false
  let trueStable := children.stableAt signs true
  have uniformStep : ∀ point, signs.box.Contains point →
      Encoding.Parser.Semantics.Prefix.CanStep previous.state point choice.bit := by
    intro point inside
    have sampleInNew : signs.box.Contains signs.sample.point :=
      ⟨signs.sampleInside.1.le, signs.sampleInside.2.1.le,
        signs.sampleInside.2.2.1.le, signs.sampleInside.2.2.2.le⟩
    have stable : Hermitian.Formula.Box.Stable previous.box signs.box (children.atBit choice.bit) := by
      cases selected : choice.bit with
      | false => exact falseStable
      | true => exact trueStable
    have sampleHolds := (children.canStep_iff choice.bit sampleInside).mpr choice.possible
    have pointHolds := (stable.holds_iff inside sampleInNew).mpr sampleHolds
    exact (children.canStep_iff choice.bit
      ((Rational.Box.Refinement.StrictInterior.refines signs.nested).contains inside)).mp pointHolds
  let extension := previous.appendWithBox choice.bit signs.box signs.proper signs.nested uniformStep
  exact
    { children := children
      signs := signs
      sampleTail := sampleTail
      sampleTailSpec := rfl
      sampleRepresents := sampleRepresents
      terminalExcluded := terminalExcluded
      choice := choice
      falseStable := falseStable
      trueStable := trueStable
      uniformStep := uniformStep
      extension := extension
      extensionSpec := rfl }

/-- Read the exact cached extended enclosure without repeating child construction or sampling. -/
@[expose] def next {previous : Encoding.Prefix.Enclosure} (step : Step previous) : Encoding.Prefix.Enclosure :=
  step.extension.next

/-- Read the exact retained rational sample without repeating the finite search. -/
@[expose] def sample {previous : Encoding.Prefix.Enclosure} (step : Step previous) : Gaussian.Basic.Canonical :=
  step.signs.sample.point

/-- The exact retained sample lies in the actual new prefix enclosure. -/
theorem sample_inside {previous : Encoding.Prefix.Enclosure} (step : Step previous) :
    step.next.box.Contains step.sample :=
  step.extension.boxEq.symm ▸
    ⟨step.signs.sampleInside.1.le, step.signs.sampleInside.2.1.le,
      step.signs.sampleInside.2.2.1.le, step.signs.sampleInside.2.2.2.le⟩

/-- The actual later rational sample represents the exact appended raw word. -/
theorem sample_represented {previous : Encoding.Prefix.Enclosure} (step : Step previous) :
    Encoding.Parser.Semantics.Prefix.Represented step.next.word step.sample := step.next.represented step.sample_inside

/-- The bit retained by the exact word extension equals the original local decision at the same sample. -/
theorem bit_eq_choice {previous : Encoding.Prefix.Enclosure} (step : Step previous) :
    step.extension.bit = step.choice.bit := by
  rcases step.next.uniform step.sample step.sample_inside with ⟨tail, represented⟩
  have possible : Encoding.Parser.Semantics.Prefix.CanStep previous.state step.sample step.extension.bit :=
    ⟨tail, step.extension.stateEq ▸ represented⟩
  exact step.choice.unique step.extension.bit possible

/-- The actual returned raw word appends the same unique Boolean selected at the retained original sample. -/
theorem wordEq {previous : Encoding.Prefix.Enclosure} (step : Step previous) :
    step.next.word = previous.word ++ [step.choice.bit] := by
  have actual := step.extension.wordEq
  rewrite [step.bit_eq_choice] at actual
  exact actual

/-- Every point of the actual returned enclosure is nonzero under the retained input guard. -/
theorem point_nonzero {previous : Encoding.Prefix.Enclosure} (step : Step previous)
    {point : Gaussian.Basic.Canonical} (inside : step.next.box.Contains point) : point ≠ 0 :=
  step.signs.ne_center 0 step.children.zeroFormMember (step.extension.boxEq ▸ inside)

end Step

end Purelib.Geometry.CCL.Prefix
