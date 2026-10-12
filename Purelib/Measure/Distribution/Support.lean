module
public import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic

section
/-!
# Support on retained distribution atoms

Support records a property of every original atom payload, including zero-weight occurrences. Pure distributions and
finite binding preserve these payload certificates.
-/

public section

namespace Purelib.Measure

namespace Distribution

open Purelib.Data

/-- Require the property on every payload occurrence retained by the exact distribution.

This includes occurrences with zero weight; the condition describes the retained list rather than only its positive-mass
payloads. -/
@[expose] def Supports {alpha : Type} (distribution : Distribution alpha)
    (property : alpha → Prop) : Prop :=
  ∀ atom, atom ∈ distribution.atoms → property atom.item

/-- A pure distribution supports every property certified for its sole retained payload. -/
theorem Supports.pure {alpha : Type} {property : alpha → Prop}
    {item : alpha} (selected : property item) :
    (Distribution.pure item).Supports property := by
  intro atom member
  have atomIdentity := List.Membership.mem_singleton.mp member
  have itemIdentity := congrArg Weighted.item atomIdentity
  simpa only [itemIdentity] using selected

/-- Binding a supported source through kernels supporting the target property preserves that target support. -/
theorem Supports.bind {alpha beta : Type}
    {source : Distribution alpha} {transition : alpha → Distribution beta}
    {sourceProperty : alpha → Prop} {targetProperty : beta → Prop}
    (sourceSupport : source.Supports sourceProperty)
    (transitionSupport : ∀ item, sourceProperty item →
      (transition item).Supports targetProperty) :
    (source.bind transition).Supports targetProperty := by
  intro atom member
  rcases mem_bindAtoms_source_transition transition atom member with
      ⟨sourceAtom, sourceMember, targetAtom, targetMember, itemIdentity⟩
  have targetSelected := transitionSupport sourceAtom.item
    (sourceSupport sourceAtom sourceMember) targetAtom targetMember
  simpa only [itemIdentity] using targetSelected

/-- An event selected by every retained occurrence has probability one. -/
theorem probability_eq_one_of_supports {alpha : Type}
    (distribution : Distribution alpha) (event : alpha → Bool)
    (support : distribution.Supports fun item => event item = true) :
    distribution.probability event = 1 := by
  unfold Distribution.probability
  rw [eventWeight_eq_totalWeight_of_all event distribution.atoms support,
    distribution.total_one]

end Distribution

end Purelib.Measure

end
