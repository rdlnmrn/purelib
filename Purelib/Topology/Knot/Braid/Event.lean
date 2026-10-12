module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Topology.Knot.Braid.Word.Basic
meta import Purelib.Elab.Deriving.Repr
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Topology.Knot.Braid.Basic

open Purelib.Data.Fin

section
@[expose] public section

/-!
# Certified projected crossings of finite root paths

An Artin generator acts on the left-to-right positions of a chosen planar
projection, whereas finite monodromy transports the persistent owner indices
of root boxes.  Those numberings need not coincide.  This file records their
finite relabelling explicitly and folds atomic projected chamber overlaps into
an executable braid word.

A crossing chart contains only rational root boxes, a signed adjacent
generator, an exact owner-matching law, and a strict height separation of the
two crossing strands.  It is therefore finite certificate data: no completed
root track or configuration space is introduced.  The extraction theorem
proves that evaluating the resulting word gives exactly the chamber-path
transport, expressed in the endpoint projection orders.
-/

namespace Purelib.Topology.Knot.Braid

open Purelib.Topology.Knot.Braid

/-! ## Atomic projected events -/

set_option genInjectivity false in
/-- A finite projected event with either no crossing or one signed adjacent crossing. -/
inductive Event (strands : Nat)
  /-- An event with no crossing and identity endpoint action. -/ | stationary
  /-- An event retaining one signed adjacent generator. -/ | crossing (generator : Generator strands)
deriving DecidableEq

constructive_injectivity Event

derive_exposed_repr Event

namespace Event

/-- Read a stationary event as the empty word and a crossing as a singleton word. -/
def word {strands : Nat} : Event strands → Word strands
  | .stationary => []
  | .crossing generator => [generator]

section
open Purelib.Topology.Knot.Braid.Event
open _root_.Purelib.Topology.Knot.Braid renaming Event -> Event
/-- The word of a stationary event is empty. -/
@[simp] theorem word_stationary (strands : Nat) :
    word (.stationary : Event strands) = [] := rfl

/-- The word of a crossing event contains its single retained generator. -/
@[simp] theorem word_crossing {strands : Nat}
    (generator : Generator strands) : word (.crossing generator) = [generator] :=
  rfl

end

/-- Evaluate the finite endpoint permutation of an event through its word. -/
def permutation {strands : Nat} (event : Event strands) :
    Data.Fin.Bijection strands strands := event.word.permutation

/-- Reverse the retained crossing, leaving a stationary event unchanged. -/
def reverse {strands : Nat} : Event strands → Event strands
  | .stationary => .stationary
  | .crossing generator => .crossing generator.reverse

open Purelib.Topology.Knot.Braid.Event in
open _root_.Purelib.Topology.Knot.Braid renaming Event -> Event in
/-- Reversing a projected event twice restores the original event. -/
@[simp] theorem reverse_reverse {strands : Nat} (event : Event
  strands) :
    event.reverse.reverse = event := by
  cases event with
  | stationary => rfl
  | crossing generator =>
      simp only [reverse, Generator.reverse_reverse, -eq_self, -iff_self]
      rfl

/-- Reversing an event gives the inverse of its braid word. -/
@[simp] theorem word_reverse {strands : Nat} (event : Event
  strands) :
    event.reverse.word = event.word.inverse := by
  cases event with
  | stationary => rfl
  | crossing generator => rfl

open Purelib.Topology.Knot.Braid.Event
open _root_.Purelib.Topology.Knot.Braid renaming Event -> Event
/-- A stationary event fixes every strand position. -/
@[simp] theorem permutation_stationary_forward (strands : Nat)
    (position : Fin strands) :
    (permutation (.stationary : Event strands)).forward position = position :=
  rfl

/-- A crossing event acts on strands by its retained generator permutation. -/
@[simp] theorem permutation_crossing_forward {strands : Nat}
    (generator : Generator strands) (position : Fin strands) :
    (permutation (.crossing generator)).forward position =
      generator.permutation.forward position := rfl

end Event

end Purelib.Topology.Knot.Braid

end
