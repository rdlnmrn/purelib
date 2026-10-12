module
import Purelib.Data.List.Append

public import Purelib.Data.Function.Iterate
import Purelib.Measure.Event.Family
public import Purelib.Measure.Event.Occurrence

section
/-!
# Finite measure-preserving dynamics

This module packages the part of elementary dynamical measure theory that is
already meaningful for an explicitly displayed finite rational law.  A map
preserves a distribution when its finite pushforward has exactly the same
Boolean-event probabilities and rational expectations.  Orbit windows,
visit counts, and their second-moment hitting estimate are all indexed by
supplied natural numbers; no infinite orbit, limiting average, recurrence
principle, or completed measurable space is introduced.
-/

public section

namespace Purelib.Measure

open Purelib.Data

open Purelib.Data in
/-- Test the original event after the supplied finite number of iterations of the payload transformation. -/
@[expose] def orbitEvent {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (time : Nat) : alpha → Bool :=
  fun item => event (Function.iterateMap transformation time item)

/-- List the successive iterated events over the exact finite window starting at the supplied time.

The recursive successor step appends the event at the old window's endpoint, preserving time order. -/
@[expose] def orbitEvents {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start : Nat) :
    Nat → List (alpha → Bool)
  | 0 => []
  | count + 1 =>
      orbitEvents transformation event start count ++
        [orbitEvent transformation event (start + count)]

/-- An orbit event window of length zero is empty. -/
@[simp] theorem orbitEvents_zero {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start : Nat) :
    orbitEvents transformation event start 0 = [] := rfl

/-- Extending an orbit event window appends its next endpoint event. -/
theorem orbitEvents_succ {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start count : Nat) :
    orbitEvents transformation event start (count + 1) =
      orbitEvents transformation event start count ++
        [orbitEvent transformation event (start + count)] := rfl

/-- The finite orbit event window has exactly its requested length. -/
theorem orbitEvents_length {alpha : Type}
    (transformation : alpha → alpha) (event : alpha → Bool)
    (start : Nat) : ∀ count : Nat,
    (orbitEvents transformation event start count).length = count
  | 0 => rfl
  | count + 1 => by
      rw [orbitEvents_succ, List.Append.length_append,
        orbitEvents_length transformation event start count]
      simp only [-eq_self, -iff_self, List.length_cons, List.length_nil]
      rfl

/-- Select payloads whose finite orbit visits the original event within the retained time window. -/
@[expose] def orbitHitEvent {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start count : Nat) : alpha → Bool :=
  unionEvents (orbitEvents transformation event start count)

/-- Count selecting time positions of the exact finite orbit event window. -/
@[expose] def orbitVisitCount {alpha : Type} (transformation : alpha → alpha)
    (event : alpha → Bool) (start count : Nat) : alpha → Nat :=
  occurrenceCount (orbitEvents transformation event start count)

namespace Distribution
namespace InvariantUnder
end InvariantUnder

end Distribution

end Purelib.Measure

end
