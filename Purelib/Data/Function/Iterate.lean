module

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

@[expose] public section

namespace Purelib.Data.Function

/-- Apply a self-map a specified natural number of times.

Zero iterations return the input. Each successor step applies the map once and
recurses on the remaining count. -/
def iterateMap {alpha : Type} (transformation : alpha → alpha) :
    Nat → alpha → alpha
  | 0, item => item
  | count + 1, item => iterateMap transformation count (transformation item)

section
open Purelib.Data
/-- Zero iterations of a self-map return the input. -/
@[simp] theorem iterateMap_zero {alpha : Type}
    (transformation : alpha → alpha) (item : alpha) :
    iterateMap transformation 0 item = item := rfl

/-- A successor iteration applies the map once before the remaining iterations. -/
@[simp] theorem iterateMap_succ {alpha : Type}
    (transformation : alpha → alpha) (count : Nat) (item : alpha) :
    iterateMap transformation (count + 1) item =
      iterateMap transformation count (transformation item) := rfl
end

namespace Distribution
namespace InvariantUnder
end InvariantUnder

end Distribution

end Purelib.Data.Function

end
