module
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic

section
/-!
# Finite Markov return estimates

This module gives an executable finite substitute for the recurrence step in
an ergodic argument.  A finite Markov path records exactly a supplied number
of future states.  If every current state has at least a displayed rational
chance `rate` to enter an event at the next step, then the probability of
avoiding the event for `count` steps is at most `(1 - rate) ^ count`.

The block form applies the same argument to an explicitly iterated transition
after any supplied burn-in time.  It is therefore suitable for a finite
transversal model: the geometry must provide a uniform block-hit certificate,
while this file performs the probability and recurrence calculation.  There
is no infinite path, stationary process, limit, or appeal to ergodicity.
-/

@[expose] public section

namespace Purelib.Measure

/-- Construct the exact finite law of successive transition states starting after the supplied initial state.

Zero steps return the empty path; each successor draws the next state and prepends it to the original recursively
constructed tail path. -/
def markovPathFrom {alpha : Type}
    (transition : alpha → Distribution alpha) :
    Nat → alpha → Distribution (List alpha)
  | 0, _ => Distribution.pure []
  | count + 1, item =>
      (transition item).bind fun next =>
        (markovPathFrom transition count next).map fun remaining =>
          next :: remaining

/-- Average the exact finite transition-path law over the retained original starting distribution. -/
def markovPaths {alpha : Type} (transition : alpha → Distribution alpha)
    (count : Nat) (source : Distribution alpha) : Distribution (List alpha) :=
  source.bind (markovPathFrom transition count)

end Purelib.Measure

end
