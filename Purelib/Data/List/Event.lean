module
public import Purelib.Measure.Weighted.Event
public import Purelib.Data.List.BinaryPrefix.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix renaming CCLMeasureWord -> Word

section
public section

/-!
# Explicit finite-depth raw-prefix contents

For a supplied raw prefix and natural depth, `rawExtensions` generates the
complete displayed binary frontier below that prefix.  Its total dyadic
content is exactly the prefix weight, independently of the chosen finite
depth.  This is a finite conservation theorem, not a statement about an
infinite bit space.
-/

namespace Purelib.Data.List

/-- Count the displayed Boolean words accepted by an executable event.

Each list occurrence contributes one or zero according to the event; repeated words
are counted separately. -/
@[expose] def rawFrontierEventCount : List Word → (Word → Bool) → Nat
  | [], _ => 0
  | word :: remaining, event =>
      (if event word then 1 else 0) + Purelib.Data.List.rawFrontierEventCount remaining event
end Purelib.Data.List

end

section
section
public section

/-!
# Finite counting and empirical measures

A displayed sample list gives an exact rational counting content.  When its
length is explicitly positive, uniform normalization gives an exact empirical
distribution.  Probabilities are selected natural counts divided by the
displayed finite sample size.
-/

namespace Purelib.Data.List

/-- Count the occurrences accepted by a Boolean event in a finite sample list.

Structural recursion adds one for each accepted entry and zero for each rejected
entry, preserving multiplicities. -/
@[expose] def countEvent {α : Type} : List α → (α → Bool) → Nat
  | [], _ => 0
  | item :: remaining, event =>
      (if event item then 1 else 0) + Purelib.Data.List.countEvent remaining event

/-- Counting after mapping equals counting with the event composed with that map. -/
theorem countEvent_map {α β : Type} (samples : List α)
    (function : α → β) (event : β → Bool) :
    List.countEvent (samples.map function) event =
      List.countEvent samples (fun item => event (function item)) := by
  induction samples with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      change (if event (function item) then 1 else 0) +
        List.countEvent (remaining.map function) event =
          (if event (function item) then 1 else 0) +
            List.countEvent remaining (fun entry => event (function entry))
      exact congrArg (fun count => (if event (function item) then 1 else 0) + count)
        inductionHypothesis
end Purelib.Data.List

end

end

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

public section

namespace Purelib.Data.List

/-- Test that no entry of a displayed finite list is accepted by the supplied event.

The empty list succeeds. Each nonempty step requires rejection of its head and
successful avoidance by the remaining tail. -/
@[expose] def pathAvoids {alpha : Type} (event : alpha → Bool) :
    List alpha → Bool
  | [] => true
  | item :: remaining => !(event item) && Purelib.Data.List.pathAvoids event remaining

/-- Test whether a displayed finite list contains any entry accepted by the event.

This is the Boolean complement of the retained pathAvoids computation on the same
event and list. -/
@[expose] def pathHits {alpha : Type} (event : alpha → Bool) :
    List alpha → Bool :=
  Measure.complementEvent (List.pathAvoids event)

end Purelib.Data.List

end

section
/-!
# Stationary finite dynamics and occupation averages

A finite transition preserves a displayed rational law when one exact step is
evaluation-equivalent to the original law.  This module proves preservation
at every supplied finite horizon and computes the exact expectation of a
finite Markov-path occupation count and frequency.  A final Chebyshev theorem
isolates the remaining dynamical input as the exact variance of that finite
occupation frequency.

This is a finite quantitative mean-ergodic interface, not an asymptotic
ergodic theorem: every path, horizon, event, expectation, and variance is
displayed finite rational data.
-/

public section

namespace Purelib.Data.List

/-- Count the displayed list entries accepted by a supplied Boolean event.

Every accepted occurrence contributes one, including repeated values; the recursion
terminates on the retained finite tail. -/
@[expose] def pathVisitCount {alpha : Type} (event : alpha → Bool) :
    List alpha → Nat
  | [] => 0
  | item :: remaining =>
      (if event item then 1 else 0) + Purelib.Data.List.pathVisitCount event remaining

/-- A successful avoidance test certifies zero visits to the supplied event. -/
theorem pathVisitCount_eq_zero_of_pathAvoids {alpha : Type}
    (event : alpha → Bool) : ∀ path : List alpha,
    List.pathAvoids event path = true → List.pathVisitCount event path = 0
  | [], selected => rfl
  | item :: remaining, selected => by
      cases head : event item
      · simp only [List.pathAvoids, head, Bool.not_false, Bool.true_and] at selected
        change (if event item then 1 else 0) + List.pathVisitCount event remaining = 0
        rewrite [head]
        change 0 + List.pathVisitCount event remaining = 0
        rewrite [Nat.zero_add]
        exact pathVisitCount_eq_zero_of_pathAvoids event remaining selected
      · simp only [List.pathAvoids, head, Bool.not_true, Bool.false_and] at selected
        cases selected

end Purelib.Data.List

end
