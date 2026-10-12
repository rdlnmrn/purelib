module

import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Grid.Nearest.Replay
import Purelib.Data.Gaussian.Inverse.Check
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.RootIsolation.SquareRoot.Newton.Replay.Step
public import Purelib.RootIsolation.SquareRoot.Newton.Search
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Grid.Nearest.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.RootIsolation

section
@[expose] public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.RootIsolation.SquareRoot.Newton.Replay

set_option genInjectivity false in
/-- A finite exact replay of rounded square-root Newton search.

The original fuel, grid and proposal remain indices; accepted values, rejected selections and checked inverse steps are
retained explicitly. -/
inductive Trace (parameter : Gaussian.Basic.Canonical) (acceptable : Gaussian.Basic.Canonical → Prop) [DecidablePred
  acceptable] :
    Nat → Fraction.Rational → Gaussian.Basic.Canonical → Type where
  /-- The finite search has no fuel left at the retained grid and proposal. -/ | exhausted (grid : Fraction.Rational)
    (proposal : Gaussian.Basic.Canonical) : Trace parameter
    acceptable 0 grid proposal
  /-- The checked rounded proposal selects the retained value satisfying the exact requested predicate. -/ | accepted
    {fuel : Nat} {grid : Fraction.Rational} {proposal : Gaussian.Basic.Canonical}
      (point : Grid.Nearest.Replay.Rounded grid proposal) (value : {value : Gaussian.Basic.Canonical // acceptable
        value})
      (selected : SquareRoot.Newton.Search.select parameter acceptable point.val = some value) :
      Trace parameter acceptable (fuel + 1) grid proposal
  /-- A rejected rounded point and checked inverse lead to the retained lower-fuel continuation trace. -/ | next {fuel :
    Nat} {grid : Fraction.Rational} {proposal : Gaussian.Basic.Canonical}
      (point : Grid.Nearest.Replay.Rounded grid proposal) (miss : SquareRoot.Newton.Search.select parameter acceptable
        point.val = none)
      (inverse : Data.Gaussian.Basic.Canonical.Inverse.Certificate point.val)
      (tail : Trace parameter acceptable fuel (grid / 4)
        (SquareRoot.Newton.Replay.Step.advance parameter point.val inverse)) :
      Trace parameter acceptable (fuel + 1) grid proposal

constructive_injectivity Trace

namespace Trace.accepted

end Trace.accepted

namespace Trace.next

end Trace.next

namespace Trace

/-- Read the accepted checked value from a replay trace, or no value from an exhausted finite attempt. -/
def result {parameter : Gaussian.Basic.Canonical} {acceptable : Gaussian.Basic.Canonical → Prop} [DecidablePred
  acceptable] :
    {fuel : Nat} → {grid : Fraction.Rational} → {proposal : Gaussian.Basic.Canonical} →
      Trace parameter acceptable fuel grid proposal → Option {value :
        Gaussian.Basic.Canonical // acceptable value}
  | _, _, _, .exhausted _ _ => none
  | _, _, _, .accepted _ value _ => some value
  | _, _, _, .next _ _ _ tail => tail.result

/-- The retained replay result equals the original rounded Newton search at the same fuel, grid and proposal. -/
theorem result_eq {parameter : Gaussian.Basic.Canonical} {acceptable : Gaussian.Basic.Canonical → Prop}
  [DecidablePred acceptable]
    {fuel : Nat} {grid : Fraction.Rational} {proposal : Gaussian.Basic.Canonical}
    (trace : Trace parameter acceptable fuel grid proposal) :
    trace.result = SquareRoot.Newton.Search.search parameter acceptable fuel grid proposal := by
  induction trace with
  | exhausted => rfl
  | accepted point value selected =>
      rw [SquareRoot.Newton.Search.search_step, ← point.property, selected]
      rfl
  | next point miss inverse tail ih =>
      rw [SquareRoot.Newton.Search.search_step, ← point.property, miss]
      exact ih.trans (congrArg (SquareRoot.Newton.Search.search parameter acceptable _ _)
        (SquareRoot.Newton.Replay.Step.advance_eq parameter point.val inverse))

end Trace

end Purelib.RootIsolation.SquareRoot.Newton.Replay

end

end
