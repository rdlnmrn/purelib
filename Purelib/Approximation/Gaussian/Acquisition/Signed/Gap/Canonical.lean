module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Coherent

import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Schedule
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition (State)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap

open Purelib.Approximation.Gaussian.Acquisition.State

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical

namespace Gap
end Gap

set_option genInjectivity false in
/-- The retained result of the computed finite signed-acquisition schedule.

It records the actual refinement count, the final state reached from the original start and a signed certificate indexed
by that final state. -/
structure CanonicalReport (tau :
  Coherent.CoherentNamed) (start : State tau) (delta : Fraction.Rational) where
  /-- The retained number of canonical refinement steps. -/ count : Nat
  /-- The retained count equals the schedule computed from the original start and gap threshold. -/ count_eq : count =
    Schedule.canonicalCount start delta
  /-- The exact final acquisition state. -/ final : State tau
  /-- The final state equals the original start advanced by the retained count. -/ final_eq : final = Schedule.advanceN
    start count
  /-- The positive or negative certificate indexed by the exact final state and original gap threshold. -/ outcome :
    Decision.Outcome tau final delta

constructive_injectivity CanonicalReport

/-- Execute the computed finite signed-acquisition schedule under a positive persistent gap.

The result retains the count and final state, and rules out the near-boundary alternative using the original gap
certificate. -/
def canonical (tau : Coherent.CoherentNamed)
  (start : State tau) (delta : Fraction.Rational) (positive : 0 < delta)
    (gap : Approximation.Gaussian.Acquisition.Signed.Gap tau start delta) :
        CanonicalReport tau
      start delta :=
  let count := Schedule.canonicalCount start delta
  let final := Schedule.advanceN start count
  let fine := Schedule.canonical_accurate start delta positive
  { count := count
    count_eq := rfl
    final := final
    final_eq := rfl
    outcome := Decision.certify final delta positive fine (Approximation.Gaussian.Acquisition.Signed.Gap.advanceN start
        gap count)
      (Signed.decide final.ball delta positive fine) }
end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical

end
