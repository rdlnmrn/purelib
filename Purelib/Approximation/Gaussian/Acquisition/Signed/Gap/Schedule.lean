module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Rounding.Floor

public import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Quantitative signed completeness from an unsigned candidate gap

A persistent rational gap removes the near-boundary alternative without
supplying the sign. Both direct requested precision and a coefficient-bounded
canonical refinement schedule construct signed evidence. The canonical
positive result supplies a budget for the original positivity `attempt`.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Schedule

open Purelib
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Acquisition.State
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding

namespace Gap
end Gap

/-- A finite rational scan computes the number of canonical refinements. The final extra unit performs the request at
the selected small index. -/
@[expose] public def canonicalCount {tau : Coherent.CoherentNamed} (state : State tau) (delta : Fraction.Rational)
  : Nat :=
  Search.firstQuarterBelow 1 state.retained.nextIndex (delta ^ 2 / 16) -
    state.retained.nextIndex + 1

/-- The computed canonical schedule makes the cached squared enclosure radius smaller than one sixteenth of the squared
positive gap threshold. -/
theorem canonical_accurate {tau : Coherent.CoherentNamed} (state : State tau)
    (delta : Fraction.Rational) (positive : 0 < delta) :
    (Schedule.advanceN state (Approximation.Gaussian.Acquisition.Signed.Gap.Schedule.canonicalCount state
      delta)).ball.radiusSq < delta ^ 2 / 16 := by
  let index := Search.firstQuarterBelow 1 state.retained.nextIndex (delta ^ 2 / 16)
  have indexGe : state.retained.nextIndex ≤ index :=
    Search.firstQuarterBelow_ge _ _ _
  have indexEq : state.retained.nextIndex + (index - state.retained.nextIndex) = index := by omega
  have fine := Schedule.advanceN_accurate state (index - state.retained.nextIndex)
  rw [indexEq] at fine
  exact fine.trans (Search.firstQuarterBelow_accurate 1 (by decide)
    state.retained.nextIndex (delta ^ 2 / 16) (Purelib.Data.Rat.Bounds.Quarter.target_positive positive))

/-- Binary-length bound on the number of requested canonical refinements. It is not a bound on the cost of each source
refinement. -/
theorem canonicalCount_le {tau : Coherent.CoherentNamed} (state : State tau) (delta : Fraction.Rational) :
    Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Schedule.canonicalCount state delta ≤
      Nat.log2 (Floor.ceilNat (1 / (delta ^ 2 / 16))) + 2 := by
  have bound := Search.firstQuarterBelow_le 1 state.retained.nextIndex (delta ^ 2 / 16)
  unfold Approximation.Gaussian.Acquisition.Signed.Gap.Schedule.canonicalCount
  omega
end Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Schedule

end
