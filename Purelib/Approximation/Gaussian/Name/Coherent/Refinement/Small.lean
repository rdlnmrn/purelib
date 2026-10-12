module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Based

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Requested-precision denominator acquisition

One prescribed source refinement followed by the audited small-or-apart
decision returns either candidate apartness or a persistent squared-norm
upper bound. Smallness is relative to a supplied threshold, not a zero test.
The ordinary canonical retry index is preserved: this is a requested-target
refinement, not a falsely labelled canonical `Progress` transition.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement

/-- A bound on candidates at one retained source, hence also on every based future candidate. It does not assert that
later enclosing balls are nested. -/
structure Small (denominator :
  Coherent.CoherentNamed) (state : State denominator) (threshold : Fraction.Rational) : Type where
  /-- Every candidate at the retained source has squared norm strictly below the displayed threshold. -/ bound : ∀
    {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible state.source value →
    Data.Gaussian.Norm.Basic.normSq value < threshold

namespace Small

/-- The retained strict candidate bound persists at every certified based future state. -/
theorem at_future {denominator :
  Coherent.CoherentNamed} {state : State denominator}
    {threshold : Fraction.Rational} (small : Small denominator
      state threshold)
    (future : Gaussian.Process.Based.BasedState denominator.name.process state.source)
    {value : Data.Gaussian.Basic.Canonical} (possible : denominator.name.process.Possible future.source value) :
    Data.Gaussian.Norm.Basic.normSq value < threshold := small.bound (future.persists possible)

/-- Transport the strict candidate bound along an explicit candidate-persistence certificate between the original
denominator states. -/
def after {denominator :
  Coherent.CoherentNamed} {first last : State denominator}
    {threshold : Fraction.Rational} (small : Small denominator
      first threshold)
    (persists : ∀ {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) :
        Small denominator last threshold :=
  ⟨fun possible => small.bound (persists possible)⟩

/-- A threshold-relative obstruction, using an explicit finite candidate. Smaller positive lower bounds are not ruled
out. -/
theorem incompatible_lower {denominator :
  Coherent.CoherentNamed} {state : State denominator}
    {threshold : Fraction.Rational} (small : Small denominator
      state threshold)
    (apart : Possible.PossibleApart (Gaussian.Process.Based.based denominator.name.process state.source))
    (large : threshold ≤ apart.lowerSq) : False := by
  let initial := BasedState.initial denominator.name.process state.source
  let witness := denominator.name.process.witness state.source
  have lower := apart.lower initial witness.property
  exact (not_lt_of_ge (large.trans lower)) (small.bound witness.property)

end Small
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement

end
