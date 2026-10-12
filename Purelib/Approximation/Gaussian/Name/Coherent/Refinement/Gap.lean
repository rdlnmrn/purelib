module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Exact finite division decisions from a candidate gap

The extra invariant supplies a positive rational exclusion zone for nonzero
candidates, without supplying the result of the decision. Requested-precision
smallness then forces zero; the other branch constructs ordinary apartness.
This candidate invariant is intentionally not asserted for arbitrary
approximate readings of an algebraic or operationally zero channel.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Process.Apart.Possible (PossibleApart)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero (ZeroCandidates)
open Purelib.Data.Gaussian.Basic.Canonical

/-- An unsigned exclusion zone at one retained source. Different candidates are not assumed in advance to choose the
same side of the disjunction. -/
def Gap (denominator : Coherent.CoherentNamed) (state
  : State denominator) (gap : Fraction.Rational) : Prop :=
  ∀ {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible state.source value →
    value = 0 ∨ gap ≤ Data.Gaussian.Norm.Basic.normSq value

namespace Gap

/-- The retained candidate gap persists along any supplied backwards candidate transport between source states. -/
theorem after {denominator :
  Coherent.CoherentNamed} {first last : State denominator} {gap : Fraction.Rational}
    (certificate : Gap denominator first gap)
    (persists : ∀ {value : Data.Gaussian.Basic.Canonical}, denominator.name.process.Possible last.source value →
      denominator.name.process.Possible first.source value) : Gap
        denominator last gap :=
  fun possible => certificate (persists possible)

/-- The threshold-relative upper bound becomes exact negative evidence only because the independent gap excludes the
small nonzero alternative. -/
theorem zero_of_small {denominator :
  Coherent.CoherentNamed} {state : State denominator} {gap : Fraction.Rational}
    (certificate : Gap denominator state gap) (small : Small
      denominator state gap) :
    Zero.ZeroCandidates denominator state :=
  fun possible => (certificate possible).resolve_right
    (not_le_of_gt (small.bound possible))

end Gap
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement

end
