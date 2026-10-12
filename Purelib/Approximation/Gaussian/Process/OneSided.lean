module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.RationalInterval
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.OneSided.Basic
public import Purelib.Approximation.OneSided.Located
public import Purelib.Approximation.Rational.Request.Square
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Rational.Request

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# One-sided rational pairs as ordinary CCL processes

This CCL-side bridge converts a lower/upper rational pair only when it carries
the explicit finite gap modulus in `FiniteMeasure.LocatedPair`.  The bare
one-sided processes remain rate-free.

The requested CCL squared-error target is translated to the strictly smaller
rational gap `target / (target + 1)`.  Its square is below `target`, so the
construction needs no square root, completion, limit, or unbounded search.
-/

namespace Purelib.Approximation.Gaussian.Process.OneSided.LocatedPair

/-- Convert a one-sided pair with an explicit finite gap modulus into the ordinary stateful CCL process. Possible values
are exactly the displayed real-axis rational candidates in the current paired interval. -/
def toProcess {lower : Approximation.LowerProcess}
  {upper : Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) : Approximation.Gaussian.Process where
  State := pair.State
  ball state :=
    RationalInterval.ballOfBound
      (pair.observation state).bound
  Possible state value := ∃ candidate : Fraction.Rational,
    (pair.observation state).bound.Contains candidate ∧
      value = RationalEmbedding.realPoint candidate
  witness state :=
    ⟨RationalEmbedding.realPoint
        (pair.observation state).bound.sample,
      ⟨(pair.observation state).bound.sample,
        (pair.observation state).bound.sample_contains, rfl⟩⟩
  possible_inside := by
    rintro state value ⟨candidate, inside, rfl⟩
    exact RationalInterval.ballOfBound_contains inside
  refine state target positive :=
    pair.request state
      (Square.gapTarget target)
      (Square.gapTarget_pos positive)
  refine_persists := by
    rintro state target positive value ⟨candidate, inside, rfl⟩
    let gapPositive :=
      Square.gapTarget_pos positive
    exact ⟨candidate,
      (pair.request_refines state _ gapPositive).bound.contains inside, rfl⟩
  accurate := by
    intro state target positive
    let gapPositive :=
      Square.gapTarget_pos positive
    have small := pair.accurate state
      (Square.gapTarget target) gapPositive
    change (pair.observation
      (pair.request state
        (Square.gapTarget target)
        gapPositive)).gap ^ 2 < target
    exact Square.square_lt_target_of_gap_lt
      (pair.observation
        (pair.request state
          (Square.gapTarget target)
          gapPositive)).gap_nonnegative positive small
  centerBound :=
    2 * (Data.Gaussian.Norm.Basic.normSq
      (RationalEmbedding.realPoint
        (pair.observation pair.initial).bound.sample) +
      (pair.observation pair.initial).bound.width ^ 2)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  center_bounded state :=
    RationalInterval.ballOfBound_center_bounded
      (pair.refinesInitial state).bound

/-- The located-pair process observes the rational ball of the original paired interval at the same retained state. -/
@[simp] theorem toProcess_ball {lower :
  Approximation.LowerProcess} {upper : Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) (state : pair.State) :
    (toProcess pair).ball state =
      RationalInterval.ballOfBound
        (pair.observation state).bound :=
  rfl

/-- Refining the located-pair process requests the original pair at the computed rational gap target. -/
@[simp] theorem toProcess_refine {lower :
  Approximation.LowerProcess} {upper : Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) (state : pair.State)
    (target : Fraction.Rational) (positive : 0 < target) :
    (toProcess pair).refine state target positive =
      pair.request state
        (Square.gapTarget target)
        (Square.gapTarget_pos positive) :=
  rfl

end Purelib.Approximation.Gaussian.Process.OneSided.LocatedPair

end
