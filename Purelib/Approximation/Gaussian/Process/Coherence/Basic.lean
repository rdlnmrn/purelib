module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic

set_option genInjectivity false in
/-- A wholly finite certificate that all refinement branches of a process describe one progressively sharpened
operational value. The factor four is the squared two-leg triangle bound needed when two readings are compared through
one displayed finite centre. -/
structure Coherent (process :
  Approximation.Gaussian.Process) where
  /-- The retained rational semantic squared-error allowance at each process state. -/ allowance : process.State →
    Fraction.Rational
  /-- Every retained semantic allowance is nonnegative. -/ allowance_nonneg : ∀ state, 0 ≤ allowance state
  /-- Each state's observed ball radius is bounded by its semantic allowance. -/ ball_radius_le : ∀ state,
    (process.ball state).radiusSq ≤ allowance state
  /-- Possible readings at any two retained states differ by squared norm at most four times their summed allowances. -/
    possible_close : ∀ {leftState rightState : process.State}
      {leftValue rightValue : Canonical},
    process.Possible leftState leftValue →
      process.Possible rightState rightValue →
        Data.Gaussian.Norm.Basic.normSq (leftValue - rightValue) ≤
          4 * (allowance leftState + allowance rightState)
  /-- Compute the positive refinement-request threshold for a desired semantic allowance. -/ accuracyRequest :
    Fraction.Rational → Fraction.Rational
  /-- A positive semantic target yields a positive refinement-request threshold. -/ accuracyRequest_pos : ∀ {target :
    Fraction.Rational}, 0 < target →
    0 < accuracyRequest target
  /-- Every positive refinement request below the computed threshold yields semantic allowance below the original
    positive target. -/ refine_accurate : ∀ (state : process.State) (target : Fraction.Rational)
      (_positive : 0 < target) (request : Fraction.Rational)
      (requestPositive : 0 < request),
    request < accuracyRequest target →
      allowance (process.refine state request requestPositive) < target

constructive_injectivity Coherent

namespace Coherent

/-- The exact displayed-rational process is coherent with zero semantic allowance. -/
def exact (value : Canonical)
  :
    Approximation.Gaussian.Process.Coherence.Basic.Coherent (Approximation.Gaussian.Process.exact value) where
  allowance _ := 0
  allowance_nonneg _ := le_rfl
  ball_radius_le _ := le_rfl
  possible_close := by
    intro leftState rightState leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    change (0 : Fraction.Rational) ≤ 0
    exact le_rfl
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

/-- A possible finite reading is bounded by its semantic allowance and the process's rational centre bound. -/
theorem possible_normSq_le {process :
  Approximation.Gaussian.Process} (coherent : Approximation.Gaussian.Process.Coherence.Basic.Coherent process)
    {state : process.State} {value : Canonical}
    (possible : process.Possible state value) :
    Data.Gaussian.Norm.Basic.normSq value ≤ 2 * (coherent.allowance state + process.centerBound) := by
  let center := (process.ball state).center
  have inside := process.possible_inside possible
  have deviationLe : Data.Gaussian.Norm.Basic.normSq (value - center) ≤ coherent.allowance state :=
    inside.trans (coherent.ball_radius_le state)
  have identity : value = (value - center) + center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add deviationLe (process.center_bounded state)) (by decide))
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
