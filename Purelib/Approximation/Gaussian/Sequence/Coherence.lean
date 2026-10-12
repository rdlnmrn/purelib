module
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Sequence

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
namespace Coherent

/-- Two samples later than a common base differ by squared norm at most four times that base's error allowance. -/
private theorem approximation_pair_close_from
    (approximation : ApproximationData) {base left right : Nat}
    (leftOrder : base ≤ left) (rightOrder : base ≤ right) :
    Data.Gaussian.Norm.Basic.normSq (approximation.sample left - approximation.sample right) ≤
      4 * approximation.radiusSq base := by
  have leftClose := approximation.later_close leftOrder
  have rightCloseForward := approximation.later_close rightOrder
  have rightClose :
      Data.Gaussian.Norm.Basic.normSq
          (approximation.sample base - approximation.sample right) ≤
        approximation.radiusSq base := by
    rw [Purelib.Data.Gaussian.Field.sub_eq_neg_sub, Data.Gaussian.Norm.Basic.normSq_neg]
    exact rightCloseForward
  calc
    Data.Gaussian.Norm.Basic.normSq (approximation.sample left - approximation.sample right) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq
            (approximation.sample left - approximation.sample base) +
          Data.Gaussian.Norm.Basic.normSq
            (approximation.sample base - approximation.sample right)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 *
        (approximation.radiusSq base + approximation.radiusSq base) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftClose rightClose) (by decide)
    _ = 4 * approximation.radiusSq base := by ring1

/-- Every limit-free progressive approximation already carries enough finite data to certify coherence of the process
generated from it. -/
def ofApproximation (approximation :
  ApproximationData) :
    Gaussian.Process.Coherence.Basic.Coherent approximation.toProcess where
  allowance index := approximation.radiusSq index
  allowance_nonneg := approximation.radiusSq_nonneg
  ball_radius_le _ := le_rfl
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    change approximation.Possible leftState leftValue at leftPossible
    change approximation.Possible rightState rightValue at rightPossible
    rcases leftPossible with ⟨leftLater, leftOrder, rfl⟩
    rcases rightPossible with ⟨rightLater, rightOrder, rfl⟩
    rcases Nat.le_total leftState rightState with stateOrder | stateOrder
    · calc
        Data.Gaussian.Norm.Basic.normSq
            (approximation.sample leftLater -
              approximation.sample rightLater) ≤
            4 * approximation.radiusSq leftState :=
          approximation_pair_close_from approximation leftOrder
            (stateOrder.trans rightOrder)
        _ ≤ 4 *
            (approximation.radiusSq leftState +
              approximation.radiusSq rightState) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (le_add_of_nonneg_right
              (approximation.radiusSq_nonneg rightState)) (by decide)
    · calc
        Data.Gaussian.Norm.Basic.normSq
            (approximation.sample leftLater -
              approximation.sample rightLater) ≤
            4 * approximation.radiusSq rightState :=
          approximation_pair_close_from approximation
            (stateOrder.trans leftOrder) rightOrder
        _ ≤ 4 *
            (approximation.radiusSq leftState +
              approximation.radiusSq rightState) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (le_add_of_nonneg_left
              (approximation.radiusSq_nonneg leftState)) (by decide)
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact (approximation.refineIndex_accurate state request
      requestPositive).trans requestSmall
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
