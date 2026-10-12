module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Data.CCL.Transducer.Replay.Check

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
/-- Return the exact replay ball when its squared radius is nonnegative and strictly below the retained target.

Failure keeps the same source index, requested target and ball together with a proof that their radius condition is
violated. -/
def checkedBall (index : Nat) (target : Fraction.Rational) (ball :
  Enclosure.Ball.Data.BallData) :
    Except Data.CCL.Transducer.Replay.Failure Enclosure.Ball.Data.BallData :=
  if valid : 0 ≤ ball.radiusSq ∧ ball.radiusSq < target then .ok ball
  else .error (.inaccurate index target ball valid)

/-- The exact replay ball is accepted precisely when its radius squared is nonnegative and strictly below the target. -/
theorem checkedBall_ok_iff (index : Nat) (target : Fraction.Rational)
  (ball : Enclosure.Ball.Data.BallData) :
    checkedBall index target ball = .ok ball ↔ 0 ≤ ball.radiusSq ∧ ball.radiusSq < target := by
  unfold checkedBall
  split
  · rename_i valid
    exact ⟨fun _ => valid, fun _ => rfl⟩
  · rename_i invalid
    constructor
    · intro impossible
      cases impossible
    · intro valid
      exact (invalid valid).elim

/-- A failed ball check retains that exact index, target and ball with a witness of the violated radius condition. -/
theorem checkedBall_error {index : Nat} {target : Fraction.Rational}
  {ball : Enclosure.Ball.Data.BallData} {error : Data.CCL.Transducer.Replay.Failure}
    (failure : checkedBall index target ball = .error error) :
    ∃ violated : ¬ (0 ≤ ball.radiusSq ∧ ball.radiusSq < target),
      error = .inaccurate index target ball violated := by
  unfold checkedBall at failure
  split at failure
  · cases failure
  · rename_i violated
    cases failure
    exact ⟨violated, rfl⟩
end Purelib.Data.CCL.Transducer.Replay.Check

end
