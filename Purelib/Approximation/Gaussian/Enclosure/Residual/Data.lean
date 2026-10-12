module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
public import Purelib.Approximation.Gaussian.Enclosure.Residual

import Purelib.Data.Gaussian.Norm.Comparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Gaussian.Enclosure.Ball.Data

open Purelib.Data.Gaussian.Basic.Canonical.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-! # Certified projection of the recorded productive chunks -/

namespace Purelib.Approximation.Gaussian.Enclosure.Residual.Data

open Purelib.Data.Gaussian.Basic.Canonical

/-- The selected apartness certificate retains precisely the numerical lower bound computed by the existing residual
decision. -/
theorem residualDecision_fields (ball :
    Approximation.Gaussian.Enclosure.Ball)
  (target : Fraction.Rational) (positive : 0 < target)
    (fine : ball.radiusSq < target / 6) :
    match Residual.decide ball target positive fine with
    | .small _ => Data.Bounds.smallUpper (BallData.ofBall ball) < target
    | .apart certificate =>
        ¬ Data.Bounds.smallUpper (BallData.ofBall ball) < target ∧
        certificate.lowerSq = Data.Gaussian.Norm.Basic.normSq ball.center / 2 - ball.radiusSq := by
  unfold Residual.decide
  by_cases small : Residual.SmallBall ball target
  · rw [dif_pos small]
    simpa only [Data.Bounds.smallUpper, Comparison.normSqFromReduced_eq, BallData.ofBall,
      Residual.SmallBall] using small
  · rw [dif_neg small]
    refine ⟨?_, rfl⟩
    simpa only [Data.Bounds.smallUpper, Comparison.normSqFromReduced_eq, BallData.ofBall,
      Residual.SmallBall] using small
end Purelib.Approximation.Gaussian.Enclosure.Residual.Data

end
