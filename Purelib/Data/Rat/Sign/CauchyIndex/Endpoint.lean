module

public import Purelib.Data.Rat.Sign.Jump
public import Purelib.Data.Rat.Sign.Typed
public import Purelib.Data.Sign.CauchyIndex.Product
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Rational readbacks of one-sided Cauchy contributions

The retained starting denominator and terminal product determine the endpoint
contribution. Formal sign classification gives the same integer reading.
-/

namespace Purelib.Data.Rat.Sign.CauchyIndex.Endpoint

open Purelib.Data.Rat
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- Compute the doubled left endpoint index from the starting denominator and ending numerator-denominator signs.

When the starting denominator vanishes, return the sign of the terminal numerator-denominator product; otherwise return
zero. The starting numerator is intentionally retained as an unused argument of this endpoint interface. -/
@[expose] public def leftEndpointIndex2
    (_P₀ Q₀ P₁ Q₁ : Fraction.Rational) : Int :=
  if Q₀ = 0 then Sign.Basic.sign (P₁ * Q₁) else 0

/-- Finite-sign evaluation of the left endpoint index agrees with its rational-coordinate calculation.

A vanishing starting denominator selects the terminal product sign in both
readings; a nonvanishing denominator selects zero in both readings. -/
public theorem sign_leftEndpointIndex2_ofCoordinate
    (P₀ Q₀ P₁ Q₁ : Fraction.Rational) :
    FiniteSign.leftEndpointIndex2
        (FiniteSign.ofCoordinate P₀) (FiniteSign.ofCoordinate Q₀)
        (FiniteSign.ofCoordinate P₁) (FiniteSign.ofCoordinate Q₁) =
      leftEndpointIndex2 P₀ Q₀ P₁ Q₁ := by
  by_cases QZero : Q₀ = 0
  · subst Q₀
    rw [leftEndpointIndex2, if_pos rfl,
      FiniteSign.leftEndpointIndex2,
      FiniteSign.ofCoordinate_zero, if_pos rfl,
      ← FiniteSign.ofCoordinate_mul, FiniteSign.value_ofCoordinate]
  · have signNonzero :
        FiniteSign.ofCoordinate Q₀ ≠ FiniteSign.zero := by
      intro equal
      exact QZero (FiniteSign.ofCoordinate_eq_zero_iff.mp equal)
    rw [leftEndpointIndex2, if_neg QZero,
      FiniteSign.leftEndpointIndex2, if_neg signNonzero]

/-- The finite-sign product correction agrees with the rational sign jump from one to the triple product.

The formal triple product has the sign of the retained rational product.
The finite jump from the positive sign therefore has the same doubled reading. -/
public theorem sign_productCorrection2_ofCoordinate
    (H B D : Fraction.Rational) :
    FiniteSign.productCorrection2
        (FiniteSign.ofCoordinate H) (FiniteSign.ofCoordinate B)
        (FiniteSign.ofCoordinate D) =
      Sign.Jump.signJump 1 (H * (B * D)) := by
  unfold FiniteSign.productCorrection2
  rw [show FiniteSign.positive = FiniteSign.ofCoordinate 1 by
      exact (FiniteSign.ofCoordinate_of_pos (by decide)).symm,
    ← FiniteSign.ofCoordinate_mul B D,
    ← FiniteSign.ofCoordinate_mul H (B * D),
    FiniteSign.jump_ofCoordinate]

end Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
