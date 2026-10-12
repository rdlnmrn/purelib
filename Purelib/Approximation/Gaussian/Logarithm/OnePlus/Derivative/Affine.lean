module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.OneAdd

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian.Norm

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Affine

/-! ## From a local coordinate to an anchored logarithm branch -/

/-- For `x = anchor * (1+u)`, the local derivative target followed by the affine chart derivative is exactly `x⁻¹`. A
branch correction is constant with respect to `x`, so it contributes the exact zero derivative. -/
theorem anchoredLogDerivative_inverse (anchor
  u : Data.Gaussian.Basic.Canonical)
    (anchorNonzero : anchor ≠ 0) (disk : Data.Gaussian.Norm.Basic.normSq u ≤ 1 / 4) :
    (1 + u)⁻¹ * anchor⁻¹ = (anchor * (1 + u))⁻¹ := by
  have oneAddNonzero := OneAdd.one_add_ne_zero disk
  have productNonzero :=
    Data.Gaussian.Field.mul_ne_zero_direct
      anchorNonzero oneAddNonzero
  have anchorCancel : anchor⁻¹ * anchor = 1 := by
    simpa only [Data.Gaussian.Field.inv_eq] using
      Data.Gaussian.Field.inv_mul anchor anchorNonzero
  have oneAddCancel : (1 + u)⁻¹ * (1 + u) = 1 := by
    simpa only [Data.Gaussian.Field.inv_eq] using
      Data.Gaussian.Field.inv_mul (1 + u) oneAddNonzero
  have productCancel :
      (anchor * (1 + u))⁻¹ * (anchor * (1 + u)) = 1 := by
    simpa only [Data.Gaussian.Field.inv_eq] using
      Data.Gaussian.Field.inv_mul
        (anchor * (1 + u)) productNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    productNonzero
  calc
    ((1 + u)⁻¹ * anchor⁻¹) * (anchor * (1 + u)) =
        ((1 + u)⁻¹ * (1 + u)) * (anchor⁻¹ * anchor) := by
      ring1
    _ = 1 := by
      rw [oneAddCancel, anchorCancel,
        Data.Gaussian.Basic.one_mul]
    _ = (anchor * (1 + u))⁻¹ * (anchor * (1 + u)) :=
      productCancel.symm

end Purelib.Approximation.Gaussian.Logarithm.OnePlus.Derivative.Affine

end
