module
import Purelib.Data.Nat.Order
import Purelib.Algebra.NatCast

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
public import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.GaussianInt.Norm

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Cast

open scoped Purelib.Data.Nat

section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data

/-- The natural quadrance is the sum of the squares of the two displayed
component magnitudes.

Both original integer coordinate squares are nonnegative, so natural
readback retains their sum and their individual magnitudes. -/
theorem normNat_eq_component_squares (z : GaussianInt) :
    normNat z = Nat.pow z.re.natAbs 2 + Nat.pow z.im.natAbs 2 :=
  Norm.Basic.normNat_eq_component_squares z
end Purelib.Data.GaussianInt
end

end

section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data

/-- The imaginary coordinate's natural magnitude is bounded by the Gaussian integer's
natural quadrance. -/
theorem imaginaryComponent_natAbs_le_normNat (z : GaussianInt) :
    z.im.natAbs ≤ normNat z := by
  rw [normNat_eq_component_squares]
  change z.im.natAbs ≤ (1 * z.re.natAbs) * z.re.natAbs +
    (1 * z.im.natAbs) * z.im.natAbs
  rw [Nat.one_mul, Nat.one_mul]
  exact (Nat.Order.le_mul_self _).trans (Nat.le_add_left _ _)

end Purelib.Data.GaussianInt
end

end

section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data

/-- The real coordinate's natural magnitude is bounded by the Gaussian integer's natural
quadrance. -/
theorem realComponent_natAbs_le_normNat (z : GaussianInt) :
    z.re.natAbs ≤ normNat z := by
  rw [normNat_eq_component_squares]
  change z.re.natAbs ≤ (1 * z.re.natAbs) * z.re.natAbs +
    (1 * z.im.natAbs) * z.im.natAbs
  rw [Nat.one_mul, Nat.one_mul]
  exact (Nat.Order.le_mul_self _).trans (Nat.le_add_right _ _)
end Purelib.Data.GaussianInt
end

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.GaussianInt.Norm.Bounds
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Algebra

/-- The displayed imaginary component magnitude does not exceed quadrance. -/
theorem imaginaryComponent_le_normNat (value : GaussianInt) :
    value.im.natAbs ≤ normNat value :=
  imaginaryComponent_natAbs_le_normNat value
end Purelib.Data.GaussianInt.Norm.Bounds

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.GaussianInt.Norm.Bounds
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Algebra

/-! ## Homogeneous Gaussian-integer evaluation -/

/-- The quadrance of a sum is bounded by twice the sum of quadrances.

Embedding the two retained integer inputs preserves addition and quadrance;
the coordinate square bound then transports back through the natural cast. -/
theorem normNat_add_le_two (left right : GaussianInt) :
    normNat (left + right) ≤ 2 * (normNat left + normNat right) := by
  apply (Order.natCast_le_iff_direct).1
  calc
    (normNat (left + right) : Rational) =
        Data.Gaussian.Norm.Basic.normSq (toGaussian left + toGaussian right) := by
      rw [← toGaussian_add, normSq_toGaussian]
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (toGaussian left) + Data.Gaussian.Norm.Basic.normSq (toGaussian right)) :=
      Bounds.normSq_add_le_two _ _
    _ = ((2 * (normNat left + normNat right) : Nat) : Rational) := by
      rw [normSq_toGaussian, normSq_toGaussian, NatCast.mul,
        NatCast.add, Nat.cast_ofNat]
end Purelib.Data.GaussianInt.Norm.Bounds

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.GaussianInt.Norm.Bounds
open Purelib.Data.Gaussian
open Purelib.Data.GaussianInt
open Purelib.Algebra

/-- The displayed real component magnitude does not exceed quadrance. -/
theorem realComponent_le_normNat (value : GaussianInt) :
    value.re.natAbs ≤ normNat value :=
  realComponent_natAbs_le_normNat value
end Purelib.Data.GaussianInt.Norm.Bounds

end
