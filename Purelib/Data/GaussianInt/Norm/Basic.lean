module
public import Mathlib.Algebra.Group.Nat.Defs

public import Purelib.Data.GaussianInt.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic

open Purelib.Data

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- A positive integer has positive natural absolute value.

Strict positivity excludes zero and the negative integer constructor. -/
private theorem natAbs_pos_of_pos {value : Int} (positive : 0 < value) :
    0 < value.natAbs := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => cases positive
      | succ value => exact Nat.zero_lt_succ value
  | negSucc value => cases positive
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- Compute integral Gaussian quadrance as the sum of the two coordinate squares. -/
def normInt (z : GaussianInt) : Int := z.re * z.re + z.im * z.im
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- The integer norm vanishes exactly at the zero Gaussian integer. -/
theorem normInt_eq_zero {z : GaussianInt} : normInt z = 0 ↔ z = 0 := by
  constructor
  · intro normZero
    have realNonnegative : 0 ≤ z.re * z.re := Purelib.Data.Int.Order.mul_self_nonneg z.re
    have imagNonnegative : 0 ≤ z.im * z.im := Purelib.Data.Int.Order.mul_self_nonneg z.im
    have squaresZero := Order.eq_zero_of_add_nonneg_eq_zero
      realNonnegative imagNonnegative normZero
    have realZero := squaresZero.1
    have imagZero := squaresZero.2
    have realCoordinateZero : z.re = 0 :=
      (Arithmetic.eq_zero_of_mul_eq_zero realZero).elim id id
    have imagCoordinateZero : z.im = 0 :=
      (Arithmetic.eq_zero_of_mul_eq_zero imagZero).elim id id
    ext <;> assumption
  · rintro rfl
    rfl
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- Integral Gaussian quadrance is multiplicative. -/
theorem normInt_mul (z w : GaussianInt) :
    normInt (z * w) = normInt z * normInt w := by
  simp only [normInt, mul_re, mul_im]
  ring1
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- The displayed integer norm is nonnegative. -/
theorem normInt_nonneg (z : GaussianInt) : 0 ≤ normInt z := by
  exact Order.add_nonneg (Purelib.Data.Int.Order.mul_self_nonneg z.re) (Purelib.Data.Int.Order.mul_self_nonneg z.im)
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- A nonzero Gaussian integer has positive integer norm. -/
theorem normInt_pos {z : GaussianInt} (nonzero : z ≠ 0) : 0 < normInt z := by
  have nonnegative := normInt_nonneg z
  have notZero : normInt z ≠ 0 := fun equal => nonzero (normInt_eq_zero.mp equal)
  exact Order.lt_of_le_of_ne nonnegative (Ne.symm notZero)
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- Compute natural Gaussian quadrance as the absolute value of its integral sum of
squares. -/
def normNat (z : GaussianInt) : Nat := (normInt z).natAbs
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- Natural Gaussian quadrance is multiplicative. -/
@[simp] theorem normNat_mul (z w : GaussianInt) :
    normNat (z * w) = normNat z * normNat w := by
  rw [normNat, normInt_mul, Arithmetic.natAbs_mul]
  rfl
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- Negating both Gaussian-integer coordinates preserves natural quadrance. -/
@[simp] theorem normNat_neg (z : GaussianInt) : normNat (-z) = normNat z := by
  apply congrArg Int.natAbs
  simp only [normInt, neg_re, neg_im]
  ring1
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- The norm of a displayed natural Gaussian integer is its natural square. -/
@[simp] theorem normNat_ofNat (value : Nat) :
    normNat (ofNat value) = Nat.pow value 2 := by
  change (((value : Int) * (value : Int) + 0 * 0 : Int).natAbs) = Nat.pow value 2
  rw [Int.mul_zero, Int.add_zero, ← Int.natCast_mul, Int.natAbs_natCast]
  change value * value = (1 * value) * value
  rw [Nat.one_mul]

end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

end

section
section
@[expose] public section
namespace Purelib.Data.GaussianInt

/-- A nonzero Gaussian integer has strictly positive natural quadrance. -/
theorem normNat_pos {z : GaussianInt} (nonzero : z ≠ 0) : 0 < normNat z := by
  exact natAbs_pos_of_pos (normInt_pos nonzero)
end Purelib.Data.GaussianInt
end

end

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

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

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- The natural norm is the sum of the two natural coordinate squares.

The original integer coordinate squares are nonnegative, so their sum's
magnitude retains ordinary natural addition and multiplication. -/
theorem normNat_eq_component_squares (value : GaussianInt) :
    GaussianInt.normNat value =
      Nat.pow value.re.natAbs 2 + Nat.pow value.im.natAbs 2 := by
  unfold GaussianInt.normNat GaussianInt.normInt
  rw [Int.natAbs_add_of_nonneg (Purelib.Data.Int.Order.mul_self_nonneg value.re)
    (Purelib.Data.Int.Order.mul_self_nonneg value.im), Arithmetic.natAbs_mul,
    Arithmetic.natAbs_mul]
  change value.re.natAbs * value.re.natAbs + value.im.natAbs * value.im.natAbs =
    (1 * value.re.natAbs) * value.re.natAbs + (1 * value.im.natAbs) * value.im.natAbs
  rw [Nat.one_mul, Nat.one_mul]

end Purelib.Data.GaussianInt.Norm.Basic

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

/-- Conjugate the displayed Gaussian integer by negating its imaginary coordinate. -/
def conjugate (value : GaussianInt) : GaussianInt :=
  ⟨value.re, -value.im⟩
end Purelib.Data.GaussianInt.Norm.Basic

end

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Norm in
/-- The imaginary coordinate of integral conjugation is the original coordinate's
negation. -/
@[simp] theorem conjugate_im (value : GaussianInt) :
    (conjugate value).im = -value.im := rfl
end Purelib.Data.GaussianInt.Norm.Basic

end

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Norm in
/-- Integral conjugation preserves the real coordinate. -/
@[simp] theorem conjugate_re (value : GaussianInt) :
    (conjugate value).re = value.re := rfl
end Purelib.Data.GaussianInt.Norm.Basic

end

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- Every displayed integer square is nonnegative. -/
private theorem int_mul_self_nonneg (value : Int) :
    0 ≤ value * value := by
  by_cases zero : value = 0
  · rw [zero]
    exact Order.le_refl 0
  · exact Order.le_of_lt (Order.mul_self_pos zero)
end Purelib.Data.GaussianInt.Norm.Basic

end

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.Int

/-- Casting the natural norm retains its nonnegative integer display. -/
theorem normInt_eq_natCast_normNat (value : GaussianInt) :
    GaussianInt.normInt value = (GaussianInt.normNat value : Int) := by
  rw [GaussianInt.normNat, Order.natAbs_of_nonneg (GaussianInt.normInt_nonneg value)]
end Purelib.Data.GaussianInt.Norm.Basic

end

end

section
section
@[expose] public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Norm in
/-- A Gaussian integer with zero natural quadrance is zero. -/
theorem eq_zero_of_normNat_eq_zero {value : GaussianInt}
    (zeroNorm : GaussianInt.normNat value = 0) : value = 0 := by
  apply normInt_eq_zero.mp
  rw [normInt_eq_natCast_normNat, zeroNorm]
  rfl
end Purelib.Data.GaussianInt.Norm.Basic

end

end
