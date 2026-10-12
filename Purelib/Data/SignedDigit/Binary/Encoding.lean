module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.SignedDigit.Binary.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section
public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Data.SignedDigit.Binary

open Purelib.Data.Rat in
set_option genInjectivity false in
open Purelib.Data.SignedDigit in
/-- Retain a signed-digit word of the requested depth with its bounded residual and exact reconstruction.

The source value equals the exact prefix value plus the retained residual scaled by one half to the retained depth. Word
length and residual bounds belong to those same stored fields. -/
structure Encoding (value : Fraction.Rational) (depth : Nat) where
  /-- The retained finite signed-digit word. -/ digits : List Binary.Basic.Digit
  /-- Evidence that the retained word length equals the requested depth. -/ length_eq : digits.length = depth
  /-- The exact residual left after the retained digit word. -/ finalResidual : Fraction.Rational
  /-- Evidence that the retained residual lies between minus one and one. -/ final_bounded : Binary.Basic.Bounded
    finalResidual
  /-- The source value equals the exact prefix plus the depth-scaled retained residual. -/ reconstruct : value =
    Binary.Basic.prefixValue digits +
    finalResidual * (1 / 2 : Fraction.Rational) ^ depth

constructive_injectivity Encoding

section
open Purelib.Data.Rat
open Purelib.Data.SignedDigit
namespace Encoding

/-- Compute a finite signed binary encoding of a bounded rational at the requested depth.

At zero depth retain the original value as residual. Each successor selects the deterministic signed digit and recurses
on its bounded residual, preserving the exact reconstruction equation. -/
@[expose] def encode (value : Fraction.Rational) (bounded : Binary.Basic.Bounded value) :
    (depth : Nat) → Encoding value depth
  | 0 =>
      { digits := []
        length_eq := rfl
        finalResidual := value
        final_bounded := bounded
        reconstruct := by
          change value = 0 + value * (1 / 2 : Fraction.Rational) ^ 0
          ring1 }
  | depth + 1 =>
      let digit := Binary.Basic.select value
      let next := Binary.Basic.residual digit value
      let encoded := Purelib.Data.SignedDigit.Binary.Encoding.encode next
        (Purelib.Data.SignedDigit.Binary.Basic.select_residual_bounded bounded) depth
      { digits := digit :: encoded.digits
        length_eq := congrArg Nat.succ encoded.length_eq
        finalResidual := encoded.finalResidual
        final_bounded := encoded.final_bounded
        reconstruct := by
          have first : value =
              (digit.value + next) * (1 / 2 : Fraction.Rational) := by
            dsimp only [next, Binary.Basic.residual]
            calc
              value = value * (2 * (1 / 2 : Fraction.Rational)) := by
                rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
                ring1
              _ = (digit.value + (2 * value - digit.value)) *
                  (1 / 2 : Fraction.Rational) := by ring1
          calc
            value = (digit.value + next) * (1 / 2 : Fraction.Rational) := first
            _ = (digit.value +
                  (Binary.Basic.prefixValue encoded.digits + encoded.finalResidual *
                    (1 / 2 : Fraction.Rational) ^ depth)) * (1 / 2) :=
              congrArg (fun candidate : Fraction.Rational =>
                (digit.value + candidate) * (1 / 2)) encoded.reconstruct
            _ = Binary.Basic.prefixValue (digit :: encoded.digits) +
                encoded.finalResidual * (1 / 2 : Fraction.Rational) ^ (depth + 1) := by
              simp only [Binary.Basic.prefixValue, pow_succ]
              ring1 }

/-- Require a candidate rational to lie within one half to the retained depth of the exact prefix center. -/
@[expose] def Contains {value : Fraction.Rational} {depth : Nat}
    (encoding : Encoding value depth) (candidate : Fraction.Rational) : Prop :=
  Binary.Basic.prefixValue encoding.digits - (1 / 2 : Fraction.Rational) ^ depth ≤ candidate ∧
    candidate ≤ Binary.Basic.prefixValue encoding.digits + (1 / 2 : Fraction.Rational) ^ depth

/-- The source value belongs to its retained signed-digit cylinder. -/
theorem contains_value {value : Fraction.Rational} {depth : Nat}
    (encoding : Encoding value depth) : encoding.Contains value := by
  let factor := (1 / 2 : Fraction.Rational) ^ depth
  have factorNonnegative : 0 ≤ factor :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth
  have lowerProduct : -factor ≤ encoding.finalResidual * factor := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        encoding.final_bounded.1 factorNonnegative
    calc
      -factor = (-1 : Fraction.Rational) * factor := by ring1
      _ ≤ encoding.finalResidual * factor := scaled
  have upperProduct : encoding.finalResidual * factor ≤ factor := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        encoding.final_bounded.2 factorNonnegative
    calc
      encoding.finalResidual * factor ≤ (1 : Fraction.Rational) * factor := scaled
      _ = factor := by ring1
  change
    Binary.Basic.prefixValue encoding.digits - factor ≤ value ∧
      value ≤ Binary.Basic.prefixValue encoding.digits + factor
  exact ⟨by
      calc
        Binary.Basic.prefixValue encoding.digits - factor ≤
            Binary.Basic.prefixValue encoding.digits + encoding.finalResidual * factor :=
          calc
            Binary.Basic.prefixValue encoding.digits - factor =
                -factor + Binary.Basic.prefixValue encoding.digits := by ring1
            _ ≤ encoding.finalResidual * factor +
                Binary.Basic.prefixValue encoding.digits :=
              Fraction.Order.Arithmetic.add_le_add_right_direct
                lowerProduct _
            _ = Binary.Basic.prefixValue encoding.digits +
                encoding.finalResidual * factor := by ring1
        _ = value := encoding.reconstruct.symm,
    by
      calc
        value = Binary.Basic.prefixValue encoding.digits +
            encoding.finalResidual * factor := encoding.reconstruct
        _ ≤ Binary.Basic.prefixValue encoding.digits + factor :=
          calc
            Binary.Basic.prefixValue encoding.digits + encoding.finalResidual * factor =
                encoding.finalResidual * factor +
                  Binary.Basic.prefixValue encoding.digits := by ring1
            _ ≤ factor + Binary.Basic.prefixValue encoding.digits :=
              Fraction.Order.Arithmetic.add_le_add_right_direct
                upperProduct _
            _ = Binary.Basic.prefixValue encoding.digits + factor := by ring1⟩

/-! ## Executable encoding and quantitative geometry -/

/-- Increasing the requested depth extends the exact deterministic signed-digit word. -/
theorem encode_digits_prefix (value : Fraction.Rational) (bounded : Binary.Basic.Bounded value)
    (depth extra : Nat) :
    (Binary.Encoding.encode value bounded depth).digits.IsPrefix
      (Binary.Encoding.encode value bounded (depth + extra)).digits := by
  induction depth generalizing value with
  | zero => exact List.nil_prefix
  | succ depth inductionHypothesis =>
      let digit := Binary.Basic.select value
      let next := Binary.Basic.residual digit value
      have nextBounded : Binary.Basic.Bounded next := Binary.Basic.select_residual_bounded bounded
      rw [show depth + 1 + extra = (depth + extra) + 1 by omega]
      change (digit :: (Binary.Encoding.encode next nextBounded depth).digits).IsPrefix
        (digit :: (Binary.Encoding.encode next nextBounded (depth + extra)).digits)
      rcases inductionHypothesis next nextBounded with ⟨suffix, identity⟩
      refine ⟨suffix, ?_⟩
      simpa only [List.cons_append] using congrArg (List.cons digit) identity

/-- Dividing a rational between the signed endpoints of a positive scale gives a value in the closed unit interval. -/
theorem normalized_bounded {value scale : Fraction.Rational}
    (scalePositive : 0 < scale)
    (bounds : -scale ≤ value ∧ value ≤ scale) :
    Binary.Basic.Bounded (value / scale) := by
  constructor
  · apply (Fraction.Order.Field.le_div_iff_pos scalePositive).2
    calc
      (-1 : Fraction.Rational) * scale = -scale := by ring1
      _ ≤ value := bounds.1
  · apply (Fraction.Order.Field.div_le_iff_pos scalePositive).2
    calc
      value ≤ scale := bounds.2
      _ = 1 * scale := by ring1

end Encoding
end

open Purelib.Data.SignedDigit
namespace Encoding

/-- The two retained unequal length-two signed-digit words have the same rational prefix value. -/
theorem nonunique_prefix_center :
    Binary.Basic.prefixValue [Binary.Basic.Digit.positive, Binary.Basic.Digit.negative] =
      Binary.Basic.prefixValue [Binary.Basic.Digit.zero, Binary.Basic.Digit.positive] := by
  decide

/-- The retained length-two words positive-negative and zero-positive are syntactically unequal. -/
theorem nonunique_prefix_syntax :
    [Binary.Basic.Digit.positive, Binary.Basic.Digit.negative] ≠
      [Binary.Basic.Digit.zero, Binary.Basic.Digit.positive] := by
  decide

end Encoding
end Purelib.Data.SignedDigit.Binary

end
