module
public import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Gauge
public import Purelib.Data.List.BinaryPrefix.Minimax
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Gauge

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingPrefixMinimaxWordAlias -> GaugeWord

open Purelib.Data.List.BinaryPrefix renaming CCLMeasureWord -> MeasureWord

section
public section

/-!
# Finite prefix minimax over the pure CCL bitstream

This module formalizes the information-theoretic theorem of Section 7.  It is
only about finite `List Bool` tags.  Chordal geometry, boxed names, arithmetic
sidecars, completed streams, and collections of all compatible values do not
occur here.
-/

namespace Purelib.Data.List.BinaryPrefix.Dyadic

/-- Assign the strictly shrinking positive dyadic weight two to the negative word length.

The retained gauge value is (1/2)^length. Exact rational positivity and
multiplication bounds certify positivity and strict contraction at either one-bit
child. -/
@[expose] def bitGauge : Gauge where
  value word := (1 / 2 : Rational) ^ word.length
  positive word :=
    Arithmetic.pow_pos_direct (by decide) word.length
  child_lt word bit := by
    rw [Append.length_append, List.length_singleton, pow_succ]
    let power := (1 / 2 : Rational) ^ word.length
    have powerPositive : 0 < power :=
      Arithmetic.pow_pos_direct (by decide) word.length
    calc
      power * (1 / 2 : Rational) = (1 / 2 : Rational) * power := by
        ring1
      _ < 1 * power :=
        Arithmetic.mul_lt_mul_of_pos_right_direct
          (by decide) powerPositive
      _ = power := Field.one_mul _

/-- At a genuine binary branch, every extending candidate has dyadic two-witness radius
(1/2)^stem.length.

The two retained witness words continue in opposite bit branches. The candidate must
extend their common stem; the finite minimax theorem then identifies its maximum
distance exactly. -/
theorem bitGauge_twoWitness_radius
    (stem candidate leftTail rightTail : GaugeWord)
    (candidatePrefix : stem.IsPrefix candidate) :
    Minimax.twoWitnessRadius bitGauge candidate
        (stem ++ false :: leftTail) (stem ++ true :: rightTail) =
      (1 / 2 : Rational) ^ stem.length := by
  exact (Minimax.twoWitness_minimax bitGauge stem candidate
    leftTail rightTail).1 candidatePrefix

end Purelib.Data.List.BinaryPrefix.Dyadic

end

section
public section

/-!
# Symbolic dyadic weight of raw CCL prefixes

This is the fair-bit valuation on the raw binary address tree.  It is a
symbolic prefix weight, not geometric area and not the pushforward of
Lebesgue measure through the CCL decoder.  The distinction is explicit in the
API.
-/

namespace Purelib.Data.List.BinaryPrefix

/-- Compute the symbolic dyadic weight (1/2)^length of a finite Boolean prefix. -/
@[expose] def rawPrefixWeight (word : MeasureWord) : Rational :=
  (1 / 2 : Rational) ^ word.length

/-- Every finite prefix has nonnegative symbolic dyadic weight. -/
theorem rawPrefixWeight_nonneg (word : MeasureWord) :
    0 ≤ rawPrefixWeight word :=
  Arithmetic.pow_nonneg_direct (by decide) word.length

/-- Every finite prefix has strictly positive symbolic dyadic weight. -/
theorem rawPrefixWeight_pos (word : MeasureWord) :
    0 < rawPrefixWeight word :=
  Arithmetic.pow_pos_direct (by decide) word.length

/-- The empty prefix has symbolic dyadic weight one. -/
@[simp] theorem rawPrefixWeight_nil : rawPrefixWeight [] = 1 := by
  simp only [-eq_self, -iff_self, rawPrefixWeight, List.length_nil, pow_zero]; try rfl

/-- The symbolic weight of a concatenation is the product of its two prefix weights. -/
theorem rawPrefixWeight_append (left right : MeasureWord) :
    rawPrefixWeight (left ++ right) =
      rawPrefixWeight left * rawPrefixWeight right := by
  simp only [-eq_self, -iff_self, rawPrefixWeight, Append.length_append, pow_add]; try rfl

/-- Appending one bit halves the symbolic dyadic weight. -/
theorem rawPrefixWeight_child (word : MeasureWord) (bit : Bool) :
    rawPrefixWeight (word ++ [bit]) = rawPrefixWeight word * (1 / 2) := by
  rw [rawPrefixWeight_append]
  change rawPrefixWeight word * (1 / 2 : Rational) ^ 1 = _
  rw [pow_one]

/-- The weights of the two one-bit children sum to their parent's weight. -/
theorem rawPrefixWeight_children_add (word : MeasureWord) :
    rawPrefixWeight (word ++ [false]) +
      rawPrefixWeight (word ++ [true]) = rawPrefixWeight word := by
  rw [rawPrefixWeight_child, rawPrefixWeight_child]
  calc
    rawPrefixWeight word * (1 / 2) + rawPrefixWeight word * (1 / 2) =
        rawPrefixWeight word * ((1 / 2 : Rational) + 1 / 2) := by ring1
    _ = rawPrefixWeight word * 1 := by
      have halves : (1 / 2 : Rational) + 1 / 2 = 1 := by decide
      rw [halves]
    _ = rawPrefixWeight word := by ring1

/-- Extending a finite prefix cannot increase its symbolic dyadic weight.

An explicit suffix factors the extended weight into the original weight and a
nonnegative power of one half bounded by one. -/
theorem rawPrefixWeight_le_of_prefix {stem word : MeasureWord}
    (isPrefix : stem.IsPrefix word) :
    rawPrefixWeight word ≤ rawPrefixWeight stem := by
  rcases isPrefix with ⟨suffix, equal⟩
  rw [← equal, rawPrefixWeight_append]
  have suffixLeOne : rawPrefixWeight suffix ≤ 1 := by
    have bound := Arithmetic.pow_le_pow_direct
      (by decide : (0 : Rational) ≤ 1 / 2)
      (by decide : (1 / 2 : Rational) ≤ 1) suffix.length
    simpa only [-eq_self, -iff_self, rawPrefixWeight, one_pow] using bound
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
    suffixLeOne (rawPrefixWeight_nonneg stem)
  simpa only [-eq_self, -iff_self, mul_one] using scaled
end Purelib.Data.List.BinaryPrefix

end
