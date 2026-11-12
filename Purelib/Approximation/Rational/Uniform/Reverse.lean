module
public import Purelib.Approximation.Rational.Uniform.Modulus
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Reversing a rational unit-interval source

The same effective radius controls the original source read at `1 - point`.
The proof compares the original two rational queries in the opposite order.
-/

public section

namespace Purelib.Approximation.Rational.Uniform

open Purelib.Data.Rat

/-- Read the original source at the reflected rational unit parameter. -/
@[expose] def reversed (source : Fraction.Rational → Fraction.Rational)
    (point : Fraction.Rational) : Fraction.Rational := source (1 - point)

/-- Reverse an effective unit-interval modulus without changing its computed radius.

The reflected ordered points are compared in the opposite order by the
original modulus. Both requested variation bounds are transported by exact
rational arithmetic. -/
@[expose] def Modulus.reversed {source : Fraction.Rational → Fraction.Rational} (modulus : Modulus source) :
    Modulus (Uniform.reversed source) where
  radius := modulus.radius
  radius_pos := modulus.radius_pos
  variation := by
    intro variation positive first second lower ordered upper small
    have reflectedLower : 0 ≤ 1 - second := Fraction.Order.Arithmetic.sub_nonneg_direct upper
    have reflectedOrdered : 1 - second ≤ 1 - first :=
      Fraction.Order.Arithmetic.sub_le_sub_left_direct ordered 1
    have reflectedUpper : 1 - first ≤ 1 := by
      have shifted := Fraction.Order.Arithmetic.sub_le_sub_left_direct lower 1
      have identity : (1 : Fraction.Rational) - 0 = 1 := by ring1
      rw [identity] at shifted
      exact shifted
    have distance : (1 - first) - (1 - second) = second - first := by ring1
    have reflectedSmall : (1 - first) - (1 - second) < modulus.radius variation := distance ▸ small
    have original := modulus.variation variation positive (1 - second) (1 - first)
      reflectedLower reflectedOrdered reflectedUpper reflectedSmall
    have secondAdded := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp original.1
    exact ⟨Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr original.2, secondAdded⟩

end Purelib.Approximation.Rational.Uniform

end
