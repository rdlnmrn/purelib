module
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.SignedFraction.Normalization
public import Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Rational.Bounds

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Int

section
@[expose] public section

/-!
# Divine Proportions, Example 14.10

The rational exclusion is the finite Eisenstein-at-seven argument applied to
the computable gcd-reduced numerator and denominator.  The three decimal
displays are retained as exact rational sign-change brackets; no completed
decimal field, real root, or limit object is introduced.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFourteenRational

namespace ChapterFourteenExamples.ExampleFourteenTen

section
open Purelib.Data.Rat
open Purelib.Data.Rat.SignedFraction
/-- The exact lower endpoint 0.188255 of the first cubic sign bracket. -/
def firstLower : Fraction.Rational :=
  Normalization.ofFraction
    ⟨37651, ((200000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (200000 : Nat))⟩
/-- The exact upper endpoint 0.188256 of the first cubic sign bracket. -/
def firstUpper : Fraction.Rational :=
  Normalization.ofFraction
    ⟨5883, ((31250 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (31250 : Nat))⟩
/-- The exact lower endpoint 0.611260 of the second cubic sign bracket. -/
def secondLower : Fraction.Rational :=
  Normalization.ofFraction
    ⟨30563, ((50000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (50000 : Nat))⟩
/-- The exact upper endpoint 0.611261 of the second cubic sign bracket. -/
def secondUpper : Fraction.Rational :=
  Normalization.ofFraction
    ⟨611261, ((1000000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (1000000 : Nat))⟩
/-- The exact lower endpoint 0.950484 of the third cubic sign bracket. -/
def thirdLower : Fraction.Rational :=
  Normalization.ofFraction
    ⟨237621, ((250000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (250000 : Nat))⟩
/-- The exact upper endpoint 0.950485 of the third cubic sign bracket. -/
def thirdUpper : Fraction.Rational :=
  Normalization.ofFraction
    ⟨190097, ((200000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (200000 : Nat))⟩

end

open Purelib.Data.Rat.Fraction.Cast
open Purelib.Polynomial.Recurrence.Spread.Roots.Seven.Rational
open formalisations.DivineProportions.Chapters.Examples.ChapterFourteenRational.ChapterFourteenExamples
/-- Exact finite evidence behind the three printed decimal approximations:
each displayed millionth-width rational interval has ordered endpoints and
opposite cubic signs. -/
theorem first_rational_bracket :
    ExampleFourteenTen.firstLower < ExampleFourteenTen.firstUpper ∧ Bounds.cubic ExampleFourteenTen.firstUpper < 0 ∧ 0 <
      Bounds.cubic ExampleFourteenTen.firstLower := by
  refine ⟨by decide, ?_, ?_⟩
  · exact Bounds.cubic_negative 5883 31250 (by decide) (by
      rw [show Bounds.clearedCubic 5883 31250 = -567349768 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (-567349768 : Int) < 0 by omega0))
  · exact Bounds.cubic_positive 37651 200000 (by decide) (by
      rw [show Bounds.clearedCubic 37651 200000 = 16354851136 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (0 : Int) < 16354851136 by omega0))

/-- The second exact millionth interval has ordered endpoints and a negative-to-positive cubic sign change. -/
theorem second_rational_bracket :
    ExampleFourteenTen.secondLower < ExampleFourteenTen.secondUpper ∧ Bounds.cubic ExampleFourteenTen.secondLower < 0 ∧
      0 < Bounds.cubic ExampleFourteenTen.secondUpper := by
  refine ⟨by decide, ?_, ?_⟩
  · exact Bounds.cubic_negative 30563 50000 (by decide) (by
      rw [show Bounds.clearedCubic 30563 50000 = -536067008 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (-536067008 : Int) < 0 by omega0))
  · exact Bounds.cubic_positive 611261 1000000 (by decide) (by
      rw [show Bounds.clearedCubic 611261 1000000 = 4895051354816 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (0 : Int) < 4895051354816 by omega0))

/-- The third exact millionth interval has ordered endpoints and a positive-to-negative cubic sign change. -/
theorem third_rational_bracket :
    ExampleFourteenTen.thirdLower < ExampleFourteenTen.thirdUpper ∧ Bounds.cubic ExampleFourteenTen.thirdUpper < 0 ∧ 0 <
      Bounds.cubic ExampleFourteenTen.thirdLower := by
  refine ⟨by decide, ?_, ?_⟩
  · exact Bounds.cubic_negative 190097 200000 (by decide) (by
      rw [show Bounds.clearedCubic 190097 200000 = -74937131072 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (-74937131072 : Int) < 0 by omega0))
  · exact Bounds.cubic_positive 237621 250000 (by decide) (by
      rw [show Bounds.clearedCubic 237621 250000 = 112205020096 by
        unfold Bounds.clearedCubic
        decide +kernel]
      simpa only [Purelib.Algebra.Ring.IntCast.cast_zero] using
        Order.intCast_lt_direct
          (show (0 : Int) < 112205020096 by omega0))

end ChapterFourteenExamples.ExampleFourteenTen

end formalisations.DivineProportions.Chapters.Examples.ChapterFourteenRational

end
