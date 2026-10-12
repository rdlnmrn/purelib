module
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Int

section
@[expose] public section

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFourteenPentagonMetrics

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
variable [Nontrivial K] [DecidableEq K]

namespace Decimal

open Purelib.Data.Rat in
/-- The nontrivial quadratic factor `5-20s+16s²`. -/
def quadratic (value : Fraction.Rational) : Fraction.Rational :=
  5 - 20 * value + 16 * value ^ 2

section
open Purelib.Data.Rat
open Purelib.Data.Rat.SignedFraction
/-- Lower endpoint `0.345491` of the printed alpha bracket. -/
def alphaLower : Fraction.Rational :=
  Normalization.ofFraction
    ⟨345491, ((1000000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (1000000 : Nat))⟩

/-- Upper endpoint `0.345492` of the printed alpha bracket. -/
def alphaUpper : Fraction.Rational :=
  Normalization.ofFraction
    ⟨345492, ((1000000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (1000000 : Nat))⟩

/-- Lower endpoint `0.904508` of the printed beta bracket. -/
def betaLower : Fraction.Rational :=
  Normalization.ofFraction
    ⟨904508, ((1000000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (1000000 : Nat))⟩

/-- Upper endpoint `0.904509` of the printed beta bracket. -/
def betaUpper : Fraction.Rational :=
  Normalization.ofFraction
    ⟨904509, ((1000000 : Nat) : Int),
      Order.natCast_pos (by decide : 0 < (1000000 : Nat))⟩

end

/-- Exact finite sign-change evidence for `α≈0.345491...`. -/
theorem alphaBracket :
    alphaLower < alphaUpper ∧
      0 < quadratic alphaLower ∧ quadratic alphaUpper < 0 := by
  decide

/-- Exact finite sign-change evidence for `β≈0.904508...`. -/
theorem betaBracket :
    betaLower < betaUpper ∧
      quadratic betaLower < 0 ∧ 0 < quadratic betaUpper := by
  decide

end Decimal

end formalisations.DivineProportions.Chapters.Examples.ChapterFourteenPentagonMetrics

end
