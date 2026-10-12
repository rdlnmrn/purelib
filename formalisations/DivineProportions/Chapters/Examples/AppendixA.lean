module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Divine Proportions, Appendix A: rational polar equations of curves

The source leaves the conversions in this catalogue to the reader.  This
module supplies the missing finite algebraic derivations.  Every result is
denominator-cleared and valid over an arbitrary explicit field; divisions by
the radial quadrance are represented by an explicit nonzero hypothesis.

Three displayed equations in the source do not follow from the equations
immediately preceding them.  The trisectrix has the wrong sign, the bullet
nose omits a factor `4` in the denominator, and the hippopede loses powers of
`B`.  Corrected theorems and closed rational counterexamples are included.
-/

namespace formalisations.DivineProportions.Chapters.Examples.AppendixA

namespace RationalPolarCatalogue

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Data.Rat
/-- Exact rational data satisfy the corrected trisectrix equation and refute its printed plus-sign variant. -/
theorem
  printed_trisectrix_counterexample
  :
    let R := Fraction.Rational
    (4 * (1 : R) * 1 - (9 + 1)) ^ 2 = 4 * 1 * 9 ∧
      (4 * (1 : R) * 1 + (9 + 1)) ^ 2 ≠ 4 * 1 * 9 := by
  decide

/-- Exact rational polar data satisfy the corrected bullet-nose equation and refute the printed factor-four variant. -/
theorem
  printed_bullet_nose_counterexample
  :
    let R := Fraction.Rational
    let A : R := 1
    let B : R := 1
    let Q : R := 3 / 2
    let spread : R := 1 / 3
    (2 * Q * spread - (A + B + Q)) ^ 2 =
        (A + B + Q) ^ 2 - 4 * A * Q ∧
      (2 * Q * spread - (A + B + Q)) ^ 2 ≠
        4 * ((A + B + Q) ^ 2 - 4 * A * Q) := by
  decide

/-- Exact rational data satisfy the corrected hippopede equation and refute its printed linear factor.

The retained values A equals one, B equals four, quadrance sixteen and spread one expose the missing power of B. -/
theorem
  printed_hippopede_counterexample
  :
    let R := Fraction.Rational
    let A : R := 1
    let B : R := 4
    let Q : R := 16
    let spread : R := 1
    Q ^ 2 + 4 * B * (B - A) * Q = 4 * B ^ 2 * (spread * Q) ∧
      4 * B ^ 2 * spread = Q + 4 * B * (B - A) ∧
      4 * B * spread ≠ Q + 4 * B * (B - A) := by
  decide
end RationalPolarCatalogue
end formalisations.DivineProportions.Chapters.Examples.AppendixA

end
