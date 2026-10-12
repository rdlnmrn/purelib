module
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction.Construction
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Rat.SignedFraction.Normalization
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.SignedFraction.Basic

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Rat.Fraction

open Purelib.Data.Rat.SignedFraction

section
@[expose] public section

/-!
# Divine Proportions, Chapter 12 examples

Example 12.1 is a closed computation in the executable thirteen-element
field.  Example 12.2 uses exact Gaussian pairs over the project-owned
constructive rationals.  Only the literal points, lines, intersections, and
metric values printed by the source are evaluated; no field carrier is
enumerated.
-/

namespace Purelib.Data.Gaussian.Fraction.Construction

section ChapterTwelveExamples

section ExampleTwelveTwo

/-- Build a Gaussian rational from two integer numerators and natural denominator
parameters.

Each coordinate uses the retained rational_public constructor; the two independent
coordinate constructions form the exact displayed pair. -/
private def gaussian
    (realNumerator : Int) (realDenominator : Nat)
    (imaginaryNumerator : Int) (imaginaryDenominator : Nat) : Canonical :=
  ⟨Construction.rational realNumerator realDenominator,
    Construction.rational imaginaryNumerator imaginaryDenominator⟩

open Purelib.Data in
/-- Build a Gaussian rational from two signed fractions with successor natural
denominators.

The retained denominator parameters are increased by one, making both denominators
positive by construction. The signed-fraction normalization computes each exact
coordinate. -/
def displayedGaussian
    (realNumerator : Int) (realDenominator : Nat)
    (imaginaryNumerator : Int) (imaginaryDenominator : Nat) : Canonical :=
  ⟨Normalization.ofFraction
      ⟨realNumerator, Int.ofNat (realDenominator + 1),
        Int.Order.natCast_pos (Nat.zero_lt_succ realDenominator)⟩,
    Normalization.ofFraction
      ⟨imaginaryNumerator, Int.ofNat (imaginaryDenominator + 1),
        Int.Order.natCast_pos (Nat.zero_lt_succ imaginaryDenominator)⟩⟩
end ExampleTwelveTwo

end ChapterTwelveExamples

end Purelib.Data.Gaussian.Fraction.Construction

end
