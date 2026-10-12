module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.LayerCake
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite layer-cake identities

For a natural-valued observable, truncation at a displayed finite height is
the sum of its Boolean upper-level indicators.  Integrating this pointwise
identity gives an exact finite tail-sum, or layer-cake, formula.  There is no
infinite series and no improper integral.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Sum the original natural-valued observable's tail probabilities up to the supplied finite height. -/
def natTailProbabilitySum {α : Type} (distribution : Distribution α)
    (value : α → Nat) (height : Nat) : Fraction.Rational :=
  distribution.toContent.natTailMeasureSum value height

/-- Expectation of the observable truncated at the exact height equals its finite tail-probability sum. -/
theorem expectation_truncatedNat_eq_natTailProbabilitySum {α : Type}
    (distribution : Distribution α) (value : α → Nat)
    (height : Nat) :
    distribution.expectation (fun item =>
        ((min (value item) height : Nat) : Fraction.Rational)) =
      distribution.natTailProbabilitySum value height :=
  distribution.toContent.integral_truncatedNat_eq_natTailMeasureSum
    value height

/-- An observable bounded by the supplied height on every original atom has expectation equal to its finite
tail-probability sum. -/
theorem expectation_nat_eq_natTailProbabilitySum_of_bounded {α : Type}
    (distribution : Distribution α) (value : α → Nat) (height : Nat)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ height) :
    distribution.expectation (fun item => (value item : Fraction.Rational)) =
      distribution.natTailProbabilitySum value height :=
  distribution.toContent.integral_nat_eq_natTailMeasureSum_of_bounded
    value height bounded

end Distribution

end Purelib.Measure

end
