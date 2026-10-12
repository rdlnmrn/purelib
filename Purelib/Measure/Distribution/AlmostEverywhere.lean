module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Equality away from displayed zero weight

This is a finite replacement for almost-everywhere reasoning.  It quantifies
only over the supplied list of weighted atoms: two evaluations may differ at
an atom only when that atom carries exactly zero rational weight.
-/

namespace Purelib.Measure
namespace EqualOffZeroWeightOn
end EqualOffZeroWeightOn
namespace Distribution

open Purelib.Data.Rat in
/-- Agreement away from zero-weight retained occurrences preserves expectation. -/
theorem expectation_congr_off_zero {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.expectation left = distribution.expectation right :=
  expectationWeight_congr_off_zero distribution.atoms left right equal

/-- Boolean agreement away from zero-weight retained occurrences preserves probability. -/
theorem probability_congr_off_zero {α : Type}
    (distribution : Distribution α) (left right : α → Bool)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.probability left = distribution.probability right :=
  eventWeight_congr_off_zero distribution.atoms left right equal

open Purelib.Data.Rat in
/-- Observables agreeing outside a zero-probability event on retained occurrences have equal expectation. -/
theorem expectation_eq_of_equalOutsideZeroEvent {α : Type}
    (distribution : Distribution α) (exceptional : α → Bool)
    (left right : α → Fraction.Rational)
    (zero : distribution.probability exceptional = 0)
    (outside : EqualOutsideEventOn distribution.atoms exceptional left right) :
    distribution.expectation left = distribution.expectation right := by
  apply distribution.expectation_congr_off_zero
  exact equalOffZeroWeight_of_equalOutsideEvent distribution.atoms exceptional
    left right zero outside

/-- Boolean events agreeing outside a zero-probability exceptional event have equal probability. -/
theorem probability_eq_of_equalOutsideZeroEvent {α : Type}
    (distribution : Distribution α) (exceptional left right : α → Bool)
    (zero : distribution.probability exceptional = 0)
    (outside : EqualOutsideEventOn distribution.atoms exceptional left right) :
    distribution.probability left = distribution.probability right := by
  apply distribution.probability_congr_off_zero
  exact equalOffZeroWeight_of_equalOutsideEvent distribution.atoms exceptional
    left right zero outside

end Distribution

end Purelib.Measure

end
