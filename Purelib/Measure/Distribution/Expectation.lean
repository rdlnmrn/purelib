module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure
namespace Distribution

section
open Purelib.Data.Rat
/-- Integrate the rational observable over the distribution's exact normalized occurrence list. -/
def expectation {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  expectationWeight distribution.atoms value

/-- Pointwise equal observables have equal expectation under the same retained distribution. -/
theorem expectation_congr {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.expectation left = distribution.expectation right :=
  expectationWeight_congr distribution.atoms left right pointwise

/-- Expectation preserves pointwise addition of rational observables. -/
theorem expectation_add {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.expectation (fun item => left item + right item) =
      distribution.expectation left + distribution.expectation right :=
  expectationWeight_add distribution.atoms left right

/-- A rational scalar factors out of expectation. -/
theorem expectation_scale {α : Type} (distribution : Distribution α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    distribution.expectation (fun item => factor * value item) =
      factor * distribution.expectation value :=
  expectationWeight_scale distribution.atoms factor value

/-- An observable nonnegative on every retained distribution occurrence has nonnegative expectation. -/
theorem expectation_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item) :
    0 ≤ distribution.expectation value :=
  expectationWeight_nonneg distribution.atoms value nonnegative

/-- Pointwise comparison on the retained distribution occurrences bounds expectations. -/
theorem expectation_mono {α : Type} (distribution : Distribution α)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      lower atom.item ≤ upper atom.item) :
    distribution.expectation lower ≤ distribution.expectation upper :=
  expectationWeight_mono distribution.atoms lower upper pointwise

/-- Bound the probability of a threshold event by expectation divided by its positive threshold.

The rational observable is nonnegative on every retained occurrence and at least the threshold wherever the Boolean
event selects it. Both probability and expectation use the same exact distribution. -/
theorem markov_bound {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Fraction.Rational)
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (nonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ value atom.item)
    (selectedLower : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true → threshold ≤ value atom.item) :
    distribution.probability event ≤
      distribution.expectation value / threshold := by
  apply (Fraction.Order.Field.le_div_iff_pos positive).2
  have bounded := threshold_mul_eventWeight_le_expectationWeight
    distribution.atoms event value threshold nonnegative selectedLower
  change eventWeight distribution.atoms event * threshold ≤
    expectationWeight distribution.atoms value
  calc
    eventWeight distribution.atoms event * threshold =
        threshold * eventWeight distribution.atoms event := by ring1
    _ ≤ expectationWeight distribution.atoms value := bounded

/-- The expectation of a Boolean event indicator equals that event's probability.

The original head indicator contributes its retained weight when selected
and scalar zero otherwise. Scalar head equality and the certificate on the
same tail identify the unchanged integral and event scans. -/
theorem expectation_indicator {α : Type} (distribution : Distribution α)
    (event : α → Bool) :
    distribution.expectation (indicator event) =
      distribution.probability event :=
  expectationWeight_indicator distribution.atoms event

/-- A constant rational observable has expectation equal to that constant.

The original weighted constant integral is the retained total times the
constant. The distribution's own normalization certificate identifies that
same total with one, giving the scalar value directly. -/
theorem expectation_constant {α : Type} (distribution : Distribution α)
    (constant : Fraction.Rational) :
    distribution.expectation (fun _ => constant) = constant := by
  change expectationWeight distribution.atoms (fun _ => constant) = constant
  exact (weighted_constant distribution.atoms constant).trans
    ((congrArg (fun total => total * constant) distribution.total_one).trans
      (Fraction.Field.one_mul constant))

end

end Distribution

end Purelib.Measure

end

section
@[expose] public section

/-!
# Independence of finite rational events

Independence is an exact rational multiplication identity between three
finite event evaluations.  Event families remain displayed lists.
-/

namespace Purelib.Measure

/-- The expectation of two event indicators' product equals their intersection probability. -/
theorem Distribution.expectation_indicator_mul_indicator
    {α : Type} (distribution : Distribution α)
    (left right : α → Bool) :
    distribution.expectation (fun item =>
      indicator left item * indicator right item) =
      distribution.probability (intersectionEvent left right) := by
  calc
    distribution.expectation (fun item =>
        indicator left item * indicator right item) =
        distribution.expectation (indicator (intersectionEvent left right)) :=
      distribution.expectation_congr _ _ (fun item => by
        unfold indicator intersectionEvent
        cases left item <;> cases right item <;> rfl)
    _ = distribution.probability (intersectionEvent left right) :=
      distribution.expectation_indicator _
end Purelib.Measure

end
