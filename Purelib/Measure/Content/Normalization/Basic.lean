module
public import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Operations
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Normalizing positive finite contents

Any displayed finite rational content with explicitly positive total mass can
be normalized by direct rational scaling.  Event probabilities and
expectations are exactly the original finite measure and integral divided by
that displayed total.
-/

namespace Purelib.Measure

namespace Content

open Purelib.Data.Rat in
/-- Scale the exact content atom list by reciprocal total mass to obtain a distribution when that mass is positive.

Keep the original payload order and every occurrence. Positivity certifies the nonnegative scale and permits
cancellation in the retained unit-total proof. -/
def normalize {α : Type} (content : Content α)
    (positive : 0 < content.total) : Distribution α where
  atoms := scaleAtoms (1 / content.total)
    (Fraction.Order.Field.div_nonneg_direct (by decide) positive.le)
    content.atoms
  total_one := by
    rw [totalWeight_scaleAtoms]
    exact Fraction.Field.div_mul_cancel_of_ne
      1 content.total positive.ne'

/-- Normalization preserves the original content occurrence count. -/
theorem normalize_atoms_length {α : Type} (content : Content α)
    (positive : 0 < content.total) :
    (content.normalize positive).atoms.length = content.atoms.length :=
  scaleAtoms_length _ _ content.atoms

open Purelib.Data.Rat
/-- Normalized event probability is the original event mass divided by original total mass. -/
theorem normalize_probability {α : Type} (content : Content α)
    (positive : 0 < content.total) (event : α → Bool) :
    (content.normalize positive).probability event =
      content.measure event / content.total := by
  unfold Distribution.probability normalize measure
  rw [eventWeight_scaleAtoms]
  change (1 * content.total⁻¹) * eventWeight content.atoms event =
    eventWeight content.atoms event * content.total⁻¹
  rw [Fraction.Field.one_mul]
  exact Fraction.Field.mul_comm _ _

/-- Normalized expectation is the original integral divided by original total mass. -/
theorem normalize_expectation {α : Type} (content : Content α)
    (positive : 0 < content.total) (value : α → Fraction.Rational) :
    (content.normalize positive).expectation value =
      content.integral value / content.total := by
  unfold Distribution.expectation normalize integral
  rw [expectationWeight_scaleAtoms]
  change (1 * content.total⁻¹) *
      Distribution.expectationWeight content.atoms value =
    Distribution.expectationWeight content.atoms value * content.total⁻¹
  rw [Fraction.Field.one_mul]
  exact Fraction.Field.mul_comm _ _

/-- Multiplying normalized probability by the positive original total recovers the original event mass. -/
theorem normalize_probability_mul_total {α : Type}
    (content : Content α) (positive : 0 < content.total)
    (event : α → Bool) :
    (content.normalize positive).probability event * content.total =
      content.measure event := by
  rw [content.normalize_probability positive event]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- Multiplying normalized expectation by the positive original total recovers the original integral. -/
theorem normalize_expectation_mul_total {α : Type}
    (content : Content α) (positive : 0 < content.total)
    (value : α → Fraction.Rational) :
    (content.normalize positive).expectation value * content.total =
      content.integral value := by
  rw [content.normalize_expectation positive value]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

end Content

end Purelib.Measure
