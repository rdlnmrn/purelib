module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Jensen
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic

section
/-!
# Finite conditional Jensen inequalities

Conditioning and conditional expectation are finite rational averages.
Jensen's supporting-line proof therefore applies cellwise without any
measurable-function space or limiting argument.  Squaring gives fully
explicit cellwise and partition-level second-moment contraction.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace Distribution

/-- On a positive-probability event, the square of the conditional mean is bounded by the conditional square mean. -/
theorem conditionalMean_sq_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    distribution.conditionalMean event value ^ 2 ≤
      distribution.conditionalMean event (fun item => value item ^ 2) := by
  have nonnegative :=
    distribution.conditionalVariance_nonneg event positive value
  rw [distribution.conditionalVariance_eq_secondMoment_sub_sq
    event positive value] at nonnegative
  exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct nonnegative

/-- A supporting line on all retained conditioned occurrences gives Jensen's inequality for the exact conditional mean.
-/
theorem conditionalJensen_of_supportingLine {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) (transform : Fraction.Rational → Fraction.Rational)
    (slope : Fraction.Rational)
    (supports : ∀ atom,
      atom ∈ (distribution.conditioned event positive).atoms →
      transform
          ((distribution.conditioned event positive).expectation value) +
          slope *
            (value atom.item -
              (distribution.conditioned event positive).expectation value) ≤
        transform (value atom.item)) :
    transform (distribution.conditionalMean event value) ≤
      distribution.conditionalMean event
        (fun item => transform (value item)) := by
  rw [← distribution.conditioned_expectation_eq_conditionalMean
      event positive value,
    ← distribution.conditioned_expectation_eq_conditionalMean event positive
      (fun item => transform (value item))]
  exact (distribution.conditioned event positive).jensen_of_supportingLine
    value transform slope supports

/-- A supporting line on selected original occurrences suffices for Jensen's inequality on the positive-probability
event. -/
theorem conditionalJensen_of_supportingLine_on_event {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) (transform : Fraction.Rational → Fraction.Rational)
    (slope : Fraction.Rational)
    (supports : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
      transform (distribution.conditionalMean event value) +
          slope * (value atom.item -
            distribution.conditionalMean event value) ≤
        transform (value atom.item)) :
    transform (distribution.conditionalMean event value) ≤
      distribution.conditionalMean event
        (fun item => transform (value item)) := by
  let affine : α → Fraction.Rational := fun item =>
    transform (distribution.conditionalMean event value) +
      slope * (value item - distribution.conditionalMean event value)
  have affineMean : distribution.conditionalMean event affine =
      transform (distribution.conditionalMean event value) := by
    dsimp only [affine]
    rw [distribution.conditionalMean_add,
      distribution.conditionalMean_scale,
      distribution.conditionalMean_sub,
      distribution.conditionalMean_constant event positive,
      distribution.conditionalMean_constant event positive]
    ring1
  rw [← affineMean]
  exact distribution.conditionalMean_mono_on_event event positive affine
    (fun item => transform (value item)) supports

/-- The magnitude of a positive-event conditional mean is bounded by the corresponding conditional magnitude mean. -/
theorem conditionalMean_rationalSeparation_zero_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.conditionalMean event value) 0 ≤
      distribution.conditionalMean event (fun item =>
        Distance.rationalSeparation (value item) 0) := by
  rw [← distribution.conditioned_expectation_eq_conditionalMean
      event positive value,
    ← distribution.conditioned_expectation_eq_conditionalMean event positive
      (fun item => Distance.rationalSeparation (value item) 0)]
  exact (distribution.conditioned event positive)
    |>.jensen_rationalSeparation_zero value

end Distribution

namespace PositiveEventPartition
end PositiveEventPartition

end Purelib.Measure

end
