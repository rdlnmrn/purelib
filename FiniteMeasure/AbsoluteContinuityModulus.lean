import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EssentialMaximum
import FiniteMeasure.RadonNikodymExistence

/-!
# Explicit finite absolute-continuity moduli

The computed essential maximum of a finite Radon--Nikodym density bounds the
target content of every event by that constant times its source content.
Consequently absolute continuity has a requested rational epsilon--delta
modulus, constructed without compactness, an infimum, or an existential
choice.
-/

namespace FiniteMeasure

namespace AtomicChange.Witness

/-- Quantitative finite absolute continuity from the least displayed
essential density bound. -/
theorem measure_le_essentialMaximumDensity_mul {α : Type}
    {source target : FiniteContent α}
    (witness : AtomicChange.Witness source target)
    (event : α → Bool) :
    target.measure event ≤
      source.essentialMaximumMagnitude witness.density *
        source.measure event := by
  calc
    target.measure event = source.integral (fun item =>
          witness.density item * Distribution.indicator event item) :=
      witness.measure_eq event
    _ = source.integral (fun item =>
          Distribution.indicator event item * witness.density item) := by
      exact source.integral_congr _ _ (fun item => by ring1)
    _ ≤ source.integral (fun item =>
          source.essentialMaximumMagnitude witness.density *
            Distribution.indicator event item) := by
      apply source.integral_mono_off_zero
      intro atom member
      rcases source.essentiallyBoundedBy_essentialMaximumMagnitude
          witness.density atom member with zero | magnitudeBound
      · exact Or.inl zero
      · apply Or.inr
        have densityLe : witness.density atom.item ≤
            source.essentialMaximumMagnitude witness.density := by
          change rationalSeparation (witness.density atom.item) 0 ≤
            source.essentialMaximumMagnitude witness.density at magnitudeBound
          rw [rationalSeparation_zero_of_nonneg
            (witness.nonnegative atom.item)] at magnitudeBound
          exact magnitudeBound
        cases selected : event atom.item
        · simp only [Distribution.indicator, selected, zero_mul, mul_zero]
          exact le_rfl
        · simp only [Distribution.indicator, selected, one_mul, mul_one]
          exact densityLe
    _ = source.essentialMaximumMagnitude witness.density *
          source.measure event := by
      rw [source.integral_scale, source.integral_indicator]

end AtomicChange.Witness

namespace FiniteContent

/-- An executable epsilon--delta modulus for finite absolute continuity. -/
structure AbsoluteContinuityModulus {α : Type}
    (target source : FiniteContent α) where
  request : (epsilon : Coordinate) → 0 < epsilon → Coordinate
  request_positive : ∀ epsilon positive,
    0 < request epsilon positive
  controls : ∀ epsilon positive event,
    source.measure event < request epsilon positive →
      target.measure event < epsilon

end FiniteContent

namespace AtomicChange.Witness

/-- A finite density computes an explicit absolute-continuity modulus.  If
its essential maximum is zero, every positive request works; otherwise the
request is `epsilon / maximum`. -/
def absoluteContinuityModulus {α : Type}
    {source target : FiniteContent α}
    (witness : AtomicChange.Witness source target) :
    FiniteContent.AbsoluteContinuityModulus target source where
  request epsilon positive :=
    if source.essentialMaximumMagnitude witness.density = 0 then epsilon
    else epsilon / source.essentialMaximumMagnitude witness.density
  request_positive epsilon positive := by
    by_cases maximumZero :
        source.essentialMaximumMagnitude witness.density = 0
    · simp only [maximumZero, ↓reduceIte]
      exact positive
    · simp only [maximumZero, ↓reduceIte]
      have maximumPositive :
          0 < source.essentialMaximumMagnitude witness.density :=
        lt_of_le_of_ne
          (source.essentialMaximumMagnitude_nonnegative witness.density)
          (Ne.symm maximumZero)
      exact RFAP.ConstructiveFraction.div_pos_direct positive maximumPositive
  controls epsilon positive event small := by
    by_cases maximumZero :
        source.essentialMaximumMagnitude witness.density = 0
    · have bound := witness.measure_le_essentialMaximumDensity_mul event
      rw [maximumZero, zero_mul] at bound
      exact bound.trans_lt positive
    · have maximumPositive :
          0 < source.essentialMaximumMagnitude witness.density :=
        lt_of_le_of_ne
          (source.essentialMaximumMagnitude_nonnegative witness.density)
          (Ne.symm maximumZero)
      have sourceSmall : source.measure event <
          epsilon / source.essentialMaximumMagnitude witness.density := by
        simpa only [maximumZero, ↓reduceIte] using small
      have scaled :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          maximumPositive sourceSmall
      calc
        target.measure event ≤
            source.essentialMaximumMagnitude witness.density *
              source.measure event :=
          witness.measure_le_essentialMaximumDensity_mul event
        _ < source.essentialMaximumMagnitude witness.density *
              (epsilon /
                source.essentialMaximumMagnitude witness.density) := scaled
        _ = (epsilon /
              source.essentialMaximumMagnitude witness.density) *
                source.essentialMaximumMagnitude witness.density := by ring1
        _ = epsilon :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon
            (source.essentialMaximumMagnitude witness.density)
            maximumZero

end AtomicChange.Witness

namespace FiniteContent.AbsolutelyContinuous

/-- Every finite absolutely continuous target/source pair computes an
explicit rational modulus via the finite Radon--Nikodym existence theorem. -/
def modulus {α : Type} [DecidableEq α]
    {target source : FiniteContent α}
    (continuous : target.AbsolutelyContinuous source) :
    FiniteContent.AbsoluteContinuityModulus target source :=
  (AtomicChange.Witness.ofAbsolutelyContinuous source target continuous)
    |>.absoluteContinuityModulus

end FiniteContent.AbsolutelyContinuous

end FiniteMeasure
