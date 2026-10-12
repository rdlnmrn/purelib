module
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Distribution.Convergence.Bounded
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
/-!
# Root-free finite Lp comparison

An explicit essential magnitude ceiling converts a higher natural-powered
integral into a lower one with the expected ceiling factor.  The formulation
uses only rational powers and finite sums, avoiding roots and completed normed
spaces.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

section
open Purelib
open Purelib.Data.Rat
/-- Squared magnitude integral is bounded by total content mass times the square integral. -/
theorem poweredL1_sq_le_total_mul_poweredL2 {α : Type}
    (content : Measure.Content α) (value : α → Fraction.Rational) :
    content.poweredL1 value ^ 2 ≤
      content.total * content.poweredL2 value := by
  let magnitude := fun item => Distance.rationalSeparation (value item) 0
  let one := fun _ : α => (1 : Fraction.Rational)
  have cauchy := content.productIntegral_sq_le_poweredL2_mul magnitude one
  have productIdentity : content.productIntegral magnitude one =
      content.poweredL1 value := by
    unfold productIntegral poweredL1 magnitude one
    exact content.integral_congr _ _ (fun item => by ring1)
  have magnitudeIdentity : content.poweredL2 magnitude =
      content.poweredL2 value := by
    unfold poweredL2 magnitude
    exact content.integral_congr _ _ (fun item => by
      rw [Distance.NaturalLp.rationalSeparation_sq]
      ring1)
  have oneIdentity : content.poweredL2 one = content.total := by
    unfold poweredL2 one
    calc
      content.integral (fun _ : α => (1 : Fraction.Rational) ^ 2) =
          content.integral (fun _ => (1 : Fraction.Rational)) :=
        content.integral_congr _ _ (fun item => by ring1)
      _ = content.total * 1 := content.integral_constant 1
      _ = content.total := mul_one _
  rw [productIdentity, magnitudeIdentity, oneIdentity] at cauchy
  simpa only [mul_comm] using cauchy

/-- Squared integrated separation is bounded by total content mass times squared integrated distance. -/
theorem l1Distance_sq_le_total_mul_poweredL2Distance {α : Type}
    (content : Measure.Content α) (left right : α → Fraction.Rational) :
    content.l1Distance left right ^ 2 ≤
      content.total * content.poweredL2Distance left right := by
  have bound := content.poweredL1_sq_le_total_mul_poweredL2
    (fun item => left item - right item)
  rw [content.poweredL1_sub_eq_l1Distance] at bound
  exact bound

/-- An essential magnitude ceiling bounds the higher powered integral by its extra power times the lower powered
integral. -/
theorem poweredLp_add_le_of_essentialBound {α : Type}
    (content : Measure.Content α) (exponent extra : Nat)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredLp (exponent + extra) value ≤
      ceiling ^ extra * content.poweredLp exponent value := by
  unfold poweredLp
  calc
    content.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ (exponent + extra)) =
        content.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent *
            Distance.rationalSeparation (value item) 0 ^ extra) := by
      exact content.integral_congr _ _ (fun item => by rw [pow_add])
    _ ≤ content.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent *
            ceiling ^ extra) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.pow_le_pow_direct
            (Distance.rationalSeparation_nonneg _ _) bound extra)
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (Distance.rationalSeparation_nonneg _ _) exponent)
    _ = ceiling ^ extra * content.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent) := by
      calc
        content.integral (fun item =>
            Distance.rationalSeparation (value item) 0 ^ exponent *
              ceiling ^ extra) =
            content.integral (fun item => ceiling ^ extra *
              Distance.rationalSeparation (value item) 0 ^ exponent) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling ^ extra * content.integral (fun item =>
              Distance.rationalSeparation (value item) 0 ^ exponent) :=
          content.integral_scale _ _

/-- The computed essential maximum bounds every exponent increase by its corresponding extra power. -/
theorem poweredLp_add_le_essentialMaximum {α : Type}
    (content : Measure.Content α) (exponent extra : Nat)
    (value : α → Fraction.Rational) :
    content.poweredLp (exponent + extra) value ≤
      content.essentialMaximumMagnitude value ^ extra *
        content.poweredLp exponent value :=
  content.poweredLp_add_le_of_essentialBound exponent extra value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- The square integral is bounded by essential maximum magnitude times the magnitude integral. -/
theorem poweredL2_le_essentialMaximum_mul_poweredL1 {α : Type}
    (content : Measure.Content α) (value : α → Fraction.Rational) :
    content.poweredL2 value ≤
      content.essentialMaximumMagnitude value * content.poweredL1 value := by
  have bound := content.poweredLp_add_le_essentialMaximum 1 1 value
  rw [show 1 + 1 = 2 by decide, content.poweredLp_two,
    content.poweredLp_one, pow_one] at bound
  exact bound

/-- An essential separation ceiling bounds the higher powered distance by its extra power times the lower powered
distance. -/
theorem poweredLpDistance_add_le_of_essentialBound {α : Type}
    (content : Measure.Content α) (exponent extra : Nat)
    (left right : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling) :
    content.poweredLpDistance (exponent + extra) left right ≤
      ceiling ^ extra *
        content.poweredLpDistance exponent left right := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
          Distance.rationalSeparation (left item) (right item) ^
            (exponent + extra)) =
        content.integral (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ exponent *
            Distance.rationalSeparation (left item) (right item) ^ extra) := by
      exact content.integral_congr _ _ (fun item => by rw [pow_add])
    _ ≤ content.integral (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ exponent *
            ceiling ^ extra) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.pow_le_pow_direct
            (Distance.rationalSeparation_nonneg _ _) bound extra)
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (Distance.rationalSeparation_nonneg _ _) exponent)
    _ = ceiling ^ extra * content.integral (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ exponent) := by
      calc
        content.integral (fun item =>
            Distance.rationalSeparation (left item) (right item) ^ exponent *
              ceiling ^ extra) =
            content.integral (fun item => ceiling ^ extra *
              Distance.rationalSeparation (left item) (right item) ^ exponent) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling ^ extra * content.integral (fun item =>
              Distance.rationalSeparation (left item) (right item) ^ exponent) :=
          content.integral_scale _ _

/-- Squared integrated distance is bounded by essential maximum difference magnitude times integrated separation. -/
theorem poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    {α : Type} (content : Measure.Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL2Distance left right ≤
      content.essentialMaximumMagnitude
          (fun item => left item - right item) *
        content.l1Distance left right := by
  let difference := fun item => left item - right item
  let ceiling := content.essentialMaximumMagnitude difference
  have differenceBound :=
    content.essentiallyBoundedBy_essentialMaximumMagnitude difference
  have separationBound : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling := by
    intro atom member
    rcases differenceBound atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      dsimp only [difference] at bound
      rw [Distance.rationalSeparation_eq_sub_zero]
      exact bound
  have bound := content.poweredLpDistance_add_le_of_essentialBound
    1 1 left right ceiling separationBound
  rw [show 1 + 1 = 2 by decide, content.poweredLpDistance_two,
    content.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- An integrated-separation allowance and nonnegative essential ceiling give their product as a squared-distance
allowance. -/
theorem poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
    {α : Type} (content : Measure.Content α)
    (left right : α → Fraction.Rational) (ceiling epsilon : Fraction.Rational)
    (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        Distance.rationalSeparation (left atom.item) (right atom.item) ≤ ceiling)
    (l1Bound : content.l1Distance left right ≤ epsilon) :
    content.poweredL2Distance left right ≤ ceiling * epsilon := by
  have comparison := content.poweredLpDistance_add_le_of_essentialBound
    1 1 left right ceiling bounded
  rw [show 1 + 1 = 2 by decide, content.poweredLpDistance_two,
    content.poweredLpDistance_one, pow_one] at comparison
  exact comparison.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      l1Bound ceilingNonnegative)

end

end Content

end Purelib.Measure

end
