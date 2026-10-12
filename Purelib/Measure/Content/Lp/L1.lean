module
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Stability
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Event.RationalDistance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic

section
section
public section

/-!
# Finite rational L1 error

The exact integral of pointwise rational separation gives a finite analogue
of L1 distance.  It supports the metric-style inequalities and controls
expectation error by direct finite summation.  Indicator distance is exactly
the probability or content of an executable symmetric difference.

No function-space completion, equivalence class, convergence mode, or limit
is constructed.
-/

namespace Purelib.Measure
namespace Content

open Purelib.Data.Rat
/-- Integrate pointwise rational separation over the exact content atoms.

Nonnegative retained weights count each original occurrence. Zero-weight occurrences contribute nothing, so distinct
functions may have zero distance. -/
@[expose] def l1Distance {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item => Distance.rationalSeparation (left item) (right item)

/-- The integrated rational separation is nonnegative. -/
theorem l1Distance_nonneg {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    0 ≤ content.l1Distance left right := by
  apply content.integral_nonneg
  intro atom member
  exact Distance.rationalSeparation_nonneg _ _

/-- The integrated separation of an observable from itself is zero. -/
theorem l1Distance_refl {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.l1Distance value value = 0 := by
  calc
    content.l1Distance value value =
        content.integral (fun _ => 0) := by
      exact content.integral_congr _ _ (fun item => by
        rw [Distance.rationalSeparation, sub_self, Fraction.Order.Basic.max_self])
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- Exchanging the two observables preserves their integrated separation. -/
theorem l1Distance_symm {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.l1Distance left right = content.l1Distance right left := by
  exact content.integral_congr _ _ (fun item =>
    Distance.rationalSeparation_symm _ _)

/-- Integrated separation obeys the triangle inequality through the same middle observable. -/
theorem l1Distance_triangle {α : Type} (content : Content α)
    (left middle right : α → Fraction.Rational) :
    content.l1Distance left right ≤
      content.l1Distance left middle + content.l1Distance middle right := by
  calc
    content.l1Distance left right ≤
        content.integral (fun item =>
          Distance.rationalSeparation (left item) (middle item) +
            Distance.rationalSeparation (middle item) (right item)) := by
      apply content.integral_mono
      intro atom member
      exact Distance.rationalSeparation_triangle _ _ _
    _ = content.l1Distance left middle +
        content.l1Distance middle right := by
      exact content.integral_add _ _

/-- The separation of two integrated distances to a common anchor is bounded by the distance between their first
observables. -/
theorem l1Distance_reverse_triangle {α : Type}
    (content : Content α)
    (first second anchor : α → Fraction.Rational) :
    Distance.rationalSeparation (content.l1Distance first anchor)
        (content.l1Distance second anchor) ≤
      content.l1Distance first second := by
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · have translated := Fraction.Order.Arithmetic.sub_le_sub_right_direct
      (content.l1Distance_triangle first second anchor)
      (content.l1Distance second anchor)
    have cancel : content.l1Distance first second + content.l1Distance second anchor -
        content.l1Distance second anchor = content.l1Distance first second := by ring1
    rw [cancel] at translated
    exact translated
  · have triangle : content.l1Distance second anchor ≤
        content.l1Distance first second + content.l1Distance first anchor := by
      calc
        content.l1Distance second anchor ≤
            content.l1Distance second first +
              content.l1Distance first anchor :=
          content.l1Distance_triangle second first anchor
        _ = content.l1Distance first second +
              content.l1Distance first anchor := by
          rw [content.l1Distance_symm second first]
    have translated := Fraction.Order.Arithmetic.sub_le_sub_right_direct triangle
      (content.l1Distance first anchor)
    have cancel : content.l1Distance first second + content.l1Distance first anchor -
        content.l1Distance first anchor = content.l1Distance first second := by ring1
    rw [cancel] at translated
    exact translated

/-- Integrated pointwise separation bounds both signed differences of the two integrals. -/
theorem integral_close_l1 {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.integral right - content.integral left ≤
        content.l1Distance left right ∧
      content.integral left - content.integral right ≤
        content.l1Distance left right := by
  apply content.integral_symmetricError
  intro atom member
  exact ⟨Fraction.Order.Basic.le_max_right _ _, Fraction.Order.Basic.le_max_left _ _⟩

/-- The separation of two integrals is bounded by the integral of pointwise separation. -/
theorem integral_separation_le_l1Distance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (content.integral left) (content.integral right) ≤
      content.l1Distance left right := by
  have close := content.integral_close_l1 left right
  unfold Distance.rationalSeparation
  exact Fraction.Order.Basic.max_le close.2 close.1

end Content

namespace Distribution
end Distribution
namespace Content

open Purelib.Data.Rat in
/-- The integrated distance of two event indicators equals the measurement of their symmetric difference. -/
theorem l1Distance_indicator {α : Type} (content : Content α)
    (first second : α → Bool) :
    content.l1Distance (Distribution.indicator first)
        (Distribution.indicator second) =
      content.measure (symmetricDifferenceEvent first second) := by
  unfold l1Distance
  calc
    content.integral (fun item =>
          Distance.rationalSeparation
            (Distribution.indicator first item)
            (Distribution.indicator second item)) =
        content.integral
          (Distribution.indicator (symmetricDifferenceEvent first second)) := by
      exact content.integral_congr _ _ (fun item =>
        indicator_rationalSeparation first second item)
    _ = content.measure (symmetricDifferenceEvent first second) :=
      content.integral_indicator _

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end

end

section
public section

/-!
# Root-free finite Lp bounds

Square roots of rational second moments need not be rational.  The primitive
L2 quantity here is therefore the exact powered norm `integral (f^2)`.  Its
Cauchy--Schwarz inequality is stated after squaring, and so remains wholly
rational and executable.
-/

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Integrate the rational magnitude of an observable over the exact content atoms. -/
@[expose] def poweredL1 {α : Type} (content : Content α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  content.integral fun item => Distance.rationalSeparation (value item) 0

/-- Pointwise equal observables have the same integral of magnitude. -/
theorem poweredL1_congr {α : Type} (content : Content α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    content.poweredL1 left = content.poweredL1 right := by
  unfold poweredL1
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun value => Distance.rationalSeparation value 0) (pointwise item))

/-- The integral of an observable's magnitude is nonnegative. -/
theorem poweredL1_nonnegative {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    0 ≤ content.poweredL1 value := by
  apply content.integral_nonneg
  intro atom member
  exact Distance.rationalSeparation_nonneg _ _

/-- The zero observable has zero integral of magnitude. -/
theorem poweredL1_zero {α : Type} (content : Content α) :
    content.poweredL1 (fun _ => 0) = 0 := by
  unfold poweredL1
  calc
    content.integral (fun _ : α => Distance.rationalSeparation 0 0) =
        content.integral (fun _ => (0 : Fraction.Rational)) :=
      content.integral_congr _ _ (fun item => rfl)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

/-- The integral of a constant magnitude equals content total mass times that magnitude. -/
theorem poweredL1_constant {α : Type} (content : Content α)
    (constant : Fraction.Rational) :
    content.poweredL1 (fun _ => constant) =
      content.total * Distance.rationalSeparation constant 0 := by
  unfold poweredL1
  exact content.integral_constant _

/-- Scaling an observable scales its integral of magnitude by the rational magnitude of the factor. -/
theorem poweredL1_scale {α : Type} (content : Content α)
    (factor : Fraction.Rational) (value : α → Fraction.Rational) :
    content.poweredL1 (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 * content.poweredL1 value := by
  unfold poweredL1
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (factor * value item) 0) =
        content.integral (fun item => Distance.rationalSeparation factor 0 *
          Distance.rationalSeparation (value item) 0) :=
      content.integral_congr _ _ (fun item =>
        Distance.rationalSeparation_mul_zero factor (value item))
    _ = Distance.rationalSeparation factor 0 * content.integral (fun item =>
          Distance.rationalSeparation (value item) 0) :=
      content.integral_scale _ _

/-- Negating an observable preserves its integral of magnitude. -/
theorem poweredL1_neg {α : Type} (content : Content α)
    (value : α → Fraction.Rational) :
    content.poweredL1 (fun item => -value item) =
      content.poweredL1 value := by
  have scaled := content.poweredL1_scale (-1) value
  calc
    content.poweredL1 (fun item => -value item) =
        content.poweredL1 (fun item => (-1) * value item) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ = Distance.rationalSeparation (-1) 0 * content.poweredL1 value := scaled
    _ = content.poweredL1 value := by
      rw [show Distance.rationalSeparation (-1) 0 = 1 by decide, one_mul]

/-- The integral of the magnitude of a sum is bounded by the sum of the two magnitude integrals. -/
theorem poweredL1_add_le {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL1 (fun item => left item + right item) ≤
      content.poweredL1 left + content.poweredL1 right := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          Distance.rationalSeparation (left item + right item) 0) ≤
        content.integral (fun item =>
          Distance.rationalSeparation (left item) 0 +
            Distance.rationalSeparation (right item) 0) := by
      apply content.integral_mono
      intro atom member
      exact Distance.rationalSeparation_add_zero_le
        (left atom.item) (right atom.item)
    _ = content.integral (fun item => Distance.rationalSeparation (left item) 0) +
          content.integral (fun item => Distance.rationalSeparation (right item) 0) :=
      content.integral_add _ _

/-- The integral of the magnitude of a difference is bounded by the sum of the two magnitude integrals. -/
theorem poweredL1_sub_le {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL1 (fun item => left item - right item) ≤
      content.poweredL1 left + content.poweredL1 right := by
  have bound := content.poweredL1_add_le left (fun item => -right item)
  rw [content.poweredL1_neg] at bound
  calc
    content.poweredL1 (fun item => left item - right item) =
        content.poweredL1 (fun item => left item + -right item) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ ≤ content.poweredL1 left + content.poweredL1 right := bound

/-- The integral of an observable's magnitude is its integrated distance from zero. -/
theorem poweredL1_eq_l1Distance_zero {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.poweredL1 value = content.l1Distance value (fun _ => 0) := rfl

/-- The separation of two magnitude integrals is bounded by their integrated pointwise distance. -/
theorem poweredL1_separation_le_l1Distance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (content.poweredL1 left) (content.poweredL1 right) ≤
      content.l1Distance left right := by
  rw [content.poweredL1_eq_l1Distance_zero,
    content.poweredL1_eq_l1Distance_zero]
  exact content.l1Distance_reverse_triangle left right (fun _ => 0)

/-- The magnitude integral of a pointwise difference is the integrated distance of the original observables. -/
theorem poweredL1_sub_eq_l1Distance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.poweredL1 (fun item => left item - right item) =
      content.l1Distance left right := by
  unfold poweredL1 l1Distance
  exact content.integral_congr _ _ (fun item =>
    (Distance.rationalSeparation_eq_sub_zero (left item) (right item)).symm)

/-- A nonnegative uniform magnitude ceiling for the right factor bounds the product's magnitude integral by that ceiling
times the left magnitude integral. -/
theorem poweredL1_mul_le_of_right_bounded {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (ceiling : Fraction.Rational) (_ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ content.atoms →
      Distance.rationalSeparation (right atom.item) 0 ≤ ceiling) :
    content.poweredL1 (fun item => left item * right item) ≤
      ceiling * content.poweredL1 left := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          Distance.rationalSeparation (left item * right item) 0) =
        content.integral (fun item =>
          Distance.rationalSeparation (left item) 0 *
            Distance.rationalSeparation (right item) 0) := by
      exact content.integral_congr _ _ (fun item =>
        Distance.rationalSeparation_mul_zero (left item) (right item))
    _ ≤ content.integral (fun item =>
          Distance.rationalSeparation (left item) 0 * ceiling) := by
      apply content.integral_mono
      intro atom member
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (bounded atom member) (Distance.rationalSeparation_nonneg _ _)
    _ = ceiling * content.integral (fun item =>
          Distance.rationalSeparation (left item) 0) := by
      calc
        content.integral (fun item =>
            Distance.rationalSeparation (left item) 0 * ceiling) =
            content.integral (fun item =>
              ceiling * Distance.rationalSeparation (left item) 0) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling * content.integral (fun item =>
              Distance.rationalSeparation (left item) 0) :=
          content.integral_scale _ _

end

end Content

end Purelib.Measure

end
