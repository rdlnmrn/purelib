module
import Purelib.Tactic.Ring

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.MinimalAxioms

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.Multiplication

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Algebra.Field
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Compute the total Gaussian reciprocal from the conjugated coordinates divided by
squared norm.

The operation is defined at every input, with zero sent to zero. A nonzero input has
nonzero quadrance, giving the usual multiplicative cancellation laws. -/
def inv (source : Canonical) : Canonical :=
  ⟨source.re / Canonical.normSq source, -source.im / Canonical.normSq source⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Use the displayed coordinate reciprocal as the total Gaussian inverse. -/
instance : Inv Canonical := ⟨inv⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Divide Gaussian values by multiplication with the total reciprocal of the
denominator. -/
instance : Div Canonical := ⟨fun left right => left * right⁻¹⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- A nonzero Gaussian multiplied by its reciprocal equals one. -/
theorem mul_inv_cancel (source : Canonical) (sourceNonzero : source ≠ 0) :
    source * source⁻¹ = 1 := by
  have normNonzero : Canonical.normSq source ≠ 0 := fun normZero =>
    sourceNonzero ((Canonical.normSq_eq_zero source).mp normZero)
  apply Canonical.ext
  · change source.re * (source.re / Canonical.normSq source) -
      source.im * (-source.im / Canonical.normSq source) = 1
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    calc
      source.re * (source.re * (Canonical.normSq source)⁻¹) -
            source.im * (-source.im * (Canonical.normSq source)⁻¹) =
          Canonical.normSq source * (Canonical.normSq source)⁻¹ := by
        simp only [Canonical.normSq, Arithmetic.sub_eq_add_neg_direct, _root_.add_mul,
          _root_.neg_mul, _root_.mul_neg, _root_.neg_neg]
        exact congrArg₂ (fun left right : Rational => left + right)
          (Fraction.mul_assoc source.re source.re
            (Canonical.normSq source)⁻¹).symm
          (Fraction.mul_assoc source.im source.im
            (Canonical.normSq source)⁻¹).symm
      _ = 1 := Fraction.mul_inv_cancel _ normNonzero
  · change source.re * (-source.im / Canonical.normSq source) +
      source.im * (source.re / Canonical.normSq source) = 0
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    simp only [_root_.neg_mul, _root_.mul_neg]
    have swapped :
        source.im * (source.re * (Canonical.normSq source)⁻¹) =
          source.re * (source.im * (Canonical.normSq source)⁻¹) := by
      calc
        source.im * (source.re * (Canonical.normSq source)⁻¹) =
            (source.im * source.re) * (Canonical.normSq source)⁻¹ :=
          (Fraction.mul_assoc source.im source.re
            (Canonical.normSq source)⁻¹).symm
        _ = (source.re * source.im) * (Canonical.normSq source)⁻¹ := by
          rw [Fraction.mul_comm source.im source.re]
        _ = source.re * (source.im * (Canonical.normSq source)⁻¹) :=
          Fraction.mul_assoc source.re source.im
            (Canonical.normSq source)⁻¹
    rw [swapped]
    exact Fraction.neg_add_cancel
      (source.re * (source.im * (Canonical.normSq source)⁻¹))

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The reciprocal of a nonzero Gaussian multiplied by the original value equals one. -/
theorem inv_mul_cancel (source : Canonical) (sourceNonzero : source ≠ 0) :
    source⁻¹ * source = 1 := by
  rw [Canonical.mul_comm]
  exact mul_inv_cancel source sourceNonzero

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The squared norm of a nonzero Gaussian reciprocal is the reciprocal of its squared
norm. -/
theorem normSq_inv (source : Canonical) (sourceNonzero : source ≠ 0) :
    Canonical.normSq source⁻¹ = (Canonical.normSq source)⁻¹ := by
  have normNonzero : Canonical.normSq source ≠ 0 := fun normZero =>
    sourceNonzero ((Canonical.normSq_eq_zero source).mp normZero)
  apply Fraction.mul_left_cancel_of_nonzero normNonzero
  calc
    Canonical.normSq source * Canonical.normSq source⁻¹ = Canonical.normSq (source * source⁻¹) :=
      (Canonical.normSq_mul source source⁻¹).symm
    _ = Canonical.normSq 1 := by rw [mul_inv_cancel source sourceNonzero]
    _ = 1 := Canonical.normSq_one
    _ = Canonical.normSq source * (Canonical.normSq source)⁻¹ :=
      (Fraction.mul_inv_cancel
        (Canonical.normSq source) normNonzero).symm

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The squared norm of division by a nonzero Gaussian equals numerator quadrance times
reciprocal denominator quadrance. -/
theorem normSq_div (left right : Canonical) (rightNonzero : right ≠ 0) :
    Canonical.normSq (left / right) = Canonical.normSq left * (Canonical.normSq right)⁻¹ := by
  change Canonical.normSq (left * right⁻¹) = _
  rw [Canonical.normSq_mul, normSq_inv right rightNonzero]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Cancel the same retained nonzero Gaussian factor from two right products. -/
theorem mul_right_cancel_of_nonzero {left right factor : Canonical}
    (factorNonzero : factor ≠ 0) (equalProducts : left * factor = right * factor) :
    left = right := by
  have multiplied := congrArg (fun value => value * factor⁻¹) equalProducts
  simpa only [Canonical.mul_assoc, mul_inv_cancel factor factorNonzero,
    _root_.mul_one] using multiplied

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The product of two retained nonzero Gaussian values is nonzero. -/
theorem mul_ne_zero {left right : Canonical}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 := by
  intro productZero
  apply leftNonzero
  apply mul_right_cancel_of_nonzero rightNonzero
  rw [productZero, zero_mul]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The reciprocal of a retained nonzero Gaussian value is nonzero. -/
theorem inv_ne_zero {source : Canonical} (sourceNonzero : source ≠ 0) :
    source⁻¹ ≠ 0 := by
  intro inverseZero
  have productOne := mul_inv_cancel source sourceNonzero
  rw [inverseZero, mul_zero] at productOne
  exact Canonical.zero_ne_one productOne

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Algebra.Ring

/-- Negating a canonical Gaussian pair negates its total reciprocal.

Zero uses the same total reciprocal display. For a nonzero pair, cancelling
its retained negative factor compares the two original inverse products. -/
theorem inv_neg (source : Canonical) : (-source)⁻¹ = -(source⁻¹) := by
  by_cases sourceZero : source = 0
  · rw [sourceZero]
    rfl
  · have negativeNonzero : -source ≠ 0 := by
      intro negativeZero
      have twice := congrArg (fun value : Canonical => -value) negativeZero
      rw [neg_neg, neg_zero] at twice
      exact sourceZero twice
    apply mul_right_cancel_of_nonzero negativeNonzero
    calc
      (-source)⁻¹ * (-source) = 1 := by
        rw [Canonical.mul_comm]
        exact mul_inv_cancel (-source) negativeNonzero
      _ = source⁻¹ * source := by
        rw [Canonical.mul_comm]
        exact (mul_inv_cancel source sourceZero).symm
      _ = (-(source⁻¹)) * (-source) := (Multiplication.neg_mul_neg source⁻¹ source).symm

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Equip canonical Gaussian arithmetic with explicit finite reciprocal and cancellation
laws.

The original coordinate inverse and division instances are retained together with
their explicit nonzeroness and sign proofs; no choice of inverse witness is required. -/
instance instExplicitField : ExplicitField Canonical where
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel := mul_inv_cancel
  mul_ne_zero := mul_ne_zero
  inv_ne_zero := inv_ne_zero
  inv_neg := inv_neg

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Reading a working Gaussian reciprocal preserves its exact reciprocal value. -/
@[simp] theorem value_inv_instance (source : Canonical) :
    Gaussian.Basic.value source⁻¹ = (Gaussian.Basic.value source)⁻¹ := rfl

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Reading a working Gaussian quotient preserves its exact quotient value. -/
@[simp] theorem value_div_instance (left right : Canonical) :
    Gaussian.Basic.value (left / right) = Gaussian.Basic.value left / Gaussian.Basic.value right := rfl

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.CCL.Arithmetic.OperationalEquivalence

end Purelib.CCL.Arithmetic.OperationalEquivalence
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Interchange the middle factors of a Gaussian product of two pairs. -/
public theorem gaussian_mul_pair_swap (a b c d : Canonical) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) :=
      _root_.mul_assoc _ _ _
    _ = a * ((b * c) * d) := by
      rw [_root_.mul_assoc b c d]
    _ = a * ((c * b) * d) := by
      rw [_root_.mul_comm b c]
    _ = a * (c * (b * d)) := by
      rw [_root_.mul_assoc c b d]
    _ = (a * c) * (b * d) :=
      (_root_.mul_assoc _ _ _).symm

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.CCL.Progressive.Sampling

end Purelib.CCL.Progressive.Sampling
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Split a Gaussian difference through a retained intermediate value. -/
public theorem later_sub_earlier (later center earlier : Canonical) :
    later - earlier = (later - center) + (center - earlier) := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- Compute the total Gaussian reciprocal from the conjugated coordinates divided by
squared norm.

The operation is defined at every input, with zero sent to zero. A nonzero input has
nonzero quadrance, giving the usual multiplicative cancellation laws. -/
def inv (source : Canonical) : Canonical :=
  ⟨source.re / Norm.Basic.normSq source, -source.im / Norm.Basic.normSq source⟩

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The installed Gaussian inverse equals the coordinate formula using power-based
squared norm. -/
@[simp] theorem inv_eq (source : Canonical) : source⁻¹ = inv source := by
  change Canonical.inv source = inv source
  apply Gaussian.Basic.ext
  · change source.re / Canonical.normSq source =
      source.re / Norm.Basic.normSq source
    rw [Norm.Basic.normSq_eq_canonical]
  · change -source.im / Canonical.normSq source =
      -source.im / Norm.Basic.normSq source
    rw [Norm.Basic.normSq_eq_canonical]

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The total Gaussian reciprocal sends zero to zero. -/
@[simp] theorem inv_zero : inv 0 = 0 := by
  decide

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The total Gaussian reciprocal sends one to one. -/
@[simp] theorem inv_one_direct : inv 1 = 1 := by decide

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- A retained nonzero Gaussian times its displayed coordinate reciprocal equals one. -/
theorem mul_inv (source : Canonical) (nonzero : source ≠ 0) :
    source * inv source = 1 := by
  rw [← inv_eq]
  exact Canonical.mul_inv_cancel source nonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The displayed coordinate reciprocal of a retained nonzero Gaussian times that value
equals one. -/
theorem inv_mul (source : Canonical) (nonzero : source ≠ 0) :
    inv source * source = 1 := by
  rw [_root_.mul_comm]
  exact mul_inv source nonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- Cancel the same retained nonzero Gaussian factor from two right products. -/
theorem mul_right_cancel_of_ne {left right factor : Canonical}
    (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right :=
  Canonical.mul_right_cancel_of_nonzero
    factorNonzero productsEqual

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The product of two retained nonzero Gaussian values is nonzero. -/
theorem mul_ne_zero_direct {left right : Canonical}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    left * right ≠ 0 :=
  Canonical.mul_ne_zero leftNonzero rightNonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The reciprocal of a retained nonzero Gaussian value is nonzero. -/
theorem inv_ne_zero_direct {source : Canonical} (nonzero : source ≠ 0) :
    source⁻¹ ≠ 0 :=
  Canonical.inv_ne_zero nonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- Negation preserves a nonzero canonical Gaussian pair. -/
theorem neg_ne_zero_direct {source : Canonical} (nonzero : source ≠ 0) :
    -source ≠ 0 := by
  intro negativeZero
  have twice := congrArg (fun value : Basic.Canonical => -value) negativeZero
  rw [neg_neg, neg_zero] at twice
  exact nonzero twice

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- Total Gaussian reciprocal commutes with negation. -/
theorem inv_neg_direct (source : Canonical) : inv (-source) = -inv
  source :=
  by rw [← inv_eq, ← inv_eq]
     exact Canonical.inv_neg source

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The squared norm of a nonzero Gaussian reciprocal is the reciprocal of its squared
norm. -/
theorem normSq_inv (source : Canonical) (nonzero : source ≠ 0) :
    Norm.Basic.normSq (inv source) = (Norm.Basic.normSq source)⁻¹ := by
  rw [← inv_eq]
  simpa only [Norm.Basic.normSq_eq_canonical] using
    Canonical.normSq_inv source nonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field
section Field

/-- The squared norm of division by a nonzero Gaussian equals numerator quadrance times
reciprocal denominator quadrance. -/
theorem normSq_div (left right : Canonical) (rightNonzero : right ≠ 0) :
    Norm.Basic.normSq (left / right) = Norm.Basic.normSq left * (Norm.Basic.normSq right)⁻¹ :=
  by simpa only [Norm.Basic.normSq_eq_canonical] using
    Canonical.normSq_div left right rightNonzero

end Field
end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Approximation.QuotientVariation

end Purelib.Approximation.QuotientVariation
end

section
@[expose] public section
namespace Purelib.CCL.Arithmetic.Enclosures
section Ball

end Ball
end Purelib.CCL.Arithmetic.Enclosures
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- The difference of reciprocals of two nonzero Gaussians equals reciprocal-left times
reversed difference times reciprocal-right. -/
theorem inverse_sub_inverse_direct {left right : Canonical}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    inv left - inv right =
      inv left * (right - left) * inv right := by
  have productNonzero : left * right ≠ 0 :=
    mul_ne_zero_direct leftNonzero rightNonzero
  apply mul_right_cancel_of_ne productNonzero
  have leftCancel := inv_mul left leftNonzero
  have rightCancel := inv_mul right rightNonzero
  calc
    (inv left - inv right) * (left * right) = right - left := by
      calc
        (inv left - inv right) * (left * right) =
            (inv left * left) * right -
              (inv right * right) * left := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
              ring1
        _ = right - left := by
          rw [leftCancel, rightCancel]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
              Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;>
            ring1
    _ = (inv left * (right - left) * inv right) * (left * right) := by
      calc
        right - left =
            (right - left) *
              ((inv left * left) * (inv right * right)) := by
          rw [leftCancel, rightCancel,
            _root_.one_mul,
            _root_.mul_one]
        _ = (inv left * (right - left) * inv right) *
              (left * right) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
              ring1

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.CCL.Progressive.Coherence
section Coherent

end Coherent
end Purelib.CCL.Progressive.Coherence
end

section
@[expose] public section
namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
section Coherent

/-- Multiplication by the retained nonzero Gaussian denominator cancels exact division. -/
private theorem gaussian_div_mul_cancel
  (numerator denominator : Canonical)
    (denominatorNonzero : denominator ≠ 0) :
    numerator / denominator * denominator = numerator := by
  rw [ExplicitField.div_eq_mul_inv]
  calc
    numerator * denominator⁻¹ * denominator =
        numerator * (denominator⁻¹ * denominator) :=
      _root_.mul_assoc _ _ _
    _ = numerator * 1 := by
      rw [Field.inv_eq,
        Field.inv_mul
          denominator denominatorNonzero]
    _ = numerator := _root_.mul_one numerator

end Coherent
end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
end

section
@[expose] public section
namespace Purelib.CCL.Progressive.Coherence
section Coherent

end Coherent
end Purelib.CCL.Progressive.Coherence
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field.GaussianNormalized

/-- Compute the total Gaussian reciprocal from the conjugated coordinates divided by
squared norm.

The operation is defined at every input, with zero sent to zero. A nonzero input has
nonzero quadrance, giving the usual multiplicative cancellation laws. -/
def inv (source : Number) : Number :=
  source⁻¹

end Purelib.Data.Gaussian.Field.GaussianNormalized
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Divide two working Gaussian values using the total reciprocal convention. -/
def div (left right : Number) : Number :=
  left / right

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Reading a working Gaussian reciprocal preserves its exact reciprocal value. -/
theorem value_inv (source : Number) :
    Gaussian.Basic.value (GaussianNormalized.inv source) = (Gaussian.Basic.value source)⁻¹ := rfl

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Reading a working Gaussian quotient preserves its exact quotient value. -/
theorem value_div (left right : Number) :
    Gaussian.Basic.value (div left right) = Gaussian.Basic.value left / Gaussian.Basic.value right := rfl

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Compute total Gaussian reciprocal through the identical working-pair representation. -/
def normalizedInv (source : Canonical) : Canonical :=
  Gaussian.Basic.value (GaussianNormalized.inv (Gaussian.Basic.ofGaussian source))

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Compute total Gaussian division through the identical working-pair representation. -/
def normalizedDiv (left right : Canonical) : Canonical :=
  Gaussian.Basic.value (div (Gaussian.Basic.ofGaussian left) (Gaussian.Basic.ofGaussian right))

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Working-pair reciprocal agrees with the original Gaussian inverse. -/
@[simp] theorem normalizedInv_eq (source : Canonical) :
    normalizedInv source = source⁻¹ := by
  rw [normalizedInv, value_inv, Gaussian.Basic.value_ofGaussian]

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Working-pair division agrees with the original Gaussian quotient. -/
@[simp] theorem normalizedDiv_eq (left right : Canonical) :
    normalizedDiv left right = left / right := by
  rw [normalizedDiv, value_div, Gaussian.Basic.value_ofGaussian, Gaussian.Basic.value_ofGaussian]

end Purelib.Data.Gaussian.Field
end

section
@[expose] public section
namespace Purelib.Riemann.Integration.QuotientVariation

end Purelib.Riemann.Integration.QuotientVariation
end

section
@[expose] public section
namespace Purelib.Data.Gaussian.Field

/-- Cancel the same retained nonzero Gaussian factor from two left products. -/
public theorem eq_of_mul_eq_mul_left
    {left right factor : Canonical} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply mul_right_cancel_of_ne
    factorNonzero
  calc
    left * factor = factor * left :=
      _root_.mul_comm left factor
    _ = factor * right := productsEqual
    _ = right * factor :=
      _root_.mul_comm factor right

end Purelib.Data.Gaussian.Field
end

namespace Purelib.Data.Gaussian.Field

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic
open Purelib.Algebra
open Purelib.Algebra.Field

/-- Reversing a Gaussian difference negates it. -/
public theorem sub_eq_neg_sub (center value : Canonical) :
    center - value = -(value - center) := by
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;> ring1

/-- Subtract two Gaussian fractions by the exact cross-product formula.

Both original denominators must be nonzero; their product is then nonzero and the
displayed combined fraction retains the original numerator order. -/
public theorem div_sub_div (leftNumerator rightNumerator
  leftDenominator
    rightDenominator : Canonical)
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0) :
    leftNumerator / leftDenominator -
        rightNumerator / rightDenominator =
      (leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
        (leftDenominator * rightDenominator) := by
  have productNonzero := mul_ne_zero_direct leftNonzero rightNonzero
  apply mul_right_cancel_of_ne productNonzero
  calc
    (leftNumerator / leftDenominator -
          rightNumerator / rightDenominator) *
        (leftDenominator * rightDenominator) =
      (leftNumerator / leftDenominator * leftDenominator) *
          rightDenominator -
        (rightNumerator / rightDenominator * rightDenominator) *
          leftDenominator := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    _ = leftNumerator * rightDenominator -
          rightNumerator * leftDenominator := by
      rw [ExplicitField.div_mul_cancel leftNumerator leftNonzero,
        ExplicitField.div_mul_cancel rightNumerator rightNonzero]
    _ = ((leftNumerator * rightDenominator -
          rightNumerator * leftDenominator) /
            (leftDenominator * rightDenominator)) *
          (leftDenominator * rightDenominator) :=
      (ExplicitField.div_mul_cancel _ productNonzero).symm

end Purelib.Data.Gaussian.Field
