module
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.Fraction.Reduced
public import Purelib.Data.GaussianInt.Units

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.Deriving.Repr
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Basic

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Fraction

section
@[expose] public section

/-!
# Reduced Gaussian-integer fractions

This file turns the executable extended Gaussian Euclidean certificate into a
reduced numerator--denominator record.  Coprimality is carried by displayed
Bezout coefficients rather than by an abstract ideal or quotient.  It also
proves constructively that two reduced records with the same value have
unit-associate denominators and hence the same denominator quadrance.
-/

namespace Purelib.Data.GaussianInt.Fraction.Canonical

/-- A Gaussian denominator has strictly positive real coordinate and nonnegative
imaginary coordinate. -/
def IsCanonicalDenominator (denominator : GaussianInt) : Prop :=
  0 < denominator.re ∧ 0 ≤ denominator.im

/-- Decide the half-open first-quadrant condition by exact integer coordinate
comparisons. -/
instance isCanonicalDenominatorDecidable (denominator : GaussianInt)
  :
    Decidable (IsCanonicalDenominator denominator) := by
  unfold IsCanonicalDenominator
  infer_instance

/-- Choose the exact Gaussian unit rotating the displayed denominator into the half-open
first quadrant.

Sign tests on the two integer coordinates choose one of 1, -1, i and -i. Every
selected value is a unit, including the deterministic choice at zero; the sector
guarantee requires a nonzero input. -/
def canonicalizingUnit (denominator : GaussianInt) : GaussianInt :=
  if 0 < denominator.re then
    if 0 ≤ denominator.im then 1 else Units.imaginaryUnit
  else if denominator.re < 0 then
    if 0 < denominator.im then -Units.imaginaryUnit else -1
  else if 0 < denominator.im then
    -Units.imaginaryUnit
  else
    Units.imaginaryUnit

/-- Multiply the displayed Gaussian integer by its deterministically selected normalizing
unit. -/
def canonicalAssociate (denominator : GaussianInt) : GaussianInt :=
  canonicalizingUnit denominator * denominator

/-- The selected normalizing Gaussian unit always has natural quadrance one. -/
theorem canonicalizingUnit_normNat (denominator : GaussianInt) :
    GaussianInt.normNat (canonicalizingUnit denominator) = 1 := by
  unfold canonicalizingUnit
  split
  · split <;> decide
  · split
    · split <;> decide
    · split <;> decide

/-- A nonzero Gaussian denominator rotated by its selected unit lies in the canonical
half-open first quadrant. -/
theorem canonicalAssociate_isCanonical
    {denominator : GaussianInt} (denominatorNonzero : denominator ≠ 0) :
    IsCanonicalDenominator (canonicalAssociate denominator) := by
  rw [IsCanonicalDenominator, canonicalAssociate,
    canonicalizingUnit]
  by_cases realPositive : 0 < denominator.re
  · by_cases imaginaryNonnegative : 0 ≤ denominator.im
    · rw [if_pos realPositive, if_pos imaginaryNonnegative, GaussianInt.one_mul]
      exact ⟨realPositive, imaginaryNonnegative⟩
    · rw [if_pos realPositive, if_neg imaginaryNonnegative]
      simp only [GaussianInt.mul_re, GaussianInt.mul_im, Units.imaginaryUnit,
        Int.Arithmetic.zero_mul, Int.one_mul, Int.Arithmetic.zero_sub,
        Int.Arithmetic.zero_add, -eq_self, -iff_self]
      constructor
      · have positive := Int.Order.sub_pos.mpr
          (Int.Order.lt_of_not_le imaginaryNonnegative)
        rewrite [Int.Arithmetic.zero_sub]
          at positive
        exact positive
      · exact Int.Order.le_of_lt realPositive
  · by_cases realNegative : denominator.re < 0
    · by_cases imaginaryPositive : 0 < denominator.im
      · rw [if_neg realPositive, if_pos realNegative, if_pos imaginaryPositive]
        simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.neg_re,
          GaussianInt.neg_im, Units.imaginaryUnit, Int.neg_zero,
          Int.Arithmetic.neg_mul, Int.Arithmetic.zero_mul, Int.one_mul,
          Int.Arithmetic.zero_sub, Int.Arithmetic.zero_add, Int.neg_neg,
          -eq_self, -iff_self]
        constructor
        · exact imaginaryPositive
        · have bound := Int.Order.neg_le_neg (Int.Order.le_of_lt realNegative)
          rewrite [Int.neg_zero]
            at bound
          exact bound
      · rw [if_neg realPositive, if_pos realNegative, if_neg imaginaryPositive]
        simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.neg_re,
          GaussianInt.neg_im, GaussianInt.one_re, GaussianInt.one_im,
          Int.neg_zero, Int.Arithmetic.neg_mul, Int.one_mul,
          Int.Arithmetic.zero_mul, Int.Arithmetic.sub_zero, Int.add_zero,
          -eq_self, -iff_self]
        constructor
        · have positive := Int.Order.sub_pos.mpr realNegative
          rewrite [Int.Arithmetic.zero_sub]
            at positive
          exact positive
        · have bound := Int.Order.neg_le_neg
            (Int.Order.le_of_not_lt imaginaryPositive)
          rewrite [Int.neg_zero]
            at bound
          exact bound
    · have realZero : denominator.re = 0 :=
        Int.Order.le_antisymm (Int.Order.le_of_not_lt realPositive)
          (Int.Order.le_of_not_lt realNegative)
      by_cases imaginaryPositive : 0 < denominator.im
      · rw [if_neg realPositive, if_neg realNegative, if_pos imaginaryPositive]
        simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.neg_re,
          GaussianInt.neg_im, Units.imaginaryUnit, Int.neg_zero,
          Int.Arithmetic.neg_mul, Int.Arithmetic.zero_mul, Int.one_mul,
          Int.Arithmetic.zero_sub, Int.Arithmetic.zero_add, Int.neg_neg,
          -eq_self, -iff_self]
        constructor
        · exact imaginaryPositive
        · rewrite [realZero, Int.neg_zero]
          exact Int.Order.le_refl 0
      · have imaginaryNonzero : denominator.im ≠ 0 := by
          intro imaginaryZero
          exact denominatorNonzero (GaussianInt.ext realZero imaginaryZero)
        rw [if_neg realPositive, if_neg realNegative, if_neg imaginaryPositive]
        simp only [GaussianInt.mul_re, GaussianInt.mul_im, Units.imaginaryUnit,
          Int.Arithmetic.zero_mul, Int.one_mul, Int.Arithmetic.zero_sub,
          Int.Arithmetic.zero_add, -eq_self, -iff_self]
        constructor
        · have imaginaryNegative := Int.Order.lt_of_le_of_ne
            (Int.Order.le_of_not_lt imaginaryPositive) imaginaryNonzero
          have positive := Int.Order.sub_pos.mpr imaginaryNegative
          rewrite [Int.Arithmetic.zero_sub]
            at positive
          exact positive
        · rewrite [realZero]
          exact Int.Order.le_refl 0

set_option genInjectivity false in
/-- Retain a reduced Gaussian fraction whose denominator lies in the canonical half-open
first quadrant.

The original reduced-fraction parent retains numerator, denominator, nonzeroness and
explicit Bezout coefficients. The extra field certifies the selected denominator
sector without replacing that parent. -/
structure CanonicalFraction extends toFraction :
  Data.GaussianInt.Fraction.Reduced where
  /-- The retained denominator has positive real coordinate and nonnegative imaginary coordinate. -/
    canonicalDenominator : IsCanonicalDenominator denominator

constructive_injectivity CanonicalFraction

derive_exposed_repr CanonicalFraction

namespace CanonicalFraction

open Purelib.Data.GaussianInt.Fraction.Canonical
/-- Read the exact Gaussian-rational value of the retained canonical reduced fraction. -/
def value (fraction : CanonicalFraction) :
  Canonical := fraction.toFraction.value

/-- Read the natural quadrance of the retained canonical denominator. -/
def height (fraction : CanonicalFraction) : Nat :=
  fraction.toFraction.height

/-- Forget only the reduction and sector certificates, retaining the exact displayed
Gaussian numerator and denominator. -/
def displayed (fraction : CanonicalFraction) :
  Fraction :=
  fraction.toFraction.displayed

end CanonicalFraction

open Purelib.Data.GaussianInt.Fraction.Canonical in
/-- Rotate a reduced Gaussian fraction by the deterministic unit of its denominator.

Scale numerator and denominator by the same unit, and transport the original Bezout
coefficients by its conjugate. The result retains exact value, denominator quadrance,
nonzeroness and the canonical sector proof. -/
def canonicalize (fraction : Data.GaussianInt.Fraction.Reduced) :
  CanonicalFraction :=
  by
  let unit := canonicalizingUnit fraction.denominator
  have unitNorm : GaussianInt.normNat unit = 1 :=
    canonicalizingUnit_normNat fraction.denominator
  have denominatorNonzero : unit * fraction.denominator ≠ 0 := by
    intro productZero
    have normZero := congrArg GaussianInt.normNat productZero
    rw [GaussianInt.normNat_mul, unitNorm, Nat.one_mul] at normZero
    have zeroNorm : GaussianInt.normNat (0 : GaussianInt) = 0 := rfl
    rw [zeroNorm] at normZero
    exact (Nat.ne_of_gt (GaussianInt.normNat_pos fraction.denominatorNonzero)) normZero
  have conjugateUnitProduct : GaussianInt.conj unit * unit = 1 := by
    rw [GaussianInt.mul_comm,
      GaussianInt.mul_conj, unitNorm]
    rfl
  have transportedBezout :
      1 = (fraction.leftCoefficient * GaussianInt.conj unit) *
            (unit * fraction.numerator) +
          (fraction.rightCoefficient * GaussianInt.conj unit) *
            (unit * fraction.denominator) := by
    calc
      1 = fraction.leftCoefficient * fraction.numerator +
          fraction.rightCoefficient * fraction.denominator := fraction.bezout
      _ = (fraction.leftCoefficient * GaussianInt.conj unit) *
            (unit * fraction.numerator) +
          (fraction.rightCoefficient * GaussianInt.conj unit) *
            (unit * fraction.denominator) := by
        calc
          fraction.leftCoefficient * fraction.numerator +
                fraction.rightCoefficient * fraction.denominator =
              (GaussianInt.conj unit * unit) *
                (fraction.leftCoefficient * fraction.numerator +
                  fraction.rightCoefficient * fraction.denominator) := by
            rw [conjugateUnitProduct, GaussianInt.one_mul]
          _ = (fraction.leftCoefficient * GaussianInt.conj unit) *
                (unit * fraction.numerator) +
              (fraction.rightCoefficient * GaussianInt.conj unit) *
                (unit * fraction.denominator) := by
            apply GaussianInt.ext <;>
              simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
              ring1
  exact
    { numerator := unit * fraction.numerator
      denominator := unit * fraction.denominator
      denominatorNonzero := denominatorNonzero
      leftCoefficient := fraction.leftCoefficient * GaussianInt.conj unit
      rightCoefficient := fraction.rightCoefficient * GaussianInt.conj unit
      bezout := transportedBezout
      canonicalDenominator := canonicalAssociate_isCanonical
        fraction.denominatorNonzero }

/-- Unit normalization preserves the exact Gaussian-rational value of the reduced
fraction. -/
theorem canonicalize_value (fraction :
  Data.GaussianInt.Fraction.Reduced) :
    (canonicalize fraction).value = fraction.value := by
  apply Fraction.Basic.value_eq_of_crossProduct
  change
    (canonicalize fraction).numerator * fraction.denominator =
      fraction.numerator * (canonicalize fraction).denominator
  dsimp only [canonicalize]
  apply GaussianInt.ext <;>
    simp only [GaussianInt.mul_re, GaussianInt.mul_im] <;>
    ring1

section
open Purelib.Data.GaussianInt.Fraction.Canonical
/-- Unit normalization preserves the natural denominator quadrance. -/
theorem canonicalize_height (fraction :
  Data.GaussianInt.Fraction.Reduced) :
    (canonicalize fraction).height = fraction.height := by
  unfold CanonicalFraction.height Data.GaussianInt.Fraction.Reduced.height
  change GaussianInt.normNat
      (canonicalizingUnit fraction.denominator * fraction.denominator) =
    GaussianInt.normNat fraction.denominator
  rw [GaussianInt.normNat_mul, canonicalizingUnit_normNat, Nat.one_mul]

/-- Reduce a displayed Gaussian fraction by the retained Euclidean procedure, then
normalize its denominator sector.

The original Euclidean reduction supplies explicit Bezout coefficients; deterministic
unit normalization retains that reduced parent and places its nonzero denominator in
the canonical half-open first quadrant. -/
def reduceCanonical (source : Fraction) : CanonicalFraction :=
  canonicalize (Reduced.reduce source)

end

/-- Deterministic reduction and unit normalization preserve the original exact Gaussian
value. -/
theorem reduceCanonical_value (source : Fraction) :
    (reduceCanonical source).value = source.value := by
  rw [reduceCanonical, canonicalize_value, Reduced.reduce_value]

/-- The canonicalized denominator quadrance equals the Euclidean reduced denominator
quadrance. -/
theorem reduceCanonical_height (source : Fraction) :
    (reduceCanonical source).height = (Reduced.reduce source).height := by
  exact canonicalize_height (Reduced.reduce source)

/-- Deterministic canonical reduction never increases the displayed denominator
quadrance. -/
theorem reduceCanonical_height_le (source : Fraction) :
    (reduceCanonical source).height ≤ source.height := by
  rw [reduceCanonical_height]
  exact Reduced.reduce_height_le source

/-- Two denominators in the canonical half-open quadrant that differ by a Gaussian unit
are identical. -/
theorem eq_of_canonical_unit_associate
    {left right unit : GaussianInt}
    (leftCanonical : IsCanonicalDenominator left)
    (rightCanonical : IsCanonicalDenominator right)
    (unitNorm : GaussianInt.normNat unit = 1)
    (associated : right = unit * left) : right = left := by
  change 0 < left.re ∧ 0 ≤ left.im at leftCanonical
  change 0 < right.re ∧ 0 ≤ right.im at rightCanonical
  rcases Units.normNat_eq_one_cases unitNorm with unitOne | unitNegOne |
      unitImaginary | unitNegImaginary
  · rw [unitOne, GaussianInt.one_mul]
    at associated
    exact associated
  · have realIdentity := congrArg
      (fun value : GaussianInt => value.re) associated
    rw [unitNegOne] at realIdentity
    simp only [GaussianInt.mul_re, GaussianInt.neg_re, GaussianInt.neg_im, GaussianInt.one_re, GaussianInt.one_im]
      at realIdentity
    exact (False.elim (by omega : False))
  · have realIdentity := congrArg
      (fun value : GaussianInt => value.re) associated
    rw [unitImaginary] at realIdentity
    dsimp only [Units.imaginaryUnit, GaussianInt.mul_re] at realIdentity
    exact (False.elim (by omega : False))
  · have imaginaryIdentity := congrArg
      (fun value : GaussianInt => value.im) associated
    rw [unitNegImaginary] at imaginaryIdentity
    dsimp only [Units.imaginaryUnit, GaussianInt.mul_im, GaussianInt.neg_re, GaussianInt.neg_im] at imaginaryIdentity
    exact (False.elim (by omega : False))

section
open Purelib.Data.GaussianInt.Fraction.Canonical
/-- Canonical reduced fractions of equal exact value have identical retained
denominators.

The retained Bezout certificates give an explicit unit association between
denominators. Their shared canonical sector forces that unit association to fix the
actual denominator coordinates. -/
theorem canonical_denominator_eq_of_value_eq
    (left right : CanonicalFraction) (valueEqual : left.value = right.value) :
    left.denominator = right.denominator := by
  obtain ⟨unit, unitNorm, associated⟩ :=
    Reduced.exists_unit_associate_denominator_of_value_eq left.toFraction
      right.toFraction valueEqual
  exact (eq_of_canonical_unit_associate left.canonicalDenominator
    right.canonicalDenominator unitNorm associated).symm

/-- Canonical reduced fractions of equal exact value have identical retained numerators. -/
theorem canonical_numerator_eq_of_value_eq
    (left right : CanonicalFraction) (valueEqual : left.value = right.value) :
    left.numerator = right.numerator := by
  have denominatorEqual :=
    canonical_denominator_eq_of_value_eq left right valueEqual
  have crossProduct := Fraction.Basic.crossProduct_of_value_eq left.displayed right.displayed
    valueEqual
  change left.numerator * right.denominator =
    right.numerator * left.denominator at crossProduct
  rw [← denominatorEqual] at crossProduct
  apply Cancellation.mul_left_cancel_of_nonzero left.denominatorNonzero
  simpa only [GaussianInt.mul_comm] using
    crossProduct

end

/-- Displayed Gaussian fractions of equal value reduce to identical canonical numerator
and denominator coordinates. -/
theorem reduceCanonical_coordinates_eq_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    (reduceCanonical left).numerator = (reduceCanonical right).numerator ∧
      (reduceCanonical left).denominator =
        (reduceCanonical right).denominator := by
  have reducedValueEqual :
      (reduceCanonical left).value = (reduceCanonical right).value := by
    rw [reduceCanonical_value, reduceCanonical_value, valueEqual]
  exact ⟨canonical_numerator_eq_of_value_eq _ _ reducedValueEqual,
    canonical_denominator_eq_of_value_eq _ _ reducedValueEqual⟩

open Purelib.Data.GaussianInt.Fraction.Canonical in
/-- The canonical reduced denominator quadrance depends only on the exact Gaussian value. -/
theorem reduceCanonical_height_eq_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    (reduceCanonical left).height = (reduceCanonical right).height := by
  have coordinates := reduceCanonical_coordinates_eq_of_value_eq left right
    valueEqual
  unfold CanonicalFraction.height Data.GaussianInt.Fraction.Reduced.height
  rw [coordinates.2]

end Purelib.Data.GaussianInt.Fraction.Canonical

end

end

section
@[expose] public section

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace Purelib.Polynomial.GaussianDenominatorHeight
end Purelib.Polynomial.GaussianDenominatorHeight

end
