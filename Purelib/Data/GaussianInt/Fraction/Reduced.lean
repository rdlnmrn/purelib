module

import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Cancellation
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.GaussianInt.GCD
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.GaussianInt.Fraction

public section

/-!
# Reduced Gaussian-integer fractions

This file turns the executable extended Gaussian Euclidean certificate into a
reduced numerator--denominator record.  Coprimality is carried by displayed
Bezout coefficients rather than by an abstract ideal or quotient.  It also
proves constructively that two reduced records with the same value have
unit-associate denominators and hence the same denominator quadrance.
-/

namespace Purelib.Data.GaussianInt.Fraction

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
set_option genInjectivity false in
/-- Retain a reduced Gaussian fraction together with explicit Bezout coefficients.

The original integral numerator and nonzero denominator satisfy a displayed linear
combination equal to one. This certifies that every common integral factor has unit
quadrance. -/
structure Reduced where
  /-- The retained Gaussian-integer numerator. -/ numerator : GaussianInt
  /-- The retained Gaussian-integer denominator. -/ denominator : GaussianInt
  /-- The exact retained denominator is nonzero. -/ denominatorNonzero : denominator ≠ 0
  /-- The retained integral coefficient of the numerator in the Bezout identity. -/ leftCoefficient : GaussianInt
  /-- The retained integral coefficient of the denominator in the Bezout identity. -/ rightCoefficient : GaussianInt
  /-- The retained coefficients combine this numerator and denominator to exactly one. -/ bezout :
    1 = leftCoefficient * numerator + rightCoefficient * denominator

constructive_injectivity Reduced

derive_exposed_repr Reduced

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

namespace Reduced

end Reduced
namespace Reduced

end Reduced
namespace Reduced

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Forget only the reduction certificate, retaining the exact numerator, denominator and
nonzero evidence. -/
@[expose] def displayed (fraction : Reduced) :
  GaussianInt.Fraction :=
  { numerator := fraction.numerator
    denominator := fraction.denominator
    denominatorNonzero := fraction.denominatorNonzero }

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Read the exact Gaussian-rational value of the retained reduced fraction. -/
@[expose] def value (fraction : Reduced) :
  Gaussian.Basic.Canonical := fraction.displayed.value

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Read the natural quadrance of the retained reduced Gaussian denominator. -/
@[expose] def height (fraction : Reduced) : Nat :=
  GaussianInt.normNat fraction.denominator

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- The embedded denominator of a retained Gaussian fraction is nonzero. -/
theorem denominatorGaussianNonzero (fraction :
  Reduced) :
    GaussianInt.toGaussian fraction.denominator ≠ 0 :=
  fraction.displayed.denominatorGaussianNonzero

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
/-- Multiplying the exact fraction value by its embedded denominator recovers its
embedded numerator. -/
theorem value_mul_denominator (fraction : Reduced) :
    fraction.value * GaussianInt.toGaussian fraction.denominator =
      GaussianInt.toGaussian fraction.numerator :=
  fraction.displayed.value_mul_denominator

end Reduced

namespace Reduced

/-- Reduce a displayed Gaussian fraction using its computed extended Euclidean
certificate.

Retain the certificate's quotient coordinates as numerator and denominator, and its
original coefficients as a Bezout witness. Cancellation certifies that the reduced
linear combination equals one. -/
@[expose] def reduce (source : GaussianInt.Fraction) : Reduced
  := by
  let certificate := GaussianInt.GCD.extendedGCD
    source.numerator source.denominator
  have gcdNonzero : certificate.gcd ≠ 0 := by
    intro gcdZero
    have denominatorZero := certificate.right_factor
    rw [gcdZero, zero_mul] at denominatorZero
    exact source.denominatorNonzero denominatorZero
  have denominatorQuotientNonzero : certificate.rightQuotient ≠ 0 := by
    intro quotientZero
    have denominatorZero := certificate.right_factor
    rw [quotientZero, mul_zero] at denominatorZero
    exact source.denominatorNonzero denominatorZero
  have reducedBezout :
      1 = certificate.leftCoefficient * certificate.leftQuotient +
        certificate.rightCoefficient * certificate.rightQuotient := by
    apply Eq.symm
    apply GaussianInt.Cancellation.mul_left_cancel_of_nonzero gcdNonzero
    calc
      certificate.gcd *
            (certificate.leftCoefficient * certificate.leftQuotient +
              certificate.rightCoefficient * certificate.rightQuotient) =
          certificate.leftCoefficient *
              (certificate.gcd * certificate.leftQuotient) +
            certificate.rightCoefficient *
              (certificate.gcd * certificate.rightQuotient) := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
          ring1
      _ = certificate.leftCoefficient * source.numerator +
            certificate.rightCoefficient * source.denominator := by
        rw [← certificate.left_factor, ← certificate.right_factor]
      _ = certificate.gcd := certificate.bezout.symm
      _ = certificate.gcd * 1 := by rw [mul_one]
  exact
    { numerator := certificate.leftQuotient
      denominator := certificate.rightQuotient
      denominatorNonzero := denominatorQuotientNonzero
      leftCoefficient := certificate.leftCoefficient
      rightCoefficient := certificate.rightCoefficient
      bezout := reducedBezout }

/-- The executable Gaussian Euclidean reduction preserves the displayed exact fraction
value. -/
theorem reduce_value (source : GaussianInt.Fraction) :
    (reduce source).value = source.value := by
  let certificate := GaussianInt.GCD.extendedGCD
    source.numerator source.denominator
  apply Basic.value_eq_of_crossProduct
  change
    (reduce source).numerator * source.denominator =
      source.numerator * (reduce source).denominator
  change certificate.leftQuotient * source.denominator =
    source.numerator * certificate.rightQuotient
  calc
    certificate.leftQuotient * source.denominator =
        certificate.leftQuotient *
          (certificate.gcd * certificate.rightQuotient) := by
      exact congrArg (fun value => certificate.leftQuotient * value)
        certificate.right_factor
    _ = (certificate.gcd * certificate.leftQuotient) *
          certificate.rightQuotient := by
      apply GaussianInt.ext <;>
        simp only [GaussianInt.mul_re, GaussianInt.mul_im] <;>
        ring1
    _ = source.numerator * certificate.rightQuotient := by
      exact congrArg (fun value => value * certificate.rightQuotient)
        certificate.left_factor.symm

/-- The original denominator quadrance factors into gcd quadrance times reduced
denominator quadrance. -/
theorem reduce_height_factor (source : GaussianInt.Fraction) :
    source.height =
      GaussianInt.normNat
          (GaussianInt.GCD.extendedGCD
            source.numerator source.denominator).gcd *
        (reduce source).height := by
  let certificate := GaussianInt.GCD.extendedGCD
    source.numerator source.denominator
  change GaussianInt.normNat source.denominator =
    GaussianInt.normNat certificate.gcd * GaussianInt.normNat certificate.rightQuotient
  calc
    GaussianInt.normNat source.denominator =
        GaussianInt.normNat (certificate.gcd * certificate.rightQuotient) :=
      congrArg GaussianInt.normNat certificate.right_factor
    _ = GaussianInt.normNat certificate.gcd * GaussianInt.normNat certificate.rightQuotient :=
      GaussianInt.normNat_mul _ _

/-- Gaussian Euclidean reduction never increases displayed denominator quadrance. -/
theorem reduce_height_le (source : GaussianInt.Fraction) :
    (reduce source).height ≤ source.height := by
  let certificate := GaussianInt.GCD.extendedGCD
    source.numerator source.denominator
  have gcdNonzero : certificate.gcd ≠ 0 := by
    intro gcdZero
    have denominatorZero := certificate.right_factor
    rw [gcdZero, zero_mul] at denominatorZero
    exact source.denominatorNonzero denominatorZero
  have gcdNormPositive := GaussianInt.normNat_pos gcdNonzero
  rw [reduce_height_factor]
  calc
    (reduce source).height = 1 * (reduce source).height :=
      (Nat.one_mul _).symm
    _ ≤ GaussianInt.normNat certificate.gcd * (reduce source).height :=
      Nat.mul_le_mul_right _ gcdNormPositive

/-- Every explicit common factor of a reduced numerator and denominator has natural
quadrance one.

Factor the retained Bezout identity and take natural norms; positivity of the
displayed factors forces the divisor norm to be exactly one. -/
theorem commonFactor_normNat_eq_one
    (fraction : Reduced) (factor numeratorQuotient denominatorQuotient :
      GaussianInt)
    (numeratorFactor : fraction.numerator = factor * numeratorQuotient)
    (denominatorFactor : fraction.denominator = factor * denominatorQuotient) :
    GaussianInt.normNat factor = 1 := by
  have factorNonzero : factor ≠ 0 := by
    intro factorZero
    rw [factorZero, zero_mul] at denominatorFactor
    exact fraction.denominatorNonzero denominatorFactor
  have factoredBezout :
      1 = factor *
        (fraction.leftCoefficient * numeratorQuotient +
          fraction.rightCoefficient * denominatorQuotient) := by
    calc
      1 = fraction.leftCoefficient * fraction.numerator +
          fraction.rightCoefficient * fraction.denominator := fraction.bezout
      _ = factor *
          (fraction.leftCoefficient * numeratorQuotient +
            fraction.rightCoefficient * denominatorQuotient) := by
        rw [numeratorFactor, denominatorFactor]
        apply GaussianInt.ext <;>
          simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
          ring1
  have normIdentity := congrArg GaussianInt.normNat factoredBezout
  rw [GaussianInt.normNat_mul] at normIdentity
  have factorPositive := GaussianInt.normNat_pos factorNonzero
  change 1 = GaussianInt.normNat factor *
    GaussianInt.normNat
      (fraction.leftCoefficient * numeratorQuotient +
        fraction.rightCoefficient * denominatorQuotient) at normIdentity
  let quotientNorm := GaussianInt.normNat
    (fraction.leftCoefficient * numeratorQuotient +
      fraction.rightCoefficient * denominatorQuotient)
  change 1 = GaussianInt.normNat factor * quotientNorm at normIdentity
  have quotientNormPositive : 0 < quotientNorm := by
    apply Nat.pos_of_ne_zero
    intro quotientNormZero
    change quotientNorm = 0 at quotientNormZero
    rw [quotientNormZero, Nat.mul_zero] at normIdentity
    contradiction
  have factorNormLeOne : GaussianInt.normNat factor ≤ 1 := by
    calc
      GaussianInt.normNat factor = GaussianInt.normNat factor * 1 := (Nat.mul_one _).symm
      _ ≤ GaussianInt.normNat factor * quotientNorm :=
        Nat.mul_le_mul_left _ quotientNormPositive
      _ = 1 := normIdentity.symm
  exact Nat.le_antisymm factorNormLeOne (Nat.succ_le_of_lt factorPositive)

/-- Reduced Gaussian fractions of equal value have denominators related by an explicit
unit factor.

The retained Bezout coefficients compute that factor; equality of cross-products
certifies the denominator identity and unit quadrance. -/
theorem exists_unit_associate_denominator_of_value_eq
    (left right : Reduced) (valueEqual : left.value = right.value) :
    ∃ unit : GaussianInt,
      GaussianInt.normNat unit = 1 ∧ right.denominator = unit * left.denominator := by
  have crossProduct := Basic.crossProduct_of_value_eq left.displayed right.displayed
    valueEqual
  change left.numerator * right.denominator =
    right.numerator * left.denominator at crossProduct
  let unit := left.leftCoefficient * right.numerator +
    left.rightCoefficient * right.denominator
  have denominatorIdentity : right.denominator = unit * left.denominator := by
    calc
      right.denominator = 1 * right.denominator := by rw [one_mul]
      _ = (left.leftCoefficient * left.numerator +
            left.rightCoefficient * left.denominator) * right.denominator := by
        rw [← left.bezout]
      _ = unit * left.denominator := by
        dsimp only [unit]
        calc
          (left.leftCoefficient * left.numerator +
                left.rightCoefficient * left.denominator) *
              right.denominator =
            left.leftCoefficient *
                (left.numerator * right.denominator) +
              left.rightCoefficient *
                (left.denominator * right.denominator) := by
            apply GaussianInt.ext <;>
              simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
              ring1
          _ = left.leftCoefficient *
                (right.numerator * left.denominator) +
              left.rightCoefficient *
                (left.denominator * right.denominator) := by
            rw [crossProduct]
          _ = (left.leftCoefficient * right.numerator +
                left.rightCoefficient * right.denominator) *
              left.denominator := by
            apply GaussianInt.ext <;>
              simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
              ring1
  have unitNorm := commonFactor_normNat_eq_one right unit left.numerator
    left.denominator
    (by
      dsimp only [unit]
      calc
        right.numerator = right.numerator * 1 := by
          rw [_root_.mul_one]
        _ = right.numerator *
            (left.leftCoefficient * left.numerator +
              left.rightCoefficient * left.denominator) := by
          rw [← left.bezout]
        _ = (left.leftCoefficient * right.numerator +
              left.rightCoefficient * right.denominator) *
            left.numerator := by
          calc
            right.numerator *
                  (left.leftCoefficient * left.numerator +
                    left.rightCoefficient * left.denominator) =
                left.leftCoefficient * right.numerator * left.numerator +
                  left.rightCoefficient *
                    (right.numerator * left.denominator) := by
              apply GaussianInt.ext <;>
                simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
                ring1
            _ = left.leftCoefficient * right.numerator * left.numerator +
                  left.rightCoefficient *
                    (left.numerator * right.denominator) := by
              rw [crossProduct]
            _ = (left.leftCoefficient * right.numerator +
                  left.rightCoefficient * right.denominator) *
                left.numerator := by
              apply GaussianInt.ext <;>
                simp only [GaussianInt.mul_re, GaussianInt.mul_im, GaussianInt.add_re, GaussianInt.add_im] <;>
                ring1)
    denominatorIdentity
  exact ⟨unit, unitNorm, denominatorIdentity⟩

/-- Reduced Gaussian fractions with equal exact value have equal denominator quadrance. -/
theorem height_eq_of_value_eq
    (left right : Reduced) (valueEqual : left.value = right.value) :
    left.height = right.height := by
  obtain ⟨unit, unitNorm, denominatorIdentity⟩ :=
    exists_unit_associate_denominator_of_value_eq left right valueEqual
  unfold height
  rw [denominatorIdentity, GaussianInt.normNat_mul, unitNorm, Nat.one_mul]

end Reduced
end Purelib.Data.GaussianInt.Fraction

end
