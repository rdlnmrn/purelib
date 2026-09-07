import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.GaussianEuclidean

/-!
# Reduced Gaussian-integer fractions

This file turns the executable extended Gaussian Euclidean certificate into a
reduced numerator--denominator record.  Coprimality is carried by displayed
Bezout coefficients rather than by an abstract ideal or quotient.  It also
proves constructively that two reduced records with the same value have
unit-associate denominators and hence the same denominator quadrance.
-/

namespace RFAP.ReducedGaussianFraction

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev DisplayedFraction := RFAP.HurwitzRational.Fraction

open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- A Gaussian fraction with displayed Bezout data certifying that its
numerator and denominator have no common nonunit factor. -/
structure Fraction where
  numerator : GaussianInt
  denominator : GaussianInt
  denominatorNonzero : denominator ≠ 0
  leftCoefficient : GaussianInt
  rightCoefficient : GaussianInt
  bezout :
    1 = leftCoefficient * numerator + rightCoefficient * denominator
deriving Repr

namespace Fraction

/-- Forget the reduction certificate but retain the displayed fraction. -/
def displayed (fraction : Fraction) : DisplayedFraction :=
  { numerator := fraction.numerator
    denominator := fraction.denominator
    denominatorNonzero := fraction.denominatorNonzero }

/-- Exact Gaussian value of a reduced displayed fraction. -/
def value (fraction : Fraction) : Gaussian := fraction.displayed.value

/-- Intrinsic reduced denominator quadrance. -/
def height (fraction : Fraction) : Nat := normNat fraction.denominator

theorem denominatorGaussianNonzero (fraction : Fraction) :
    toGaussian fraction.denominator ≠ 0 :=
  fraction.displayed.denominatorGaussianNonzero

theorem value_mul_denominator (fraction : Fraction) :
    fraction.value * toGaussian fraction.denominator =
      toGaussian fraction.numerator :=
  fraction.displayed.value_mul_denominator

end Fraction

/-- Direct left cancellation in the displayed Gaussian integers, proved by
embedding into the constructive Gaussian field. -/
theorem mul_left_cancel_of_nonzero
    {factor left right : GaussianInt} (factorNonzero : factor ≠ 0)
    (identity : factor * left = factor * right) : left = right := by
  apply toGaussian_injective
  have embedded := congrArg toGaussian identity
  rw [toGaussian_mul, toGaussian_mul] at embedded
  have factorGaussianNonzero : toGaussian factor ≠ 0 := by
    intro zero
    exact factorNonzero (toGaussian_eq_zero.mp zero)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    factorGaussianNonzero
  simpa only [RFAP.ConstructiveGaussian.Gaussian.mul_comm] using embedded

/-- Equality of displayed cross-products implies equality of the exact
Gaussian fraction values. -/
theorem value_eq_of_crossProduct
    (left right : DisplayedFraction)
    (crossProduct :
      left.numerator * right.denominator =
        right.numerator * left.denominator) :
    left.value = right.value := by
  have denominatorProductNonzero :
      toGaussian left.denominator * toGaussian right.denominator ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      left.denominatorGaussianNonzero right.denominatorGaussianNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorProductNonzero
  calc
    left.value *
          (toGaussian left.denominator * toGaussian right.denominator) =
        (left.value * toGaussian left.denominator) *
          toGaussian right.denominator := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = toGaussian left.numerator * toGaussian right.denominator := by
      rw [left.value_mul_denominator]
    _ = toGaussian (left.numerator * right.denominator) := by
      rw [toGaussian_mul]
    _ = toGaussian (right.numerator * left.denominator) := by
      rw [crossProduct]
    _ = toGaussian right.numerator * toGaussian left.denominator := by
      rw [toGaussian_mul]
    _ = (right.value * toGaussian right.denominator) *
          toGaussian left.denominator := by
      rw [right.value_mul_denominator]
    _ = right.value *
          (toGaussian left.denominator * toGaussian right.denominator) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1

/-- Equal exact values have equal displayed cross-products. -/
theorem crossProduct_of_value_eq
    (left right : DisplayedFraction) (valueEqual : left.value = right.value) :
    left.numerator * right.denominator =
      right.numerator * left.denominator := by
  apply toGaussian_injective
  rw [toGaussian_mul, toGaussian_mul]
  calc
    toGaussian left.numerator * toGaussian right.denominator =
        (left.value * toGaussian left.denominator) *
          toGaussian right.denominator := by
      rw [left.value_mul_denominator]
    _ = left.value *
          (toGaussian left.denominator * toGaussian right.denominator) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = right.value *
          (toGaussian left.denominator * toGaussian right.denominator) := by
      rw [valueEqual]
    _ = (right.value * toGaussian right.denominator) *
          toGaussian left.denominator := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = toGaussian right.numerator * toGaussian left.denominator := by
      rw [right.value_mul_denominator]

/-- Reduce a displayed Gaussian fraction by its executable extended Euclidean
certificate.  The returned quotient coordinates are accompanied by an exact
Bezout certificate. -/
def reduce (source : DisplayedFraction) : Fraction := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
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
    apply mul_left_cancel_of_nonzero gcdNonzero
    calc
      certificate.gcd *
            (certificate.leftCoefficient * certificate.leftQuotient +
              certificate.rightCoefficient * certificate.rightQuotient) =
          certificate.leftCoefficient *
              (certificate.gcd * certificate.leftQuotient) +
            certificate.rightCoefficient *
              (certificate.gcd * certificate.rightQuotient) := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [mul_re, mul_im, add_re, add_im] <;>
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

/-- Executable reduction preserves the exact Gaussian value. -/
theorem reduce_value (source : DisplayedFraction) :
    (reduce source).value = source.value := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    source.numerator source.denominator
  apply value_eq_of_crossProduct
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
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
        simp only [mul_re, mul_im] <;>
        ring1
    _ = source.numerator * certificate.rightQuotient := by
      exact congrArg (fun value => value * certificate.rightQuotient)
        certificate.left_factor.symm

/-- The displayed denominator quadrance factors exactly into the gcd
quadrance and the reduced denominator quadrance. -/
theorem reduce_height_factor (source : DisplayedFraction) :
    source.height =
      normNat
          (RFAP.GaussianEuclidean.extendedGCD
            source.numerator source.denominator).gcd *
        (reduce source).height := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    source.numerator source.denominator
  change normNat source.denominator =
    normNat certificate.gcd * normNat certificate.rightQuotient
  calc
    normNat source.denominator =
        normNat (certificate.gcd * certificate.rightQuotient) :=
      congrArg normNat certificate.right_factor
    _ = normNat certificate.gcd * normNat certificate.rightQuotient :=
      normNat_mul _ _

/-- Euclidean reduction never increases denominator quadrance. -/
theorem reduce_height_le (source : DisplayedFraction) :
    (reduce source).height ≤ source.height := by
  let certificate := RFAP.GaussianEuclidean.extendedGCD
    source.numerator source.denominator
  have gcdNonzero : certificate.gcd ≠ 0 := by
    intro gcdZero
    have denominatorZero := certificate.right_factor
    rw [gcdZero, zero_mul] at denominatorZero
    exact source.denominatorNonzero denominatorZero
  have gcdNormPositive := normNat_pos gcdNonzero
  rw [reduce_height_factor]
  calc
    (reduce source).height = 1 * (reduce source).height :=
      (Nat.one_mul _).symm
    _ ≤ normNat certificate.gcd * (reduce source).height :=
      Nat.mul_le_mul_right _ gcdNormPositive

/-- A common displayed divisor of a reduced numerator and denominator must
have unit quadrance. -/
theorem commonFactor_normNat_eq_one
    (fraction : Fraction) (factor numeratorQuotient denominatorQuotient :
      GaussianInt)
    (numeratorFactor : fraction.numerator = factor * numeratorQuotient)
    (denominatorFactor : fraction.denominator = factor * denominatorQuotient) :
    normNat factor = 1 := by
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
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [mul_re, mul_im, add_re, add_im] <;>
          ring1
  have normIdentity := congrArg normNat factoredBezout
  rw [normNat_mul] at normIdentity
  have factorPositive := normNat_pos factorNonzero
  change 1 = normNat factor *
    normNat
      (fraction.leftCoefficient * numeratorQuotient +
        fraction.rightCoefficient * denominatorQuotient) at normIdentity
  let quotientNorm := normNat
    (fraction.leftCoefficient * numeratorQuotient +
      fraction.rightCoefficient * denominatorQuotient)
  change 1 = normNat factor * quotientNorm at normIdentity
  have quotientNormPositive : 0 < quotientNorm := by
    apply Nat.pos_of_ne_zero
    intro quotientNormZero
    change quotientNorm = 0 at quotientNormZero
    rw [quotientNormZero, Nat.mul_zero] at normIdentity
    contradiction
  have factorNormLeOne : normNat factor ≤ 1 := by
    calc
      normNat factor = normNat factor * 1 := (Nat.mul_one _).symm
      _ ≤ normNat factor * quotientNorm :=
        Nat.mul_le_mul_left _ quotientNormPositive
      _ = 1 := normIdentity.symm
  exact Nat.le_antisymm factorNormLeOne (Nat.succ_le_of_lt factorPositive)

/-- Reduced presentations of one exact value have unit-associate
denominators. -/
theorem exists_unit_associate_denominator_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    ∃ unit : GaussianInt,
      normNat unit = 1 ∧ right.denominator = unit * left.denominator := by
  have crossProduct := crossProduct_of_value_eq left.displayed right.displayed
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
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
              simp only [mul_re, mul_im, add_re, add_im] <;>
              ring1
          _ = left.leftCoefficient *
                (right.numerator * left.denominator) +
              left.rightCoefficient *
                (left.denominator * right.denominator) := by
            rw [crossProduct]
          _ = (left.leftCoefficient * right.numerator +
                left.rightCoefficient * right.denominator) *
              left.denominator := by
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
              simp only [mul_re, mul_im, add_re, add_im] <;>
              ring1
  have unitNorm := commonFactor_normNat_eq_one right unit left.numerator
    left.denominator
    (by
      dsimp only [unit]
      calc
        right.numerator = right.numerator * 1 := by
          rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_one]
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
              apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
                simp only [mul_re, mul_im, add_re, add_im] <;>
                ring1
            _ = left.leftCoefficient * right.numerator * left.numerator +
                  left.rightCoefficient *
                    (left.numerator * right.denominator) := by
              rw [crossProduct]
            _ = (left.leftCoefficient * right.numerator +
                  left.rightCoefficient * right.denominator) *
                left.numerator := by
              apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
                simp only [mul_re, mul_im, add_re, add_im] <;>
                ring1)
    denominatorIdentity
  exact ⟨unit, unitNorm, denominatorIdentity⟩

/-- The denominator quadrance is independent of the chosen reduced
presentation. -/
theorem height_eq_of_value_eq
    (left right : Fraction) (valueEqual : left.value = right.value) :
    left.height = right.height := by
  obtain ⟨unit, unitNorm, denominatorIdentity⟩ :=
    exists_unit_associate_denominator_of_value_eq left right valueEqual
  unfold Fraction.height
  rw [denominatorIdentity, normNat_mul, unitNorm, Nat.one_mul]

/-! ## Deterministic unit canonicalisation -/

/-- The displayed Gaussian unit `i`, kept local to the reduced-fraction
implementation. -/
def imaginaryUnit : GaussianInt := ⟨0, 1⟩

/-- The half-open first quadrant used to choose one representative from each
nonzero Gaussian-unit orbit. -/
def IsCanonicalDenominator (denominator : GaussianInt) : Prop :=
  0 < denominator.re ∧ 0 ≤ denominator.im

instance isCanonicalDenominatorDecidable (denominator : GaussianInt) :
    Decidable (IsCanonicalDenominator denominator) := by
  unfold IsCanonicalDenominator
  infer_instance

/-- Deterministically select the unit rotating a nonzero Gaussian integer
into the half-open first quadrant. -/
def canonicalizingUnit (denominator : GaussianInt) : GaussianInt :=
  if 0 < denominator.re then
    if 0 ≤ denominator.im then 1 else imaginaryUnit
  else if denominator.re < 0 then
    if 0 < denominator.im then -imaginaryUnit else -1
  else if 0 < denominator.im then
    -imaginaryUnit
  else
    imaginaryUnit

/-- Apply the selected unit to a displayed Gaussian integer. -/
def canonicalAssociate (denominator : GaussianInt) : GaussianInt :=
  canonicalizingUnit denominator * denominator

theorem canonicalizingUnit_normNat (denominator : GaussianInt) :
    normNat (canonicalizingUnit denominator) = 1 := by
  unfold canonicalizingUnit
  split
  · split <;> decide
  · split
    · split <;> decide
    · split <;> decide

/-- The deterministic associate of every nonzero denominator lies in the
chosen half-open first quadrant. -/
theorem canonicalAssociate_isCanonical
    {denominator : GaussianInt} (denominatorNonzero : denominator ≠ 0) :
    IsCanonicalDenominator (canonicalAssociate denominator) := by
  rcases denominator with ⟨real, imaginary⟩
  cases real with
  | ofNat realNatural =>
      cases realNatural with
      | zero =>
          cases imaginary with
          | ofNat imaginaryNatural =>
              cases imaginaryNatural with
              | zero => exact (denominatorNonzero rfl).elim
              | succ predecessor =>
                  simp [IsCanonicalDenominator, canonicalAssociate,
                    canonicalizingUnit, imaginaryUnit]
          | negSucc predecessor =>
              simp [IsCanonicalDenominator, canonicalAssociate,
                canonicalizingUnit, imaginaryUnit]
      | succ predecessor =>
          cases imaginary with
          | ofNat imaginaryNatural =>
              simp [IsCanonicalDenominator, canonicalAssociate,
                canonicalizingUnit]
          | negSucc imaginaryPredecessor =>
              simp [IsCanonicalDenominator, canonicalAssociate,
                canonicalizingUnit, imaginaryUnit]
              omega
  | negSucc predecessor =>
      cases imaginary with
      | ofNat imaginaryNatural =>
          cases imaginaryNatural with
          | zero =>
              simp [IsCanonicalDenominator, canonicalAssociate,
                canonicalizingUnit]
          | succ imaginaryPredecessor =>
              simp [IsCanonicalDenominator, canonicalAssociate,
                canonicalizingUnit, imaginaryUnit]
              omega
      | negSucc imaginaryPredecessor =>
          simp [IsCanonicalDenominator, canonicalAssociate,
            canonicalizingUnit]
          omega

/-- A reduced fraction together with its deterministic unit-normalized
denominator. -/
structure CanonicalFraction extends Fraction where
  canonicalDenominator : IsCanonicalDenominator denominator
deriving Repr

namespace CanonicalFraction

def value (fraction : CanonicalFraction) : Gaussian := fraction.toFraction.value

def height (fraction : CanonicalFraction) : Nat := fraction.toFraction.height

def displayed (fraction : CanonicalFraction) : DisplayedFraction :=
  fraction.toFraction.displayed

end CanonicalFraction

/-- Rotate a reduced fraction into the deterministic denominator sector,
scaling its numerator by exactly the same displayed unit. -/
def canonicalize (fraction : Fraction) : CanonicalFraction := by
  let unit := canonicalizingUnit fraction.denominator
  have unitNorm : normNat unit = 1 :=
    canonicalizingUnit_normNat fraction.denominator
  have denominatorNonzero : unit * fraction.denominator ≠ 0 := by
    intro productZero
    have normZero := congrArg normNat productZero
    rw [normNat_mul, unitNorm, Nat.one_mul] at normZero
    have zeroNorm : normNat (0 : GaussianInt) = 0 := rfl
    rw [zeroNorm] at normZero
    exact (Nat.ne_of_gt (normNat_pos fraction.denominatorNonzero)) normZero
  have conjugateUnitProduct : conj unit * unit = 1 := by
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm,
      mul_conj, unitNorm]
    rfl
  have transportedBezout :
      1 = (fraction.leftCoefficient * conj unit) *
            (unit * fraction.numerator) +
          (fraction.rightCoefficient * conj unit) *
            (unit * fraction.denominator) := by
    calc
      1 = fraction.leftCoefficient * fraction.numerator +
          fraction.rightCoefficient * fraction.denominator := fraction.bezout
      _ = (fraction.leftCoefficient * conj unit) *
            (unit * fraction.numerator) +
          (fraction.rightCoefficient * conj unit) *
            (unit * fraction.denominator) := by
        calc
          fraction.leftCoefficient * fraction.numerator +
                fraction.rightCoefficient * fraction.denominator =
              (conj unit * unit) *
                (fraction.leftCoefficient * fraction.numerator +
                  fraction.rightCoefficient * fraction.denominator) := by
            rw [conjugateUnitProduct, one_mul]
          _ = (fraction.leftCoefficient * conj unit) *
                (unit * fraction.numerator) +
              (fraction.rightCoefficient * conj unit) *
                (unit * fraction.denominator) := by
            apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
              simp only [mul_re, mul_im, add_re, add_im] <;>
              ring1
  exact
    { numerator := unit * fraction.numerator
      denominator := unit * fraction.denominator
      denominatorNonzero := denominatorNonzero
      leftCoefficient := fraction.leftCoefficient * conj unit
      rightCoefficient := fraction.rightCoefficient * conj unit
      bezout := transportedBezout
      canonicalDenominator := canonicalAssociate_isCanonical
        fraction.denominatorNonzero }

/-- Canonicalisation preserves the exact reduced Gaussian value. -/
theorem canonicalize_value (fraction : Fraction) :
    (canonicalize fraction).value = fraction.value := by
  apply value_eq_of_crossProduct
  change
    (canonicalize fraction).numerator * fraction.denominator =
      fraction.numerator * (canonicalize fraction).denominator
  dsimp only [canonicalize]
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [mul_re, mul_im] <;>
    ring1

/-- Unit canonicalisation preserves denominator quadrance. -/
theorem canonicalize_height (fraction : Fraction) :
    (canonicalize fraction).height = fraction.height := by
  unfold CanonicalFraction.height Fraction.height
  change normNat
      (canonicalizingUnit fraction.denominator * fraction.denominator) =
    normNat fraction.denominator
  rw [normNat_mul, canonicalizingUnit_normNat, Nat.one_mul]

/-- Fully reduce and deterministically unit-normalize a displayed Gaussian
fraction. -/
def reduceCanonical (source : DisplayedFraction) : CanonicalFraction :=
  canonicalize (reduce source)

theorem reduceCanonical_value (source : DisplayedFraction) :
    (reduceCanonical source).value = source.value := by
  rw [reduceCanonical, canonicalize_value, reduce_value]

theorem reduceCanonical_height (source : DisplayedFraction) :
    (reduceCanonical source).height = (reduce source).height := by
  exact canonicalize_height (reduce source)

theorem reduceCanonical_height_le (source : DisplayedFraction) :
    (reduceCanonical source).height ≤ source.height := by
  rw [reduceCanonical_height]
  exact reduce_height_le source

/-! ## Uniqueness of the canonical displayed coordinates -/

private theorem nat_le_square_of_pos {value : Nat} (positive : 0 < value) :
    value ≤ value ^ 2 := by
  simpa only [pow_two] using Nat.le_mul_of_pos_right value positive

private theorem int_eq_one_or_neg_one_of_natAbs_eq_one {value : Int}
    (magnitude : value.natAbs = 1) : value = 1 ∨ value = -1 := by
  cases value with
  | ofNat natural =>
      change natural = 1 at magnitude
      subst natural
      left
      rfl
  | negSucc predecessor =>
      change predecessor + 1 = 1 at magnitude
      have predecessorZero : predecessor = 0 :=
        Nat.add_right_cancel magnitude
      subst predecessor
      right
      rfl

/-- The only displayed Gaussian integers of quadrance one are the four
units used by the canonicalisation calculation. -/
theorem normNat_eq_one_cases {unit : GaussianInt}
    (unitNorm : normNat unit = 1) :
    unit = 1 ∨ unit = -1 ∨ unit = imaginaryUnit ∨ unit = -imaginaryUnit := by
  have componentIdentity := normNat_eq_component_squares unit
  rw [unitNorm] at componentIdentity
  have realSquareLe : unit.re.natAbs ^ 2 ≤ 1 := by
    calc
      unit.re.natAbs ^ 2 ≤
          unit.re.natAbs ^ 2 + unit.im.natAbs ^ 2 := Nat.le_add_right _ _
      _ = 1 := componentIdentity.symm
  have imaginarySquareLe : unit.im.natAbs ^ 2 ≤ 1 := by
    calc
      unit.im.natAbs ^ 2 ≤
          unit.re.natAbs ^ 2 + unit.im.natAbs ^ 2 := Nat.le_add_left _ _
      _ = 1 := componentIdentity.symm
  have realLeOne : unit.re.natAbs ≤ 1 := by
    by_cases realZero : unit.re.natAbs = 0
    · rw [realZero]
      exact Nat.zero_le 1
    · exact (nat_le_square_of_pos (Nat.pos_of_ne_zero realZero)).trans
        realSquareLe
  have imaginaryLeOne : unit.im.natAbs ≤ 1 := by
    by_cases imaginaryZero : unit.im.natAbs = 0
    · rw [imaginaryZero]
      exact Nat.zero_le 1
    · exact (nat_le_square_of_pos
        (Nat.pos_of_ne_zero imaginaryZero)).trans imaginarySquareLe
  have realCases : unit.re.natAbs = 0 ∨ unit.re.natAbs = 1 := by
    rcases Nat.eq_zero_or_pos unit.re.natAbs with realZero | realPositive
    · exact Or.inl realZero
    · exact Or.inr (Nat.le_antisymm realLeOne realPositive)
  have imaginaryCases : unit.im.natAbs = 0 ∨ unit.im.natAbs = 1 := by
    rcases Nat.eq_zero_or_pos unit.im.natAbs with imaginaryZero |
      imaginaryPositive
    · exact Or.inl imaginaryZero
    · exact Or.inr (Nat.le_antisymm imaginaryLeOne imaginaryPositive)
  rcases realCases with realZero | realOne
  · have realCoordinateZero : unit.re = 0 := Int.natAbs_eq_zero.mp realZero
    rcases imaginaryCases with imaginaryZero | imaginaryOne
    · rw [realZero, imaginaryZero] at componentIdentity
      exact False.elim ((by decide : (0 : Nat) ^ 2 + 0 ^ 2 ≠ 1)
        componentIdentity.symm)
    · rcases int_eq_one_or_neg_one_of_natAbs_eq_one imaginaryOne with
        imaginaryPositive | imaginaryNegative
      · right; right; left
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
        · exact realCoordinateZero
        · exact imaginaryPositive
      · right; right; right
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
        · exact realCoordinateZero
        · simpa only [imaginaryUnit, neg_im] using imaginaryNegative
  · rcases int_eq_one_or_neg_one_of_natAbs_eq_one realOne with
      realPositive | realNegative
    · rcases imaginaryCases with imaginaryZero | imaginaryOne
      · have imaginaryCoordinateZero : unit.im = 0 :=
          Int.natAbs_eq_zero.mp imaginaryZero
        left
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
        · exact realPositive
        · exact imaginaryCoordinateZero
      · rw [realOne, imaginaryOne] at componentIdentity
        exact False.elim ((by decide : (1 : Nat) ^ 2 + 1 ^ 2 ≠ 1)
          componentIdentity.symm)
    · rcases imaginaryCases with imaginaryZero | imaginaryOne
      · have imaginaryCoordinateZero : unit.im = 0 :=
          Int.natAbs_eq_zero.mp imaginaryZero
        right; left
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
        · simpa only [neg_re, one_re] using realNegative
        · exact imaginaryCoordinateZero
      · rw [realOne, imaginaryOne] at componentIdentity
        exact False.elim ((by decide : (1 : Nat) ^ 2 + 1 ^ 2 ≠ 1)
          componentIdentity.symm)

/-- Two canonical nonzero unit associates are the same displayed Gaussian
integer. -/
theorem eq_of_canonical_unit_associate
    {left right unit : GaussianInt}
    (leftCanonical : IsCanonicalDenominator left)
    (rightCanonical : IsCanonicalDenominator right)
    (unitNorm : normNat unit = 1)
    (associated : right = unit * left) : right = left := by
  change 0 < left.re ∧ 0 ≤ left.im at leftCanonical
  change 0 < right.re ∧ 0 ≤ right.im at rightCanonical
  rcases normNat_eq_one_cases unitNorm with unitOne | unitNegOne |
      unitImaginary | unitNegImaginary
  · rw [unitOne, one_mul] at associated
    exact associated
  · have realIdentity := congrArg
      (fun value : GaussianInt => value.re) associated
    rw [unitNegOne] at realIdentity
    simp only [mul_re, neg_re, neg_im, one_re, one_im] at realIdentity
    exact (False.elim (by omega : False))
  · have realIdentity := congrArg
      (fun value : GaussianInt => value.re) associated
    rw [unitImaginary] at realIdentity
    dsimp only [imaginaryUnit, mul_re] at realIdentity
    exact (False.elim (by omega : False))
  · have imaginaryIdentity := congrArg
      (fun value : GaussianInt => value.im) associated
    rw [unitNegImaginary] at imaginaryIdentity
    dsimp only [imaginaryUnit, mul_im, neg_re, neg_im] at imaginaryIdentity
    exact (False.elim (by omega : False))

/-- Canonical reduced presentations of one exact value have identical
displayed denominators, not merely unit associates. -/
theorem canonical_denominator_eq_of_value_eq
    (left right : CanonicalFraction) (valueEqual : left.value = right.value) :
    left.denominator = right.denominator := by
  obtain ⟨unit, unitNorm, associated⟩ :=
    exists_unit_associate_denominator_of_value_eq left.toFraction
      right.toFraction valueEqual
  exact (eq_of_canonical_unit_associate left.canonicalDenominator
    right.canonicalDenominator unitNorm associated).symm

/-- Canonical reduced presentations of one exact value also have identical
displayed numerators. -/
theorem canonical_numerator_eq_of_value_eq
    (left right : CanonicalFraction) (valueEqual : left.value = right.value) :
    left.numerator = right.numerator := by
  have denominatorEqual :=
    canonical_denominator_eq_of_value_eq left right valueEqual
  have crossProduct := crossProduct_of_value_eq left.displayed right.displayed
    valueEqual
  change left.numerator * right.denominator =
    right.numerator * left.denominator at crossProduct
  rw [← denominatorEqual] at crossProduct
  apply mul_left_cancel_of_nonzero left.denominatorNonzero
  simpa only [RFAP.ConstructiveGaussianHeight.GaussianInt.mul_comm] using
    crossProduct

/-- The deterministic reduced numerator and denominator depend only on the
exact Gaussian value represented by the input. -/
theorem reduceCanonical_coordinates_eq_of_value_eq
    (left right : DisplayedFraction) (valueEqual : left.value = right.value) :
    (reduceCanonical left).numerator = (reduceCanonical right).numerator ∧
      (reduceCanonical left).denominator =
        (reduceCanonical right).denominator := by
  have reducedValueEqual :
      (reduceCanonical left).value = (reduceCanonical right).value := by
    rw [reduceCanonical_value, reduceCanonical_value, valueEqual]
  exact ⟨canonical_numerator_eq_of_value_eq _ _ reducedValueEqual,
    canonical_denominator_eq_of_value_eq _ _ reducedValueEqual⟩

/-- The canonical reduced height depends only on the exact represented value,
not on the supplied numerator--denominator presentation. -/
theorem reduceCanonical_height_eq_of_value_eq
    (left right : DisplayedFraction) (valueEqual : left.value = right.value) :
    (reduceCanonical left).height = (reduceCanonical right).height := by
  have coordinates := reduceCanonical_coordinates_eq_of_value_eq left right
    valueEqual
  unfold CanonicalFraction.height Fraction.height
  rw [coordinates.2]

end RFAP.ReducedGaussianFraction
