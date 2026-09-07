import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.CanonicalGCD

/-!
# Canonical constructive fractions

This module is the quotient-free scalar kernel.  A displayed fraction is
normalized by an executable gcd calculation to a unique positive-denominator
record.  Equality of semantic rationals is therefore ordinary structure
equality, while `Equivalent` remains available as the explicit certificate
relating differently displayed inputs.

The module intentionally does not import `mathlib.RFAP.ConstructiveFraction`.
-/

namespace RFAP.CanonicalFraction

/-- A displayed integer numerator and strictly positive natural denominator. -/
structure RawFraction where
  num : Int
  den : Nat
  den_pos : 0 < den
deriving DecidableEq

/-- Cross-multiplication equivalence of displayed fractions. -/
def Equivalent (left right : RawFraction) : Prop :=
  left.num * (right.den : Int) = right.num * (left.den : Int)

instance (left right : RawFraction) : Decidable (Equivalent left right) :=
  inferInstanceAs (Decidable
    (left.num * (right.den : Int) = right.num * (left.den : Int)))

theorem equivalent_refl (fraction : RawFraction) :
    Equivalent fraction fraction := rfl

theorem equivalent_symm {left right : RawFraction}
    (equivalent : Equivalent left right) : Equivalent right left :=
  equivalent.symm

theorem equivalent_trans {left middle right : RawFraction}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right := by
  have productZero :
      (left.num * (right.den : Int) - right.num * (left.den : Int)) *
          (middle.den : Int) = 0 := by
    dsimp only [Equivalent] at leftMiddle middleRight
    rw [sub_mul]
    calc
      left.num * (right.den : Int) * (middle.den : Int) -
          right.num * (left.den : Int) * (middle.den : Int) =
          (right.den : Int) * (left.num * (middle.den : Int)) -
            (left.den : Int) * (right.num * (middle.den : Int)) := by
              ring1
      _ = (right.den : Int) * (middle.num * (left.den : Int)) -
            (left.den : Int) * (middle.num * (right.den : Int)) := by
              rw [leftMiddle, ← middleRight]
      _ = 0 := by ring1
  have middleDenominatorNonzero : (middle.den : Int) ≠ 0 := by
    intro zero
    have denominatorZero : middle.den = 0 := Int.ofNat.inj zero
    exact (Nat.ne_of_gt middle.den_pos) denominatorZero
  have differenceZero :
      left.num * (right.den : Int) - right.num * (left.den : Int) = 0 :=
    (Int.mul_eq_zero.mp productZero).resolve_right middleDenominatorNonzero
  exact Int.sub_eq_zero.mp differenceZero

/-- Proposition-valued reducedness for a numerator magnitude and denominator.
The witnesses are explicit Bézout coefficients, not an appeal to prime
factorization or an ambient gcd theorem. -/
def Reduced (numeratorMagnitude denominator : Nat) : Prop :=
  Nonempty
    (CanonicalGCD.CoprimeCertificate numeratorMagnitude denominator)

/-- A unique gcd-reduced numerator and strictly positive denominator.  The
reducedness field is proposition-valued, so two records with the same finite
data are definitionally compared independently of which Bézout certificate
proved the invariant. -/
structure Rational where
  num : Int
  den : Nat
  den_pos : 0 < den
  reduced : Reduced num.natAbs den
deriving DecidableEq

/-- Forget the reducedness certificate while retaining the displayed data. -/
def Rational.toRaw (fraction : Rational) : RawFraction :=
  ⟨fraction.num, fraction.den, fraction.den_pos⟩

/-- Exact absolute-value accounting for division by a displayed natural
factor. -/
theorem natAbs_ediv_of_dvd {num : Int} {divisor : Nat}
    (positive : 0 < divisor) (dvd : divisor ∣ num.natAbs) :
    (num / (divisor : Int)).natAbs = num.natAbs / divisor := by
  have integerDvd : (divisor : Int) ∣ num := by
    rw [← Int.dvd_natAbs, Int.ofNat_dvd]
    exact dvd
  rcases integerDvd with ⟨factor, factorization⟩
  have divisorCastNonzero : (divisor : Int) ≠ 0 := by
    intro zero
    have divisorZero : divisor = 0 := Int.ofNat.inj zero
    exact (Nat.ne_of_gt positive) divisorZero
  rw [factorization, Int.mul_ediv_cancel_left factor divisorCastNonzero,
    Int.natAbs_mul, Int.natAbs_natCast,
    Nat.mul_div_cancel_left _ positive]

/-- Executable gcd normalization of a displayed positive-denominator
fraction. -/
def normalize (fraction : RawFraction) : Rational := by
  let result := CanonicalGCD.compute fraction.num.natAbs fraction.den
  have specification :=
    CanonicalGCD.compute_spec fraction.num.natAbs fraction.den
  have divisorPositive : 0 < result.gcd :=
    CanonicalGCD.compute_gcd_positive_right fraction.num.natAbs
      fraction.den_pos
  have divisorNumerator : result.gcd ∣ fraction.num.natAbs :=
    specification.2.1
  have divisorDenominator : result.gcd ∣ fraction.den :=
    specification.2.2
  have divisorAtMostDenominator : result.gcd ≤ fraction.den :=
    Nat.le_of_dvd fraction.den_pos divisorDenominator
  have quotientCertificate :=
    CanonicalGCD.quotientCoprimeCertificate fraction.num.natAbs
      fraction.den_pos
  refine
    ⟨fraction.num / (result.gcd : Int), fraction.den / result.gcd,
      Nat.div_pos divisorAtMostDenominator divisorPositive, ?_⟩
  rw [natAbs_ediv_of_dvd divisorPositive divisorNumerator]
  exact ⟨quotientCertificate⟩

/-- The concrete Bézout certificate produced by normalization.  This is kept
separate from `Rational.reduced`: reducedness is proposition-valued so that
the choice of valid coefficients cannot affect structural rational equality,
while callers which need a checkable certificate can still obtain the exact
coefficients computed by the Euclidean algorithm. -/
def normalizeCertificate (fraction : RawFraction) :
    CanonicalGCD.CoprimeCertificate
      (normalize fraction).num.natAbs (normalize fraction).den := by
  let result := CanonicalGCD.compute fraction.num.natAbs fraction.den
  have specification :=
    CanonicalGCD.compute_spec fraction.num.natAbs fraction.den
  have divisorPositive : 0 < result.gcd :=
    CanonicalGCD.compute_gcd_positive_right fraction.num.natAbs
      fraction.den_pos
  have divisorNumerator : result.gcd ∣ fraction.num.natAbs :=
    specification.2.1
  have quotientCertificate :=
    CanonicalGCD.quotientCoprimeCertificate fraction.num.natAbs
      fraction.den_pos
  change CanonicalGCD.CoprimeCertificate
    (fraction.num / (result.gcd : Int)).natAbs
    (fraction.den / result.gcd)
  rw [natAbs_ediv_of_dvd divisorPositive divisorNumerator]
  exact quotientCertificate

@[ext] theorem Rational.ext {left right : Rational}
    (numerator : left.num = right.num)
    (denominator : left.den = right.den) : left = right := by
  cases left
  cases right
  simp_all

/-- Coprime positive-denominator records with the same cross-product are the
same finite record. -/
theorem eq_of_cross {left right : Rational}
    (cross : left.num * (right.den : Int) =
      right.num * (left.den : Int)) : left = right := by
  have absoluteCross : left.num.natAbs * right.den =
      right.num.natAbs * left.den := by
    have absolute := congrArg Int.natAbs cross
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using absolute
  rcases left.reduced with ⟨leftCertificate⟩
  rcases right.reduced with ⟨rightCertificate⟩
  have leftDvdRight : left.num.natAbs ∣ right.num.natAbs :=
    leftCertificate.dvd_of_dvd_mul_right
      ⟨right.den, absoluteCross.symm⟩
  have rightDvdLeft : right.num.natAbs ∣ left.num.natAbs :=
    rightCertificate.dvd_of_dvd_mul_right
      ⟨left.den, absoluteCross⟩
  have absoluteEqual : left.num.natAbs = right.num.natAbs :=
    Nat.dvd_antisymm leftDvdRight rightDvdLeft
  have denominatorEqual : left.den = right.den := by
    by_cases numeratorZero : left.num.natAbs = 0
    · have leftOne : left.den = 1 :=
        leftCertificate.right_eq_one_of_left_eq_zero numeratorZero
      have rightZero : right.num.natAbs = 0 :=
        absoluteEqual.symm.trans numeratorZero
      have rightOne : right.den = 1 :=
        rightCertificate.right_eq_one_of_left_eq_zero rightZero
      exact leftOne.trans rightOne.symm
    · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero numeratorZero)
      simpa only [absoluteEqual] using absoluteCross.symm
  have numeratorEqual : left.num = right.num := by
    have denominatorCastNonzero : (left.den : Int) ≠ 0 := by
      intro zero
      have denominatorZero : left.den = 0 := Int.ofNat.inj zero
      exact (Nat.ne_of_gt left.den_pos) denominatorZero
    apply Int.eq_of_mul_eq_mul_right denominatorCastNonzero
    simpa only [denominatorEqual] using cross
  exact Rational.ext numeratorEqual denominatorEqual

/-- Gcd normalization preserves the displayed fraction by an explicit common
factor calculation. -/
theorem normalize_equivalent (fraction : RawFraction) :
    Equivalent (normalize fraction).toRaw fraction := by
  let result := CanonicalGCD.compute fraction.num.natAbs fraction.den
  have specification :=
    CanonicalGCD.compute_spec fraction.num.natAbs fraction.den
  have divisorNumerator : (result.gcd : Int) ∣ fraction.num := by
    rw [← Int.dvd_natAbs, Int.ofNat_dvd]
    exact specification.2.1
  have numeratorFactor :
      fraction.num / (result.gcd : Int) * (result.gcd : Int) = fraction.num :=
    Int.ediv_mul_cancel divisorNumerator
  have denominatorFactorNat :
      fraction.den / result.gcd * result.gcd = fraction.den :=
    Nat.div_mul_cancel specification.2.2
  have denominatorFactor :
      ((fraction.den / result.gcd : Nat) : Int) * (result.gcd : Int) =
        (fraction.den : Int) := by
    rw [← Int.natCast_mul, denominatorFactorNat]
  change
    fraction.num / (result.gcd : Int) * (fraction.den : Int) =
      fraction.num * ((fraction.den / result.gcd : Nat) : Int)
  calc
    fraction.num / (result.gcd : Int) * (fraction.den : Int) =
        fraction.num / (result.gcd : Int) *
          (((fraction.den / result.gcd : Nat) : Int) *
            (result.gcd : Int)) := by
            rw [denominatorFactor]
    _ = (fraction.num / (result.gcd : Int) * (result.gcd : Int)) *
        ((fraction.den / result.gcd : Nat) : Int) := by
          rw [mul_comm ((fraction.den / result.gcd : Nat) : Int)
            (result.gcd : Int)]
          exact (mul_assoc _ _ _).symm
    _ = fraction.num * ((fraction.den / result.gcd : Nat) : Int) := by
      rw [numeratorFactor]

/-- Equivalent raw displays normalize to the same canonical record. -/
theorem normalize_respects {left right : RawFraction}
    (equivalent : Equivalent left right) :
    normalize left = normalize right := by
  apply eq_of_cross
  have first : Equivalent (normalize left).toRaw right :=
    equivalent_trans (normalize_equivalent left) equivalent
  exact equivalent_trans first (normalize_equivalent right).symm

/-- Normalizing an already canonical record returns that same record. -/
theorem normalize_idempotent (fraction : Rational) :
    normalize fraction.toRaw = fraction := by
  apply eq_of_cross
  simpa only [Equivalent, Rational.toRaw] using
    normalize_equivalent fraction.toRaw

/-- Cross-multiplication equivalence is exactly equality after executable
normalization. -/
theorem equivalent_iff_normalize_eq (left right : RawFraction) :
    Equivalent left right ↔ normalize left = normalize right := by
  constructor
  · exact normalize_respects
  · intro normalizedEqual
    have middle : Equivalent (normalize left).toRaw (normalize right).toRaw := by
      rw [normalizedEqual]
      exact equivalent_refl _
    exact equivalent_trans (normalize_equivalent left).symm
      (equivalent_trans middle (normalize_equivalent right))

/-- The canonical zero record. -/
def zero : Rational :=
  ⟨0, 1, by decide, ⟨⟨0, 1, by decide⟩⟩⟩

@[simp] theorem normalize_zero :
    normalize ⟨0, 1, by decide⟩ = zero := by decide

theorem normalize_six_eighths :
    normalize ⟨6, 8, by decide⟩ =
      (⟨3, 4, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by decide

theorem normalize_negative_six_eighths :
    normalize ⟨-6, 8, by decide⟩ =
      (⟨-3, 4, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by decide

theorem normalize_zero_ninths :
    normalize ⟨0, 9, by decide⟩ = zero := by decide

end RFAP.CanonicalFraction
