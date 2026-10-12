module
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Coprime.Basic
public import Purelib.Data.Nat.GCD.Coprime
import Purelib.Data.Nat.GCD.Extended
public import Purelib.Data.Nat.GCD.Scalar
-- Exposed normalization retains the natural quotient and divisor-bound proofs.
import Purelib.Data.Nat.Division
public import Purelib.Data.Nat.Divisibility
-- Exposed normalization also retains signed quotient and divisor certificates.
public import Purelib.Data.Int.Division
public import Purelib.Data.Int.Divisibility
import Purelib.Data.Int.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Canonical fractions

This module is the quotient-free scalar kernel.  A displayed fraction is
normalized by an executable gcd calculation to a unique positive-denominator
record.  Equality of semantic rationals is therefore ordinary structure
equality, while `Equivalent` remains available as the explicit certificate
relating differently displayed inputs.

The kernel intentionally does not import the downstream
`Purelib.Data.Rat.Fraction.Compatibility` surface.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data
open Purelib.Data.Nat

set_option genInjectivity false in
/-- Retain an integer numerator and a strictly positive natural denominator.

The record stores the exact finite coordinates together with denominator positivity. -/
structure RawFraction where
  /-- The retained signed integer numerator. -/ num : Int
  /-- The retained denominator. -/ den : Nat
  /-- The retained denominator is strictly positive. -/ den_pos : 0 < den
deriving DecidableEq

constructive_injectivity RawFraction

/-- Two positive-denominator displays have equal integer cross-products. -/
def Equivalent (left right : RawFraction) : Prop :=
  left.num * (right.den : Int) = right.num * (left.den : Int)

/-- Decide cross-product equivalence by the displayed integer arithmetic. -/
instance (left right : RawFraction) : Decidable (Equivalent left right) :=
  inferInstanceAs (Decidable
    (left.num * (right.den : Int) = right.num * (left.den : Int)))

/-- Every displayed fraction is cross-product equivalent to itself. -/
theorem equivalent_refl (fraction : RawFraction) :
    Equivalent fraction fraction := rfl

/-- Reverse a displayed cross-product equivalence. -/
theorem equivalent_symm {left right : RawFraction}
    (equivalent : Equivalent left right) : Equivalent right left :=
  equivalent.symm

/-- Cross-multiplication equivalence composes through a positive denominator.

The two retained cross-product equalities give equal products with the
middle denominator. Its positivity makes that integer factor cancellable. -/
theorem equivalent_trans {left middle right : RawFraction}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right := by
  dsimp only [Equivalent] at leftMiddle middleRight ⊢
  have middleDenominatorNonzero : (middle.den : Int) ≠ 0 := by
    intro zero
    have denominatorZero : middle.den = 0 := Int.ofNat.inj zero
    exact (Nat.ne_of_gt middle.den_pos) denominatorZero
  apply Int.Arithmetic.eq_of_mul_eq_mul_left middleDenominatorNonzero
  rw [Int.Arithmetic.mul_comm (middle.den : Int) (left.num * (right.den : Int)),
    Int.Arithmetic.mul_comm (middle.den : Int) (right.num * (left.den : Int))]
  calc
    left.num * (right.den : Int) * (middle.den : Int) =
        left.num * (middle.den : Int) * (right.den : Int) := by
          rw [Int.Arithmetic.mul_assoc, Int.Arithmetic.mul_comm (right.den : Int)
            (middle.den : Int), ← Int.Arithmetic.mul_assoc]
    _ = middle.num * (left.den : Int) * (right.den : Int) := by rw [leftMiddle]
    _ = middle.num * (right.den : Int) * (left.den : Int) := by
      rw [Int.Arithmetic.mul_assoc, Int.Arithmetic.mul_comm (left.den : Int)
        (right.den : Int), ← Int.Arithmetic.mul_assoc]
    _ = right.num * (middle.den : Int) * (left.den : Int) := by rw [middleRight]
    _ = right.num * (left.den : Int) * (middle.den : Int) := by
      rw [Int.Arithmetic.mul_assoc, Int.Arithmetic.mul_comm (middle.den : Int)
        (left.den : Int), ← Int.Arithmetic.mul_assoc]

/-- The numerator magnitude and denominator admit explicit integer Bézout coefficients for one.

The certificate is retained under Nonempty, so reducedness is proof data while the numerator and denominator remain the
executable semantic representation. -/
def Reduced (numeratorMagnitude denominator : Nat) : Prop :=
  Nonempty
    (Coprime.Basic.CoprimeCertificate numeratorMagnitude denominator)

set_option genInjectivity false in
/-- Retain a canonical rational as coprime integer numerator and positive natural denominator.

The record stores the exact finite coordinates together with denominator positivity and proposition-valued reducedness.
-/
structure Rational where
  /-- The retained signed integer numerator. -/ num : Int
  /-- The retained denominator. -/ den : Nat
  /-- The retained denominator is strictly positive. -/ den_pos : 0 < den
  /-- Explicit Bézout coefficients witness coprimality of numerator magnitude and denominator. -/ reduced : Reduced
    num.natAbs den
deriving DecidableEq

constructive_injectivity Rational

/-- Forget only reducedness, retaining the exact integer numerator, natural denominator and positivity proof. -/
def Rational.toRaw (fraction : Rational) : RawFraction :=
  ⟨fraction.num, fraction.den, fraction.den_pos⟩

/-- Division by a displayed natural factor preserves its magnitude quotient.

The factor is positive and divides the numerator's magnitude. Its retained
divisibility witness supplies an exact signed quotient, so no remainder is
discarded in either magnitude calculation. -/
theorem natAbs_ediv_of_dvd {num : Int} {divisor : Nat}
    (positive : 0 < divisor) (dvd : divisor ∣ num.natAbs) :
    (num / (divisor : Int)).natAbs = num.natAbs / divisor := by
  have integerDvd : (divisor : Int) ∣ num := Int.Divisibility.of_natAbs dvd
  rcases integerDvd with ⟨factor, factorization⟩
  have divisorCastNonzero : (divisor : Int) ≠ 0 := by
    intro zero
    have divisorZero : divisor = 0 := Int.ofNat.inj zero
    exact (Nat.ne_of_gt positive) divisorZero
  rw [factorization, Int.Division.mul_ediv_cancel_left factor divisorCastNonzero,
    Int.Arithmetic.natAbs_mul, Int.natAbs_natCast,
    Division.mul_div_cancel_left _ positive]

/-- Normalize a positive-denominator display by its executable numerator/denominator gcd.

Divide both coordinates by the retained gcd and use the Euclidean quotient certificate for reducedness. The resulting
record has positive denominator and the same cross-product value. -/
def normalize (fraction : RawFraction) : Rational := by
  let divisor := GCD.Scalar.gcd fraction.num.natAbs fraction.den
  have specification := GCD.Scalar.gcd_dvd fraction.num.natAbs fraction.den
  have divisorPositive : 0 < divisor :=
    GCD.Scalar.gcd_positive_right fraction.num.natAbs fraction.den_pos
  have divisorNumerator : divisor ∣ fraction.num.natAbs := specification.1
  have divisorDenominator : divisor ∣ fraction.den := specification.2
  have divisorAtMostDenominator : divisor ≤ fraction.den :=
    Divisibility.le_of_dvd fraction.den_pos divisorDenominator
  have quotientCertificate :=
    GCD.Coprime.quotientCoprimeCertificate fraction.num.natAbs
      fraction.den_pos
  refine
    ⟨fraction.num / (divisor : Int), fraction.den / divisor,
      Division.div_pos divisorAtMostDenominator divisorPositive, ?_⟩
  rw [natAbs_ediv_of_dvd divisorPositive divisorNumerator]
  dsimp only [divisor]
  rw [GCD.Scalar.gcd_eq_compute]
  exact ⟨quotientCertificate⟩

/-- The concrete Bézout certificate produced by normalization.  This is kept separate from `Rational.reduced`:
reducedness is proposition-valued so that the choice of valid coefficients cannot affect structural rational equality,
while callers which need a checkable certificate can still obtain the exact coefficients computed by the Euclidean
algorithm. -/
def normalizeCertificate (fraction : RawFraction) :
    Coprime.Basic.CoprimeCertificate
      (normalize fraction).num.natAbs (normalize fraction).den := by
  change Coprime.Basic.CoprimeCertificate
    (fraction.num / (GCD.Scalar.gcd fraction.num.natAbs fraction.den : Int)).natAbs
    (fraction.den / GCD.Scalar.gcd fraction.num.natAbs fraction.den)
  rw [GCD.Scalar.gcd_eq_compute]
  let result := GCD.Extended.compute fraction.num.natAbs fraction.den
  have specification :=
    GCD.Extended.compute_spec fraction.num.natAbs fraction.den
  have divisorPositive : 0 < result.gcd :=
    GCD.Extended.compute_gcd_positive_right fraction.num.natAbs
      fraction.den_pos
  have divisorNumerator : result.gcd ∣ fraction.num.natAbs :=
    specification.2.1
  have quotientCertificate :=
    GCD.Coprime.quotientCoprimeCertificate fraction.num.natAbs
      fraction.den_pos
  change Coprime.Basic.CoprimeCertificate
    (fraction.num / (result.gcd : Int)).natAbs
    (fraction.den / result.gcd)
  rw [natAbs_ediv_of_dvd divisorPositive divisorNumerator]
  exact quotientCertificate

/-- Reduced rationals with identical numerator and denominator data are equal. -/
@[ext] theorem Rational.ext {left right : Rational}
    (numerator : left.num = right.num)
    (denominator : left.den = right.den) : left = right := by
  cases left with
  | mk leftNum leftDen leftPositive leftReduced =>
      cases right with
      | mk rightNum rightDen rightPositive rightReduced =>
          change leftNum = rightNum at numerator
          change leftDen = rightDen at denominator
          cases numerator
          cases denominator
          rfl

/-- Coprime positive-denominator records with the same cross-product are the same finite record.

Positive denominators and the two coprimality certificates force equal
denominators from the cross-product equation. The same equation then identifies
the retained integer numerators. -/
theorem eq_of_cross {left right : Rational}
    (cross : left.num * (right.den : Int) =
      right.num * (left.den : Int)) : left = right := by
  have absoluteCross : left.num.natAbs * right.den =
      right.num.natAbs * left.den := by
    have absolute := congrArg Int.natAbs cross
    simpa only [Int.Arithmetic.natAbs_mul, Int.natAbs_natCast] using absolute
  rcases left.reduced with ⟨leftCertificate⟩
  rcases right.reduced with ⟨rightCertificate⟩
  have leftDvdRight : left.num.natAbs ∣ right.num.natAbs :=
    leftCertificate.dvd_of_dvd_mul_right
      ⟨right.den, absoluteCross.symm⟩
  have rightDvdLeft : right.num.natAbs ∣ left.num.natAbs :=
    rightCertificate.dvd_of_dvd_mul_right
      ⟨left.den, absoluteCross⟩
  have absoluteEqual : left.num.natAbs = right.num.natAbs :=
    Divisibility.antisymm leftDvdRight rightDvdLeft
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
    apply Int.Arithmetic.eq_of_mul_eq_mul_left denominatorCastNonzero
    rw [Int.Arithmetic.mul_comm (left.den : Int) left.num,
      Int.Arithmetic.mul_comm (left.den : Int) right.num]
    simpa only [denominatorEqual] using cross
  exact Rational.ext numeratorEqual denominatorEqual

/-- Gcd normalization preserves the original displayed fraction by cross-product equivalence.

The numerator and denominator quotients reconstruct the original coordinates after multiplication by their shared gcd,
so the canonical output represents exactly the input display. -/
theorem normalize_equivalent (fraction : RawFraction) :
    Equivalent (normalize fraction).toRaw fraction := by
  change fraction.num / (GCD.Scalar.gcd fraction.num.natAbs fraction.den : Int) *
      (fraction.den : Int) =
    fraction.num * ((fraction.den / GCD.Scalar.gcd fraction.num.natAbs fraction.den : Nat) : Int)
  rw [GCD.Scalar.gcd_eq_compute]
  let result := GCD.Extended.compute fraction.num.natAbs fraction.den
  have specification :=
    GCD.Extended.compute_spec fraction.num.natAbs fraction.den
  have divisorNumerator : (result.gcd : Int) ∣ fraction.num :=
    Int.Divisibility.of_natAbs specification.2.1
  have numeratorFactor :
      fraction.num / (result.gcd : Int) * (result.gcd : Int) = fraction.num :=
    Int.Division.ediv_mul_cancel divisorNumerator
  have denominatorFactorNat :
      fraction.den / result.gcd * result.gcd = fraction.den :=
    Division.div_mul_cancel specification.2.2
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
          rw [Int.Arithmetic.mul_comm ((fraction.den / result.gcd : Nat) : Int)
            (result.gcd : Int)]
          exact (Int.Arithmetic.mul_assoc _ _ _).symm
    _ = fraction.num * ((fraction.den / result.gcd : Nat) : Int) := by
      rw [numeratorFactor]

/-- Equivalent raw displays normalize to the same canonical reduced record. -/
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

/-- Cross-multiplication equivalence is exactly equality after executable normalization. -/
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

/-- The canonical zero fraction with denominator one and its retained Bézout certificate. -/
def zero : Rational :=
  ⟨0, 1, by decide, ⟨⟨0, 1, by decide⟩⟩⟩

/-- Normalizing the zero-over-one display returns canonical zero. -/
@[simp] theorem normalize_zero :
    normalize ⟨0, 1, by decide⟩ = zero := by decide

/-- Normalizing six eighths returns the canonical three-quarters record. -/
theorem normalize_six_eighths :
    normalize ⟨6, 8, by decide⟩ =
      (⟨3, 4, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by decide

/-- Normalizing negative six eighths returns canonical negative three quarters. -/
theorem normalize_negative_six_eighths :
    normalize ⟨-6, 8, by decide⟩ =
      (⟨-3, 4, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by decide

/-- Normalizing zero ninths returns canonical zero. -/
theorem normalize_zero_ninths :
    normalize ⟨0, 9, by decide⟩ = zero := by decide

end Purelib.Data.Rat.Fraction

end
