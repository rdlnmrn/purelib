import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Stars.OrderSeven
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Example 14.10

The rational exclusion is the finite Eisenstein-at-seven argument applied to
the computable gcd-reduced numerator and denominator.  The three decimal
displays are retained as exact rational sign-change brackets; no completed
decimal field, real root, or limit object is introduced.
-/

namespace DivineProportions

namespace ChapterFourteenExamples.ExampleFourteenTen

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- Divisibility of a displayed natural cube by seven forces divisibility of
its base.  The seven possible remainders are the complete finite proof. -/
private theorem seven_dvd_of_seven_dvd_cube {value : Nat}
    (divides : 7 ∣ value * value * value) : 7 ∣ value := by
  rw [Nat.dvd_iff_mod_eq_zero] at divides ⊢
  have remainderLt : value % 7 < 7 := Nat.mod_lt value (by decide)
  have cubeRemainder :
      value * value * value % 7 =
        (value % 7) * (value % 7) * (value % 7) % 7 := by
    simp only [Nat.mul_mod, Nat.mod_mod]
  rw [cubeRemainder] at divides
  have cases :
      value % 7 = 0 ∨ value % 7 = 1 ∨ value % 7 = 2 ∨
        value % 7 = 3 ∨ value % 7 = 4 ∨ value % 7 = 5 ∨
          value % 7 = 6 := by
    omega0
  rcases cases with zero | one | two | three | four | five | six <;>
    simp_all

/-- The rational clause of Example 14.10: the displayed cubic has no
constructive-rational root.  Its reversed polynomial is Eisenstein at seven;
the proof below spells out that finite numerator/denominator argument. -/
theorem cubic_has_no_rational_root (value : Rational) :
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 ≠ 0 := by
  intro cubicZero
  let reduced := RFAP.ConstructiveFraction.representative value
  let numerator := reduced.num
  let denominator := reduced.den
  have clearDenominator :
      value * (denominator : Rational) = (numerator : Rational) := by
    exact RFAP.ConstructiveFraction.representative_mul_den value
  have clearedRational :
      7 * (denominator : Rational) ^ 3 -
          56 * (numerator : Rational) * (denominator : Rational) ^ 2 +
          112 * (numerator : Rational) ^ 2 * (denominator : Rational) -
          64 * (numerator : Rational) ^ 3 = 0 := by
    calc
      7 * (denominator : Rational) ^ 3 -
            56 * (numerator : Rational) * (denominator : Rational) ^ 2 +
            112 * (numerator : Rational) ^ 2 * (denominator : Rational) -
            64 * (numerator : Rational) ^ 3 =
          (denominator : Rational) ^ 3 *
            (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) := by
        rw [← clearDenominator]
        ring1
      _ = 0 := by rw [cubicZero]; ring1
  have clearedCast :
      ((7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 : Int) : Rational) = (0 : Int) := by
    change
      ((7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 : Int) : Rational) = (0 : Rational)
    simpa only [Int.cast_sub, Int.cast_add, QuotientFreeRing.intCast_mul,
      QuotientFreeRing.intCast_pow,
      Int.cast_natCast, Int.cast_ofNat] using clearedRational
  have integerEquation :
      7 * (denominator : Int) ^ 3 -
          56 * numerator * (denominator : Int) ^ 2 +
          112 * numerator ^ 2 * (denominator : Int) -
          64 * numerator ^ 3 = 0 :=
    RFAP.ConstructiveFraction.intCast_injective_direct clearedCast
  have numeratorCubeDivisibleInt : (7 : Int) ∣ numerator ^ 3 := by
    let quotient :=
      (denominator : Int) ^ 3 -
        8 * numerator * (denominator : Int) ^ 2 +
        16 * numerator ^ 2 * (denominator : Int) -
        9 * numerator ^ 3
    refine ⟨quotient, ?_⟩
    calc
      numerator ^ 3 =
          64 * numerator ^ 3 - 63 * numerator ^ 3 := by ring1
      _ = 7 *
          ((denominator : Int) ^ 3 -
            8 * numerator * (denominator : Int) ^ 2 +
            16 * numerator ^ 2 * (denominator : Int)) -
          63 * numerator ^ 3 := by
        have rearranged :
            64 * numerator ^ 3 =
              7 * ((denominator : Int) ^ 3 -
                8 * numerator * (denominator : Int) ^ 2 +
                16 * numerator ^ 2 * (denominator : Int)) := by
          apply sub_eq_zero.mp
          calc
            64 * numerator ^ 3 -
                7 * ((denominator : Int) ^ 3 -
                  8 * numerator * (denominator : Int) ^ 2 +
                  16 * numerator ^ 2 * (denominator : Int)) =
              -(7 * (denominator : Int) ^ 3 -
                56 * numerator * (denominator : Int) ^ 2 +
                112 * numerator ^ 2 * (denominator : Int) -
                64 * numerator ^ 3) := by ring1
            _ = 0 := by rw [integerEquation]; ring1
        rw [rearranged]
      _ = 7 * quotient := by
        unfold quotient
        ring1
  have numeratorCubeDivisibleNat :
      7 ∣ numerator.natAbs * numerator.natAbs * numerator.natAbs := by
    rcases numeratorCubeDivisibleInt with ⟨factor, factorization⟩
    refine ⟨factor.natAbs, ?_⟩
    have absolute := congrArg Int.natAbs factorization
    simpa only [Int.natAbs_mul, Int.natAbs_pow,
      show Int.natAbs 7 = 7 from rfl, pow_three, Nat.mul_assoc]
      using absolute
  have numeratorDivisibleNat : 7 ∣ numerator.natAbs :=
    seven_dvd_of_seven_dvd_cube numeratorCubeDivisibleNat
  have numeratorDivisibleInt : (7 : Int) ∣ numerator := by
    change ((7 : Nat) : Int) ∣ numerator
    rw [← Int.dvd_natAbs, Int.ofNat_dvd]
    exact numeratorDivisibleNat
  rcases numeratorDivisibleInt with ⟨factor, numeratorFactorization⟩
  have bracketZero :
      (denominator : Int) ^ 3 -
        56 * factor * (denominator : Int) ^ 2 +
        784 * factor ^ 2 * (denominator : Int) -
        3136 * factor ^ 3 = 0 := by
    have sevenTimes :
        7 * ((denominator : Int) ^ 3 -
          56 * factor * (denominator : Int) ^ 2 +
          784 * factor ^ 2 * (denominator : Int) -
          3136 * factor ^ 3) = 0 := by
      calc
        7 * ((denominator : Int) ^ 3 -
            56 * factor * (denominator : Int) ^ 2 +
            784 * factor ^ 2 * (denominator : Int) -
            3136 * factor ^ 3) =
          7 * (denominator : Int) ^ 3 -
            56 * numerator * (denominator : Int) ^ 2 +
            112 * numerator ^ 2 * (denominator : Int) -
            64 * numerator ^ 3 := by
          rw [numeratorFactorization]
          ring1
        _ = 0 := integerEquation
    exact (Int.mul_eq_zero.mp sevenTimes).resolve_left (by decide)
  have denominatorCubeDivisibleInt :
      (7 : Int) ∣ (denominator : Int) ^ 3 := by
    refine ⟨8 * factor * (denominator : Int) ^ 2 -
        112 * factor ^ 2 * (denominator : Int) + 448 * factor ^ 3, ?_⟩
    calc
      (denominator : Int) ^ 3 =
          56 * factor * (denominator : Int) ^ 2 -
            784 * factor ^ 2 * (denominator : Int) +
            3136 * factor ^ 3 := by
        apply sub_eq_zero.mp
        calc
          (denominator : Int) ^ 3 -
              (56 * factor * (denominator : Int) ^ 2 -
                784 * factor ^ 2 * (denominator : Int) +
                3136 * factor ^ 3) =
            (denominator : Int) ^ 3 -
              56 * factor * (denominator : Int) ^ 2 +
              784 * factor ^ 2 * (denominator : Int) -
              3136 * factor ^ 3 := by ring1
          _ = 0 := bracketZero
      _ = 7 * (8 * factor * (denominator : Int) ^ 2 -
          112 * factor ^ 2 * (denominator : Int) + 448 * factor ^ 3) := by
        ring1
  have denominatorCubeDivisibleNat :
      7 ∣ denominator * denominator * denominator := by
    apply Int.ofNat_dvd.mp
    change (7 : Int) ∣
      (denominator : Int) * (denominator : Int) * (denominator : Int)
    simpa only [pow_three, mul_assoc] using denominatorCubeDivisibleInt
  have denominatorDivisible : 7 ∣ denominator :=
    seven_dvd_of_seven_dvd_cube denominatorCubeDivisibleNat
  rcases reduced.reduced with ⟨reducedCertificate⟩
  have absurd : 7 = 1 := reducedCertificate.eq_one_of_dvd
    numeratorDivisibleNat denominatorDivisible
  omega0

private theorem rationalNontrivial : Nontrivial Rational := by
  constructor
  refine ⟨0, 1, ?_⟩
  intro zeroOne
  have twoNonzero : (2 : Rational) ≠ 0 := by decide
  apply twoNonzero
  calc
    (2 : Rational) = 1 + 1 := by ring1
    _ = 0 + 0 := by rw [← zeroOne]
    _ = 0 := by ring1

/-- Consequently no regular order-seven star exists over the constructive
rationals. -/
theorem no_rational_star : ¬ Nonempty (RegularSevenStar Rational) := by
  rintro ⟨star⟩
  have parameters := order_seven_star_parameters
    (K := Rational) (by decide) star
  rcases parameters with ⟨value, _valueNonzero, cubicZero, _spreadSquare⟩
  exact cubic_has_no_rational_root value cubicZero

def cubic (value : Rational) : Rational :=
  7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3

private def displayedFraction (numerator : Int) (denominator : Nat)
    (positive : 0 < denominator) : Rational :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, (denominator : Int), Int.natCast_pos.mpr positive⟩

def firstLower : Rational := displayedFraction 37651 200000 (by decide)
def firstUpper : Rational := displayedFraction 5883 31250 (by decide)
def secondLower : Rational := displayedFraction 30563 50000 (by decide)
def secondUpper : Rational := displayedFraction 611261 1000000 (by decide)
def thirdLower : Rational := displayedFraction 237621 250000 (by decide)
def thirdUpper : Rational := displayedFraction 190097 200000 (by decide)

private def clearedCubic (numerator : Int) (denominator : Nat) : Int :=
  7 * (denominator : Int) ^ 3 -
    56 * numerator * (denominator : Int) ^ 2 +
    112 * numerator ^ 2 * (denominator : Int) - 64 * numerator ^ 3

private theorem displayedFraction_mul_denominator
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    displayedFraction numerator denominator positive * (denominator : Rational) =
      (numerator : Rational) := by
  unfold displayedFraction
  simpa only [Int.cast_natCast] using
    RFAP.ConstructiveFraction.ofFraction_mul_den
      ⟨numerator, (denominator : Int), Int.natCast_pos.mpr positive⟩

private theorem cubic_mul_denominatorCube
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator) :
    cubic (displayedFraction numerator denominator positive) *
        (denominator : Rational) ^ 3 =
      (clearedCubic numerator denominator : Rational) := by
  let point := displayedFraction numerator denominator positive
  have clear : point * (denominator : Rational) = (numerator : Rational) :=
    displayedFraction_mul_denominator numerator denominator positive
  calc
    cubic point * (denominator : Rational) ^ 3 =
        7 * (denominator : Rational) ^ 3 -
          56 * (numerator : Rational) * (denominator : Rational) ^ 2 +
          112 * (numerator : Rational) ^ 2 * (denominator : Rational) -
          64 * (numerator : Rational) ^ 3 := by
      unfold cubic
      rw [← clear]
      ring1
    _ = (clearedCubic numerator denominator : Rational) := by
      unfold clearedCubic
      simp only [Int.cast_sub, Int.cast_add, QuotientFreeRing.intCast_mul,
        QuotientFreeRing.intCast_pow,
        Int.cast_natCast, Int.cast_ofNat]

private theorem cubic_positive
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
    (clearedPositive :
      (0 : Rational) < (clearedCubic numerator denominator : Rational)) :
    0 < cubic (displayedFraction numerator denominator positive) := by
  have productPositive :
      0 < cubic (displayedFraction numerator denominator positive) *
        (denominator : Rational) ^ 3 := by
    rw [cubic_mul_denominatorCube numerator denominator positive]
    exact clearedPositive
  have denominatorPositive :
      0 < (denominator : Rational) ^ 3 :=
    RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.natCast_lt_direct positive) 3
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
    (by simpa only [mul_comm] using productPositive) denominatorPositive.le

private theorem cubic_negative
    (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
    (clearedNegative :
      (clearedCubic numerator denominator : Rational) < 0) :
    cubic (displayedFraction numerator denominator positive) < 0 := by
  have productNegative :
      cubic (displayedFraction numerator denominator positive) *
          (denominator : Rational) ^ 3 < 0 := by
    rw [cubic_mul_denominatorCube numerator denominator positive]
    exact clearedNegative
  have denominatorPositive :
      0 < (denominator : Rational) ^ 3 :=
    RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.natCast_lt_direct positive) 3
  have negatedProductPositive :
      0 < (denominator : Rational) ^ 3 *
        (-cubic (displayedFraction numerator denominator positive)) := by
    calc
      (0 : Rational) <
          -(cubic (displayedFraction numerator denominator positive) *
            (denominator : Rational) ^ 3) := neg_pos.mpr productNegative
      _ = (denominator : Rational) ^ 3 *
          (-cubic (displayedFraction numerator denominator positive)) := by
        ring1
  have negatedPositive :=
    RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      negatedProductPositive denominatorPositive.le
  exact neg_pos.mp negatedPositive

/-- Exact finite evidence behind the three printed decimal approximations:
each displayed millionth-width rational interval has ordered endpoints and
opposite cubic signs. -/
theorem first_rational_bracket :
    firstLower < firstUpper ∧ cubic firstUpper < 0 ∧ 0 < cubic firstLower := by
  refine ⟨by decide, ?_, ?_⟩
  · exact cubic_negative 5883 31250 (by decide) (by
      rw [show clearedCubic 5883 31250 = -567349768 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (-567349768 : Int) < 0 by omega0))
  · exact cubic_positive 37651 200000 (by decide) (by
      rw [show clearedCubic 37651 200000 = 16354851136 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (0 : Int) < 16354851136 by omega0))

theorem second_rational_bracket :
    secondLower < secondUpper ∧ cubic secondLower < 0 ∧
      0 < cubic secondUpper := by
  refine ⟨by decide, ?_, ?_⟩
  · exact cubic_negative 30563 50000 (by decide) (by
      rw [show clearedCubic 30563 50000 = -536067008 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (-536067008 : Int) < 0 by omega0))
  · exact cubic_positive 611261 1000000 (by decide) (by
      rw [show clearedCubic 611261 1000000 = 4895051354816 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (0 : Int) < 4895051354816 by omega0))

theorem third_rational_bracket :
    thirdLower < thirdUpper ∧ cubic thirdUpper < 0 ∧ 0 < cubic thirdLower := by
  refine ⟨by decide, ?_, ?_⟩
  · exact cubic_negative 190097 200000 (by decide) (by
      rw [show clearedCubic 190097 200000 = -74937131072 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (-74937131072 : Int) < 0 by omega0))
  · exact cubic_positive 237621 250000 (by decide) (by
      rw [show clearedCubic 237621 250000 = 112205020096 by
        unfold clearedCubic
        ring1]
      simpa only [Int.cast_zero] using
        RFAP.ConstructiveFraction.intCast_lt_direct
          (show (0 : Int) < 112205020096 by omega0))

end ChapterFourteenExamples.ExampleFourteenTen

end DivineProportions
