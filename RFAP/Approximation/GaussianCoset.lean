import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzGeometry

/-!
# Finite norm-two Gaussian cosets

This file gives the displayed-coordinate algebra needed for the centered
index-two alternative.  Divisibility is represented by an explicit Gaussian
integer quotient.  For a divisor of quadrance two it is equivalent to even
parity of the sum of the two coordinates; the complementary odd class is
therefore closed under multiplication and two odd classes add to the even
class.  No quotient ring or cardinality argument is used.
-/

namespace RFAP.GaussianCoset

abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- Explicit divisibility in the displayed Gaussian integers. -/
def Divides (divisor value : GaussianInt) : Prop :=
  ∃ quotient : GaussianInt, value = divisor * quotient

/-- The coordinate-sum parity class represented by a displayed witness. -/
def CoordinateEven (value : GaussianInt) : Prop :=
  ∃ half : Int, value.re + value.im = 2 * half

/-- The other coordinate-sum parity class, again with a displayed witness. -/
def CoordinateOdd (value : GaussianInt) : Prop :=
  ∃ half : Int, value.re + value.im = 2 * half + 1

/-- Constructive parity decomposition using the computed Euclidean quotient
and remainder on integers. -/
theorem coordinateEven_or_coordinateOdd (value : GaussianInt) :
    CoordinateEven value ∨ CoordinateOdd value := by
  let sum := value.re + value.im
  have decomposition := Int.ediv_mul_add_emod sum 2
  have remainderNonnegative : 0 ≤ sum % 2 :=
    Int.emod_nonneg sum (by decide)
  have remainderLess : sum % 2 < 2 :=
    Int.emod_lt_of_pos sum (by decide)
  have remainderCases : sum % 2 = 0 ∨ sum % 2 = 1 := by
    by_cases remainderZero : sum % 2 = 0
    · exact Or.inl remainderZero
    · right
      have remainderPositive : 0 < sum % 2 :=
        lt_of_le_of_ne remainderNonnegative (Ne.symm remainderZero)
      have oneLe : (1 : Int) ≤ sum % 2 := by
        exact Int.add_one_le_iff.mpr remainderPositive
      have remainderLeOne : sum % 2 ≤ (1 : Int) := by
        change sum % 2 < (1 : Int) + 1 at remainderLess
        exact Int.le_of_lt_add_one remainderLess
      exact Int.le_antisymm remainderLeOne oneLe
  rcases remainderCases with remainderZero | remainderOne
  · left
    refine ⟨sum / 2, ?_⟩
    change sum = 2 * (sum / 2)
    calc
      sum = sum / 2 * 2 + sum % 2 := decomposition.symm
      _ = 2 * (sum / 2) := by rw [remainderZero]; ring1
  · right
    refine ⟨sum / 2, ?_⟩
    change sum = 2 * (sum / 2) + 1
    calc
      sum = sum / 2 * 2 + sum % 2 := decomposition.symm
      _ = 2 * (sum / 2) + 1 := by rw [remainderOne]; ring1

theorem coordinateOdd_not_coordinateEven {value : GaussianInt}
    (odd : CoordinateOdd value) : ¬ CoordinateEven value := by
  rintro ⟨evenHalf, evenIdentity⟩
  rcases odd with ⟨oddHalf, oddIdentity⟩
  have incompatible : 2 * evenHalf = 2 * oddHalf + 1 :=
    evenIdentity.symm.trans oddIdentity
  by_cases ordered : evenHalf ≤ oddHalf
  · have doubled := Int.mul_le_mul_of_nonneg_left ordered
      (show (0 : Int) ≤ 2 by decide)
    have strict : 2 * evenHalf < 2 * oddHalf + 1 :=
      doubled.trans_lt (Int.lt_add_one_iff.mpr (Int.le_refl _))
    rw [incompatible] at strict
    exact (Int.lt_irrefl _ strict).elim
  · have strict : oddHalf < evenHalf := Int.lt_of_not_ge ordered
    have nextLe : oddHalf + 1 ≤ evenHalf := Int.add_one_le_iff.mpr strict
    have doubled := Int.mul_le_mul_of_nonneg_left nextLe
      (show (0 : Int) ≤ 2 by decide)
    have impossible : 2 * oddHalf + 2 ≤ 2 * oddHalf + 1 := by
      calc
        2 * oddHalf + 2 = 2 * (oddHalf + 1) := by ring1
        _ ≤ 2 * evenHalf := doubled
        _ = 2 * oddHalf + 1 := incompatible
    have successorStrict : 2 * oddHalf + 1 < 2 * oddHalf + 2 := by
      calc
        2 * oddHalf + 1 < (2 * oddHalf + 1) + 1 :=
          Int.lt_add_one_iff.mpr (Int.le_refl _)
        _ = 2 * oddHalf + 2 := by ring1
    exact (not_lt_of_ge impossible successorStrict).elim

theorem not_coordinateEven_iff_coordinateOdd (value : GaussianInt) :
    ¬ CoordinateEven value ↔ CoordinateOdd value := by
  constructor
  · intro notEven
    rcases coordinateEven_or_coordinateOdd value with even | odd
    · exact False.elim (notEven even)
    · exact odd
  · exact coordinateOdd_not_coordinateEven

theorem coordinateOdd_mul {left right : GaussianInt}
    (leftOdd : CoordinateOdd left) (rightOdd : CoordinateOdd right) :
    CoordinateOdd (left * right) := by
  rcases leftOdd with ⟨leftHalf, leftIdentity⟩
  rcases rightOdd with ⟨rightHalf, rightIdentity⟩
  refine ⟨2 * leftHalf * rightHalf + leftHalf + rightHalf -
    left.im * right.im, ?_⟩
  simp only [mul_re, mul_im] at *
  calc
    (left.re * right.re - left.im * right.im) +
        (left.re * right.im + left.im * right.re) =
      (left.re + left.im) * (right.re + right.im) -
        2 * (left.im * right.im) := by ring1
    _ = (2 * leftHalf + 1) * (2 * rightHalf + 1) -
        2 * (left.im * right.im) := by rw [leftIdentity, rightIdentity]
    _ = 2 *
        (2 * leftHalf * rightHalf + leftHalf + rightHalf -
          left.im * right.im) + 1 := by ring1

theorem coordinateOdd_add {left right : GaussianInt}
    (leftOdd : CoordinateOdd left) (rightOdd : CoordinateOdd right) :
    CoordinateEven (left + right) := by
  rcases leftOdd with ⟨leftHalf, leftIdentity⟩
  rcases rightOdd with ⟨rightHalf, rightIdentity⟩
  refine ⟨leftHalf + rightHalf + 1, ?_⟩
  simp only [add_re, add_im] at *
  calc
    (left.re + right.re) + (left.im + right.im) =
        (left.re + left.im) + (right.re + right.im) := by ring1
    _ = (2 * leftHalf + 1) + (2 * rightHalf + 1) := by
      rw [leftIdentity, rightIdentity]
    _ = 2 * (leftHalf + rightHalf + 1) := by ring1

/-- A quadrance-two Gaussian integer divides exactly the coordinate pairs
whose coordinate sum is even. -/
theorem divides_iff_coordinateEven_of_norm_two
    {divisor value : GaussianInt} (divisorNorm : normNat divisor = 2) :
    Divides divisor value ↔ CoordinateEven value := by
  have diagonal := RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two divisorNorm
  rcases diagonal with divisorCase | divisorCase | divisorCase | divisorCase
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨quotient.re, ?_⟩
      have realIdentity := congrArg (fun z : GaussianInt => z.re) identity
      have imaginaryIdentity := congrArg (fun z : GaussianInt => z.im) identity
      simp only [mul_re, mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * quotient.re
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨half, half - value.re⟩, ?_⟩
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
      · simp only [mul_re]
        ring1
      · simp only [mul_im]
        rw [imaginaryFromEven]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨quotient.im, ?_⟩
      have realIdentity := congrArg (fun z : GaussianInt => z.re) identity
      have imaginaryIdentity := congrArg (fun z : GaussianInt => z.im) identity
      simp only [mul_re, mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * quotient.im
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨value.re - half, half⟩, ?_⟩
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
      · simp only [mul_re]
        ring1
      · simp only [mul_im]
        rw [imaginaryFromEven]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨-quotient.im, ?_⟩
      have realIdentity := congrArg (fun z : GaussianInt => z.re) identity
      have imaginaryIdentity := congrArg (fun z : GaussianInt => z.im) identity
      simp only [mul_re, mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * (-quotient.im)
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have realFromEven : value.re = 2 * half - value.im := by
        calc
          value.re = (value.re + value.im) - value.im := by ring1
          _ = 2 * half - value.im := by rw [evenIdentity]
      refine ⟨⟨value.im - half, -half⟩, ?_⟩
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
      · simp only [mul_re]
        rw [realFromEven]
        ring1
      · simp only [mul_im]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨-quotient.re, ?_⟩
      have realIdentity := congrArg (fun z : GaussianInt => z.re) identity
      have imaginaryIdentity := congrArg (fun z : GaussianInt => z.im) identity
      simp only [mul_re, mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * (-quotient.re)
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨-half, value.re - half⟩, ?_⟩
      apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext
      · simp only [mul_re]
        ring1
      · simp only [mul_im]
        rw [imaginaryFromEven]
        ring1

theorem not_divides_iff_coordinateOdd_of_norm_two
    {divisor value : GaussianInt} (divisorNorm : normNat divisor = 2) :
    ¬ Divides divisor value ↔ CoordinateOdd value := by
  rw [divides_iff_coordinateEven_of_norm_two divisorNorm,
    not_coordinateEven_iff_coordinateOdd]

/-- Any quadrance-two Gaussian integer divides every other quadrance-two
Gaussian integer.  In coordinate language all four diagonal elements lie in
the even class. -/
theorem divides_of_norm_two {divisor value : GaussianInt}
    (divisorNorm : normNat divisor = 2) (valueNorm : normNat value = 2) :
    Divides divisor value := by
  apply (divides_iff_coordinateEven_of_norm_two divisorNorm).mpr
  have diagonal := RFAP.HurwitzGeometry.isDiagonal_of_normNat_eq_two valueNorm
  rcases diagonal with valueCase | valueCase | valueCase | valueCase <;>
    rw [valueCase]
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨-1, by decide⟩

/-- A nonzero Gaussian integer strictly smaller in quadrance than a divisor
cannot be divisible by it. -/
theorem not_divides_of_norm_lt {divisor value : GaussianInt}
    (valueNonzero : value ≠ 0)
    (normSmaller : normNat value < normNat divisor) :
    ¬ Divides divisor value := by
  rintro ⟨quotient, identity⟩
  have quotientNonzero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_zero] at identity
    exact valueNonzero identity
  have quotientNormPositive := normNat_pos quotientNonzero
  have normIdentity := congrArg normNat identity
  rw [normNat_mul] at normIdentity
  have divisorNormLeValueNorm : normNat divisor ≤ normNat value := by
    calc
      normNat divisor = normNat divisor * 1 := (Nat.mul_one _).symm
      _ ≤ normNat divisor * normNat quotient :=
        Nat.mul_le_mul_left _ quotientNormPositive
      _ = normNat value := normIdentity.symm
  exact (Nat.not_le_of_gt normSmaller) divisorNormLeValueNorm

/-- Direct cancellation in the displayed Gaussian integers, proved by taking
the multiplicative natural norm rather than by importing an abstract-domain
cancellation route. -/
theorem mul_right_cancel_of_nonzero {left right factor : GaussianInt}
    (factorNonzero : factor ≠ 0)
    (identity : left * factor = right * factor) : left = right := by
  have productZero : (left - right) * factor = 0 := by
    calc
      (left - right) * factor = left * factor - right * factor := by
        apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
          simp only [RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
          ring1
      _ = 0 := sub_eq_zero.mpr identity
  have normZero := congrArg normNat productZero
  rw [normNat_mul] at normZero
  have zeroNorm : normNat (0 : GaussianInt) = 0 := rfl
  rw [zeroNorm] at normZero
  have factorNormPositive := normNat_pos factorNonzero
  have differenceNormZero : normNat (left - right) = 0 := by
    rcases Nat.mul_eq_zero.mp normZero with differenceZero | factorZero
    · exact differenceZero
    · exact False.elim ((Nat.ne_of_gt factorNormPositive) factorZero)
  have differenceZero :=
    RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero differenceNormZero
  exact sub_eq_zero.mp differenceZero

/-- The nonzero residue class modulo a quadrance-two Gaussian integer is
multiplicatively closed.  This is the only prime-like fact needed for the
centered-coset argument. -/
theorem not_divides_mul_of_norm_two
    {divisor left right : GaussianInt}
    (divisorNorm : normNat divisor = 2)
    (leftNotDivisible : ¬ Divides divisor left)
    (rightNotDivisible : ¬ Divides divisor right) :
    ¬ Divides divisor (left * right) := by
  apply (not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mpr
  exact coordinateOdd_mul
    ((not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      leftNotDivisible)
    ((not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      rightNotDivisible)

/-- Two representatives of the nonzero class add into the divisible class. -/
theorem divides_add_of_not_divides_of_norm_two
    {divisor left right : GaussianInt}
    (divisorNorm : normNat divisor = 2)
    (leftNotDivisible : ¬ Divides divisor left)
    (rightNotDivisible : ¬ Divides divisor right) :
    Divides divisor (left + right) := by
  apply (divides_iff_coordinateEven_of_norm_two divisorNorm).mpr
  exact coordinateOdd_add
    ((not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      leftNotDivisible)
    ((not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      rightNotDivisible)

end RFAP.GaussianCoset
