module
import Purelib.Data.Int.Division
import Purelib.Data.Int.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Small

import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Divisibility.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.GaussianInt.Divisibility

open Purelib.Data.GaussianInt.Norm

section
public section

/-!
# Finite norm-two Gaussian cosets

This file gives the displayed-coordinate algebra needed for the centered
index-two alternative.  Divisibility is represented by an explicit Gaussian
integer quotient.  For a divisor of quadrance two it is equivalent to even
parity of the sum of the two coordinates; the complementary odd class is
therefore closed under multiplication and two odd classes add to the even
class.  No quotient ring or cardinality argument is used.
-/

namespace Purelib.Data.GaussianInt.Divisibility.NormTwo
open Purelib.Data.GaussianInt

/-- The sum of a Gaussian integer's two coordinates is twice an explicit integer witness.

The witness is the retained half of the original coordinate sum. -/
@[expose] def CoordinateEven (value : Embedding.Integer) : Prop :=
  ∃ half : Int, value.re + value.im = 2 * half

/-- The sum of a Gaussian integer's two coordinates is twice an explicit integer witness
plus one.

The witness retains the integral half before the displayed odd unit. -/
@[expose] def CoordinateOdd (value : Embedding.Integer) : Prop :=
  ∃ half : Int, value.re + value.im = 2 * half + 1

/-- Every Gaussian coordinate sum has an explicit even or odd parity witness.

Euclidean division by two gives the retained half and remainder; the remainder bounds
reduce the result to zero or one. -/
theorem coordinateEven_or_coordinateOdd (value : Embedding.Integer) :
    NormTwo.CoordinateEven value ∨ NormTwo.CoordinateOdd value := by
  let sum := value.re + value.im
  have remainderCast : sum % 2 = Int.ofNat (Int.Division.remNat sum 2) :=
    Int.Division.remNat_cast sum (show 0 < (2 : Nat) by decide)
  have decomposition := Int.Division.ediv_add_remNat sum (show 0 < (2 : Nat) by decide)
  have integerDecomposition : 2 * (sum / 2) + sum % 2 = sum :=
    (congrArg (fun rest : Int => 2 * (sum / 2) + rest) remainderCast).trans decomposition
  have remainderLess := Int.Division.remNat_lt sum (show 0 < (2 : Nat) by decide)
  have remainderCases : sum % 2 = 0 ∨ sum % 2 = 1 := by
    rw [remainderCast]
    by_cases remainderZero : Int.Division.remNat sum 2 = 0
    · exact Or.inl (congrArg Int.ofNat remainderZero)
    · have remainderOne : Int.Division.remNat sum 2 = 1 := by omega0
      exact Or.inr (congrArg Int.ofNat remainderOne)
  rcases remainderCases with remainderZero | remainderOne
  · left
    refine ⟨sum / 2, ?_⟩
    change sum = 2 * (sum / 2)
    calc
      sum = 2 * (sum / 2) + sum % 2 := integerDecomposition.symm
      _ = 2 * (sum / 2) := by rw [remainderZero]; ring1
  · right
    refine ⟨sum / 2, ?_⟩
    change sum = 2 * (sum / 2) + 1
    calc
      sum = 2 * (sum / 2) + sum % 2 := integerDecomposition.symm
      _ = 2 * (sum / 2) + 1 := by rw [remainderOne]

/-- An odd Gaussian coordinate sum cannot also have an even witness. -/
theorem coordinateOdd_not_coordinateEven {value : Embedding.Integer}
    (odd : NormTwo.CoordinateOdd value) : ¬ NormTwo.CoordinateEven value := by
  rintro ⟨evenHalf, evenIdentity⟩
  rcases odd with ⟨oddHalf, oddIdentity⟩
  have incompatible : 2 * evenHalf = 2 * oddHalf + 1 :=
    evenIdentity.symm.trans oddIdentity
  omega0

/-- Failure of even coordinate-sum parity is equivalent to an explicit odd witness. -/
theorem not_coordinateEven_iff_coordinateOdd (value : Embedding.Integer) :
    ¬ NormTwo.CoordinateEven value ↔ NormTwo.CoordinateOdd value := by
  constructor
  · intro notEven
    rcases NormTwo.coordinateEven_or_coordinateOdd value with even | odd
    · exact False.elim (notEven even)
    · exact odd
  · exact NormTwo.coordinateOdd_not_coordinateEven

/-- The product of two Gaussian integers with odd coordinate sums again has odd
coordinate sum. -/
theorem coordinateOdd_mul {left right : Embedding.Integer}
    (leftOdd : NormTwo.CoordinateOdd left) (rightOdd : NormTwo.CoordinateOdd right) :
    NormTwo.CoordinateOdd (left * right) := by
  rcases leftOdd with ⟨leftHalf, leftIdentity⟩
  rcases rightOdd with ⟨rightHalf, rightIdentity⟩
  refine ⟨2 * leftHalf * rightHalf + leftHalf + rightHalf -
    left.im * right.im, ?_⟩
  simp only [-eq_self, -iff_self, GaussianInt.mul_re, GaussianInt.mul_im] at *
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

/-- The sum of two Gaussian integers with odd coordinate sums has even coordinate sum. -/
theorem coordinateOdd_add {left right : Embedding.Integer}
    (leftOdd : NormTwo.CoordinateOdd left) (rightOdd : NormTwo.CoordinateOdd right) :
    NormTwo.CoordinateEven (left + right) := by
  rcases leftOdd with ⟨leftHalf, leftIdentity⟩
  rcases rightOdd with ⟨rightHalf, rightIdentity⟩
  refine ⟨leftHalf + rightHalf + 1, ?_⟩
  simp only [-eq_self, -iff_self, GaussianInt.add_re, GaussianInt.add_im] at *
  calc
    (left.re + right.re) + (left.im + right.im) =
        (left.re + left.im) + (right.re + right.im) := by ring1
    _ = (2 * leftHalf + 1) + (2 * rightHalf + 1) := by
      rw [leftIdentity, rightIdentity]
    _ = 2 * (leftHalf + rightHalf + 1) := by ring1

/-- A Gaussian divisor of quadrance two divides precisely the values with even coordinate
sum.

The four integral coordinate possibilities for the divisor give explicit quotient
witnesses for the even class; multiplication yields the converse parity witness. -/
theorem divides_iff_coordinateEven_of_norm_two
    {divisor value : Embedding.Integer} (divisorNorm : normNat divisor = 2) :
    Basic.Divides divisor value ↔ NormTwo.CoordinateEven value := by
  have diagonal := Small.isDiagonal_of_normNat_eq_two divisorNorm
  rcases diagonal with divisorCase | divisorCase | divisorCase | divisorCase
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨quotient.re, ?_⟩
      have realIdentity := congrArg (fun z : Embedding.Integer => z.re) identity
      have imaginaryIdentity := congrArg (fun z : Embedding.Integer => z.im) identity
      simp only [-eq_self, -iff_self, GaussianInt.mul_re, GaussianInt.mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * quotient.re
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨half, half - value.re⟩, ?_⟩
      apply GaussianInt.ext
      · simp only [-eq_self, -iff_self, GaussianInt.mul_re]
        ring1
      · simp only [-eq_self, -iff_self, GaussianInt.mul_im]
        rw [imaginaryFromEven]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨quotient.im, ?_⟩
      have realIdentity := congrArg (fun z : Embedding.Integer => z.re) identity
      have imaginaryIdentity := congrArg (fun z : Embedding.Integer => z.im) identity
      simp only [-eq_self, -iff_self, GaussianInt.mul_re, GaussianInt.mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * quotient.im
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨value.re - half, half⟩, ?_⟩
      apply GaussianInt.ext
      · simp only [-eq_self, -iff_self, GaussianInt.mul_re]
        ring1
      · simp only [-eq_self, -iff_self, GaussianInt.mul_im]
        rw [imaginaryFromEven]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨-quotient.im, ?_⟩
      have realIdentity := congrArg (fun z : Embedding.Integer => z.re) identity
      have imaginaryIdentity := congrArg (fun z : Embedding.Integer => z.im) identity
      simp only [-eq_self, -iff_self, GaussianInt.mul_re, GaussianInt.mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * (-quotient.im)
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have realFromEven : value.re = 2 * half - value.im := by
        calc
          value.re = (value.re + value.im) - value.im := by ring1
          _ = 2 * half - value.im := by rw [evenIdentity]
      refine ⟨⟨value.im - half, -half⟩, ?_⟩
      apply GaussianInt.ext
      · simp only [-eq_self, -iff_self, GaussianInt.mul_re]
        rw [realFromEven]
        ring1
      · simp only [-eq_self, -iff_self, GaussianInt.mul_im]
        ring1
  · rw [divisorCase]
    constructor
    · rintro ⟨quotient, identity⟩
      refine ⟨-quotient.re, ?_⟩
      have realIdentity := congrArg (fun z : Embedding.Integer => z.re) identity
      have imaginaryIdentity := congrArg (fun z : Embedding.Integer => z.im) identity
      simp only [-eq_self, -iff_self, GaussianInt.mul_re, GaussianInt.mul_im] at realIdentity imaginaryIdentity
      change value.re + value.im = 2 * (-quotient.re)
      rw [realIdentity, imaginaryIdentity]
      ring1
    · rintro ⟨half, evenIdentity⟩
      have imaginaryFromEven : value.im = 2 * half - value.re := by
        calc
          value.im = (value.re + value.im) - value.re := by ring1
          _ = 2 * half - value.re := by rw [evenIdentity]
      refine ⟨⟨-half, value.re - half⟩, ?_⟩
      apply GaussianInt.ext
      · simp only [-eq_self, -iff_self, GaussianInt.mul_re]
        ring1
      · simp only [-eq_self, -iff_self, GaussianInt.mul_im]
        rw [imaginaryFromEven]
        ring1

/-- Nondivisibility by a quadrance-two Gaussian divisor is exactly odd coordinate-sum
parity. -/
theorem not_divides_iff_coordinateOdd_of_norm_two
    {divisor value : Embedding.Integer} (divisorNorm : normNat divisor = 2) :
    ¬ Basic.Divides divisor value ↔ NormTwo.CoordinateOdd value := by
  constructor
  · intro notDivisible
    apply (NormTwo.not_coordinateEven_iff_coordinateOdd value).mp
    intro even
    exact notDivisible ((NormTwo.divides_iff_coordinateEven_of_norm_two divisorNorm).mpr even)
  · intro odd divisible
    exact NormTwo.coordinateOdd_not_coordinateEven odd
      ((NormTwo.divides_iff_coordinateEven_of_norm_two divisorNorm).mp divisible)

/-- Every Gaussian integer of quadrance two divides every other Gaussian integer of
quadrance two. -/
theorem divides_of_norm_two {divisor value : Embedding.Integer}
    (divisorNorm : normNat divisor = 2) (valueNorm : normNat value = 2) :
    Basic.Divides divisor value := by
  apply (NormTwo.divides_iff_coordinateEven_of_norm_two divisorNorm).mpr
  have diagonal := Small.isDiagonal_of_normNat_eq_two valueNorm
  rcases diagonal with valueCase | valueCase | valueCase | valueCase <;>
    rw [valueCase]
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨-1, by decide⟩

/-- A quadrance-two divisor cannot divide the product of two values that it does not
divide.

The two retained nondivisibility hypotheses give odd coordinate sums, whose product
remains in the odd class. -/
theorem not_divides_mul_of_norm_two
    {divisor left right : Embedding.Integer}
    (divisorNorm : normNat divisor = 2)
    (leftNotDivisible : ¬ Basic.Divides divisor left)
    (rightNotDivisible : ¬ Basic.Divides divisor right) :
    ¬ Basic.Divides divisor (left * right) := by
  apply (NormTwo.not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mpr
  exact NormTwo.coordinateOdd_mul
    ((NormTwo.not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      leftNotDivisible)
    ((NormTwo.not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      rightNotDivisible)

/-- Two values not divisible by a fixed quadrance-two divisor have a sum divisible by it. -/
theorem divides_add_of_not_divides_of_norm_two
    {divisor left right : Embedding.Integer}
    (divisorNorm : normNat divisor = 2)
    (leftNotDivisible : ¬ Basic.Divides divisor left)
    (rightNotDivisible : ¬ Basic.Divides divisor right) :
    Basic.Divides divisor (left + right) := by
  apply (NormTwo.divides_iff_coordinateEven_of_norm_two divisorNorm).mpr
  exact NormTwo.coordinateOdd_add
    ((NormTwo.not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      leftNotDivisible)
    ((NormTwo.not_divides_iff_coordinateOdd_of_norm_two divisorNorm).mp
      rightNotDivisible)

end Purelib.Data.GaussianInt.Divisibility.NormTwo

end
