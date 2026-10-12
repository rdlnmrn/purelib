module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Square
import Mathlib.Algebra.Ring.MinimalAxioms
import Purelib.Algebra.Ring.Multiplication
import Purelib.Algebra.Group.Negation
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Basic
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic

open Purelib.Data

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Compute Gaussian quadrance as the sum of the two exact rational coordinate squares.

The result is an exact canonical rational; no square root or completed scalar carrier
is introduced. -/
@[expose] def normSq (source : Canonical) : Fraction.Rational :=
  source.re * source.re + source.im * source.im

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The squared norm of Gaussian zero is zero. -/
@[simp] theorem normSq_zero : normSq 0 = 0 := by
  change (0 : Fraction.Rational) * 0 + 0 * 0 = 0
  rw [Field.zero_mul_direct, Fraction.zero_add]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- The squared norm of Gaussian one is one. -/
@[simp] theorem normSq_one : normSq 1 = 1 := by
  change (1 : Fraction.Rational) * 1 + 0 * 0 = 1
  rw [Fraction.one_mul, Field.zero_mul_direct, _root_.add_zero]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Algebra

/-- Negating a canonical Gaussian pair preserves its squared norm.

Each displayed coordinate product has both factors negated, so both
real and imaginary squares retain their original scalar values. -/
@[simp] theorem normSq_neg (source : Canonical) :
    normSq (-source) = normSq source := by
  change (-source.re) * (-source.re) + (-source.im) * (-source.im) =
    source.re * source.re + source.im * source.im
  rw [Ring.Multiplication.neg_mul_neg, Ring.Multiplication.neg_mul_neg]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Data Purelib.Data.Rat

/-- The squared norm of a canonical Gaussian pair is nonnegative.

Both retained coordinate squares have nonnegative integer numerators. Their
positive-denominator addition display retains that sign through normalization. -/
theorem normSq_nonneg (source : Canonical) : 0 ≤ normSq source :=
  by
  apply (Fraction.Order.Square.zero_le_iff_num_nonneg _).mpr
  let realSquare := source.re * source.re
  let imaginarySquare := source.im * source.im
  have realNonnegative : 0 ≤ realSquare :=
    Fraction.Order.Square.mul_self_nonneg source.re
  have imaginaryNonnegative : 0 ≤ imaginarySquare :=
    Fraction.Order.Square.mul_self_nonneg source.im
  have realNumeratorNonnegative : 0 ≤ realSquare.num :=
    (Fraction.Order.Square.zero_le_iff_num_nonneg realSquare).mp
      realNonnegative
  have imaginaryNumeratorNonnegative : 0 ≤ imaginarySquare.num :=
    (Fraction.Order.Square.zero_le_iff_num_nonneg imaginarySquare).mp
      imaginaryNonnegative
  have display := Fraction.add_equivalent
    realSquare imaginarySquare
  have displayNumeratorNonnegative :
      0 ≤ (Fraction.referenceAddRaw
        realSquare imaginarySquare).num := by
    change
      0 ≤ realSquare.num * (imaginarySquare.den : Int) +
        imaginarySquare.num * (realSquare.den : Int)
    exact Int.Order.add_nonneg
      (Int.Order.mul_nonneg realNumeratorNonnegative (Int.natCast_nonneg _))
      (Int.Order.mul_nonneg imaginaryNumeratorNonnegative (Int.natCast_nonneg _))
  change 0 ≤ (realSquare + imaginarySquare).num
  by_cases sumNumeratorZero :
      (realSquare + imaginarySquare).num = 0
  · exact Eq.ndrec (motive := fun value : Int => 0 ≤ value)
      (Int.Order.le_refl 0) sumNumeratorZero.symm
  · exact Int.Order.le_of_lt
      ((Fraction.Order.Basic.numerator_pos_iff_of_equivalent display).mpr
        (Int.Order.lt_of_le_of_ne displayNumeratorNonnegative
          (fun displayZero => sumNumeratorZero
            ((Fraction.numerator_zero_iff_of_equivalent display).mpr
              displayZero.symm))))

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

open Purelib.Data Purelib.Data.Rat

/-- A zero sum of two nonnegative canonical rationals has both addends zero.

The retained addition display has a zero numerator. Its nonnegative integer
terms must vanish, and each retained positive denominator excludes a zero factor. -/
private theorem nonnegative_addends_of_zero
    {left right : Fraction.Rational}
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right)
    (sumZero : left + right = 0) : left = 0 ∧ right = 0 := by
  have sumNumeratorZero : (left + right).num = 0 :=
    (Fraction.eq_zero_iff_num_zero (left + right)).mp sumZero
  have display := Fraction.add_equivalent left right
  have rawNumeratorZero :
      (Fraction.referenceAddRaw left right).num = 0 :=
    (Fraction.numerator_zero_iff_of_equivalent display).mp
      sumNumeratorZero
  change
    left.num * (right.den : Int) + right.num * (left.den : Int) = 0
      at rawNumeratorZero
  have leftNumeratorNonnegative : 0 ≤ left.num :=
    (Fraction.Order.Square.zero_le_iff_num_nonneg left).mp leftNonnegative
  have rightNumeratorNonnegative : 0 ≤ right.num :=
    (Fraction.Order.Square.zero_le_iff_num_nonneg right).mp rightNonnegative
  have termsZero := Int.Order.eq_zero_of_add_nonneg_eq_zero
    (Int.Order.mul_nonneg leftNumeratorNonnegative (Int.natCast_nonneg _))
    (Int.Order.mul_nonneg rightNumeratorNonnegative (Int.natCast_nonneg _))
    rawNumeratorZero
  have leftDenominatorNonzero : (left.den : Int) ≠ 0 := by
    intro denominatorZero
    have positive := left.den_pos
    rw [Int.ofNat.inj denominatorZero] at positive
    exact Nat.not_lt_zero _ positive
  have rightDenominatorNonzero : (right.den : Int) ≠ 0 := by
    intro denominatorZero
    have positive := right.den_pos
    rw [Int.ofNat.inj denominatorZero] at positive
    exact Nat.not_lt_zero _ positive
  have leftNumeratorZero : left.num = 0 := by
    cases Int.Arithmetic.eq_zero_of_mul_eq_zero termsZero.1 with
    | inl numeratorZero => exact numeratorZero
    | inr denominatorZero => exact (rightDenominatorNonzero denominatorZero).elim
  have rightNumeratorZero : right.num = 0 := by
    cases Int.Arithmetic.eq_zero_of_mul_eq_zero termsZero.2 with
    | inl numeratorZero => exact numeratorZero
    | inr denominatorZero => exact (leftDenominatorNonzero denominatorZero).elim
  exact
    ⟨(Fraction.eq_zero_iff_num_zero left).mpr leftNumeratorZero,
      (Fraction.eq_zero_iff_num_zero right).mpr
        rightNumeratorZero⟩

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- A Gaussian rational has zero squared norm exactly when both its coordinates are zero.

Nonnegativity forces both retained coordinate squares to vanish. Conversely the
structural zero pair has zero quadrance by direct coordinate computation. -/
theorem normSq_eq_zero (source : Canonical) : normSq source = 0 ↔
  source = 0 := by
  constructor
  · intro normZero
    have squaresZero := nonnegative_addends_of_zero
      (Square.mul_self_nonneg source.re)
      (Square.mul_self_nonneg source.im) normZero
    have realZero :=
      (Square.mul_self_eq_zero source.re).mp squaresZero.1
    have imaginaryZero :=
      (Square.mul_self_eq_zero source.im).mp squaresZero.2
    exact Canonical.ext realZero imaginaryZero
  · intro sourceZero
    rw [sourceZero]
    change (0 : Fraction.Rational) * 0 + 0 * 0 = 0
    ring1

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- A Gaussian pair times its conjugate is its squared norm with zero imaginary part.

The real product is the sum of the two coordinate squares, and the signed
imaginary terms cancel using the original scalar product. -/
theorem mul_conj (source : Canonical) :
    source * Canonical.conj source = ⟨normSq source, 0⟩ := by
  apply Canonical.ext
  · change source.re * source.re - source.im * (-source.im) =
      source.re * source.re + source.im * source.im
    rw [Arithmetic.sub_eq_add_neg_direct, _root_.mul_neg,
      _root_.neg_neg]
  · change source.re * (-source.im) + source.im * source.re = 0
    rw [_root_.mul_neg, Fraction.mul_comm source.im source.re]
    exact Fraction.neg_add_cancel (source.re * source.im)

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Basic.Canonical
section Canonical

/-- Gaussian squared norm preserves multiplication. -/
theorem normSq_mul (left right : Canonical) :
    normSq (left * right) = normSq left * normSq right := by
  have rearranged :
      (left * right) * (Canonical.conj left * Canonical.conj right) =
        (left * Canonical.conj left) * (right * Canonical.conj right) := by
    calc
      (left * right) * (Canonical.conj left * Canonical.conj right) =
          left * (right * (Canonical.conj left * Canonical.conj right)) :=
        Canonical.mul_assoc left right (Canonical.conj left * Canonical.conj right)
      _ = left * ((right * Canonical.conj left) * Canonical.conj right) := by
        rw [← Canonical.mul_assoc right (Canonical.conj left) (Canonical.conj right)]
      _ = left * ((Canonical.conj left * right) * Canonical.conj right) := by
        rw [Canonical.mul_comm right (Canonical.conj left)]
      _ = left * (Canonical.conj left * (right * Canonical.conj right)) := by
        rw [Canonical.mul_assoc (Canonical.conj left) right (Canonical.conj right)]
      _ = (left * Canonical.conj left) * (right * Canonical.conj right) :=
        (Canonical.mul_assoc left (Canonical.conj left) (right * Canonical.conj right)).symm
  calc
    normSq (left * right) = ((left * right) * Canonical.conj (left * right)).re := by
      exact (congrArg Canonical.re (mul_conj (left * right))).symm
    _ = ((left * right) * (Canonical.conj left * Canonical.conj right)).re := by
      rw [Canonical.conj_mul]
    _ = ((left * Canonical.conj left) * (right * Canonical.conj right)).re := by
      rw [rearranged]
    _ = normSq left * normSq right := by
      rw [mul_conj left, mul_conj right]
      change normSq left * normSq right - (0 : Fraction.Rational) * 0 =
        normSq left * normSq right
      rw [Field.zero_mul_direct, Arithmetic.sub_eq_add_neg_direct, _root_.neg_zero, _root_.add_zero]

end Canonical
end Purelib.Data.Gaussian.Basic.Canonical
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

/-- Compute Gaussian quadrance as the sum of the two exact rational coordinate squares.

The result is an exact canonical rational; no square root or completed scalar carrier
is introduced. -/
@[expose] def normSq (source : Canonical) : Fraction.Rational :=
  source.re ^ 2 + source.im ^ 2

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

/-- The power and product displays of the squared Gaussian norm agree.

The two coordinate powers have exponent two and reduce to the original
coordinate products, with the same rational sum in both displays. -/
theorem normSq_eq_canonical (source : Canonical) :
    normSq source = Canonical.normSq source := by
  change source.re ^ 2 + source.im ^ 2 =
    source.re * source.re + source.im * source.im
  rw [pow_two, pow_two]

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Basic

/-- The squared norm of the zero Gaussian pair is zero. -/
@[simp] theorem normSq_zero : normSq 0 = 0 :=
  (normSq_eq_canonical 0).trans Canonical.normSq_zero

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Basic

/-- The squared norm of the unit Gaussian pair is one. -/
@[simp] theorem normSq_one : normSq 1 = 1 :=
  (normSq_eq_canonical 1).trans Canonical.normSq_one

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- Gaussian negation preserves squared norm. -/
@[simp] theorem normSq_neg (source : Canonical) : normSq (-source) =
  normSq source :=
  by simpa only [normSq_eq_canonical] using
    Canonical.normSq_neg source

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Algebra

/-- Conjugating a Gaussian pair preserves its squared norm.

The real coordinate is unchanged and the imaginary square has both factors
negated, so each term in the displayed sum retains its scalar value. -/
@[simp] theorem normSq_conj (source : Canonical) :
    normSq (Basic.conj source) = normSq source := by
  change source.re ^ 2 + (-source.im) ^ 2 =
    source.re ^ 2 + source.im ^ 2
  apply congrArg (source.re ^ 2 + ·)
  rw [pow_two, pow_two, Ring.Multiplication.neg_mul_neg]

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- Every Gaussian rational has nonnegative squared norm.

The proof follows the signs of the retained rational numerators and positive
denominators, establishing nonnegativity of both coordinate squares and their exact
sum. -/
theorem normSq_nonneg (source : Canonical) : 0 ≤ normSq source :=
  by simpa only [normSq_eq_canonical] using
    Canonical.normSq_nonneg source

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- A Gaussian rational has zero squared norm exactly when both its coordinates are zero.

Nonnegativity forces both retained coordinate squares to vanish. Conversely the
structural zero pair has zero quadrance by direct coordinate computation. -/
theorem normSq_eq_zero {source : Canonical} :
    normSq source = 0 ↔ source = 0 :=
  by simpa only [normSq_eq_canonical] using
    Canonical.normSq_eq_zero source

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- A retained nonzero Gaussian rational has strictly positive squared norm. -/
theorem normSq_pos {source : Canonical} (nonzero : source ≠ 0) :
    0 < normSq source := by
  have nonnegative := normSq_nonneg source
  exact ⟨nonnegative, fun reverse => nonzero
    (normSq_eq_zero.mp
      (Rat.Fraction.Order.Basic.le_antisymm _ _ reverse nonnegative))⟩

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic
section Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- Gaussian squared norm preserves multiplication. -/
theorem normSq_mul (left right : Canonical) :
    normSq (left * right) = normSq left * normSq right :=
  by simpa only [normSq_eq_canonical] using
    Canonical.normSq_mul left right

end Basic
end Purelib.Data.Gaussian.Norm.Basic
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic.GaussianNormalized

/-- Compute Gaussian quadrance as the sum of the two exact rational coordinate squares.

The result is an exact canonical rational; no square root or completed scalar carrier
is introduced. -/
@[expose] def normSq (source : Number) : ReducedFraction :=
  Canonical.normSq source

end Purelib.Data.Gaussian.Norm.Basic.GaussianNormalized
end

section
public section
namespace Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Gaussian.Norm.Basic in
/-- Reading normalized scalar quadrance equals the Gaussian squared norm of the original
pair's readback. -/
theorem value_normSq (source : Number) :
    Fraction.Basic.value (GaussianNormalized.normSq source) =
      normSq (Gaussian.Basic.value source) := by
  exact (normSq_eq_canonical source).symm

end Purelib.Data.Gaussian.Norm.Basic
end

public section
namespace Purelib.Data.Gaussian.Norm.Basic

/-- Doubling a Gaussian value multiplies its squared norm by four.

Both original rational coordinates are doubled. Expanding their squares
retains the same exact Gaussian addition and quadrance operations. -/
theorem normSq_double (value : Canonical) :
    normSq (value + value) = 4 * normSq value := by
  unfold normSq
  simp only [Basic.add_re, Basic.add_im,
    -eq_self, -iff_self]
  ring1

end Purelib.Data.Gaussian.Norm.Basic

namespace Purelib.Data.Gaussian.Basic.Canonical

/-- Twice one plus the squared Gaussian norm is strictly positive.

The coefficient is arbitrary. Its retained rational coordinate products give a
nonnegative quadrance, and the positive unit summand and factor two preserve strict positivity. -/
theorem double_one_add_normSq_positive (coefficient : Canonical) :
    0 < 2 * (1 + normSq coefficient) := by
  have positive := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (normSq_nonneg coefficient) (by decide : (0 : Fraction.Rational) < 1)
  rw [Fraction.Field.add_comm] at positive
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive

end Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Data.Gaussian.Basic.Canonical

/-- Conjugating both original values preserves the squared norm of their difference. -/
public theorem normSq_conj_sub (first last : Canonical) :
    normSq (conj first - conj last) = normSq (first - last) := by
  have conjugateEq : conj (first - last) = Basic.conj (first - last) := by
    apply Basic.ext <;> rfl
  rw [← conj_sub, conjugateEq]
  rw [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_conj, Norm.Basic.normSq_eq_canonical]

end Purelib.Data.Gaussian.Basic.Canonical
