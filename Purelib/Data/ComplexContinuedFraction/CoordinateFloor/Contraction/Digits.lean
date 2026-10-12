module

public import Purelib.Data.GaussianInt.Basic
public import Purelib.Algebra.Monoid.Int
import Purelib.Data.Int.Interval
import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
meta import Purelib.Elab.Deriving.Repr
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Exceptional coordinate-floor digits

The original eight Gaussian integer digits retain their order and coordinate
selector. Their piecewise translation lower bound and exact cone inequalities
identify the original bounded exceptional digit witnesses.
-/

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Digits

open Purelib
open Purelib.Data
open Purelib.Data.Int

@[expose] public section

/-- The eight retained exceptional Gaussian-integer digits for the coordinate-floor contraction bounds.

The constructors enumerate real coordinates one or two and imaginary coordinates from minus two through one, in the
exact order read by tau. -/
inductive SmallDigit where
  /-- The digit with coordinates one and minus two. -/ | d0 /-- The digit with coordinates one and minus one. -/ | d1
    /-- The digit with coordinates one and zero. -/ | d2 /-- The digit with coordinates one and one. -/ | d3 /-- The
    digit with coordinates two and minus two. -/ | d4 /-- The digit with coordinates two and minus one. -/ | d5 /-- The
    digit with coordinates two and zero. -/ | d6 /-- The digit with coordinates two and one. -/ | d7
deriving DecidableEq

derive_exposed_repr Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.SmallDigit

end

/-- Read the retained Gaussian-integer coordinates of one exceptional digit.

The original eight constructor cases retain the displayed signed integer
coordinates without changing the order or selecting another digit. -/
@[expose] public def tau : ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.SmallDigit → Data.GaussianInt
  | .d0 => ⟨1, -2⟩
  | .d1 => ⟨1, -1⟩
  | .d2 => ⟨1, 0⟩
  | .d3 => ⟨1, 1⟩
  | .d4 => ⟨2, -2⟩
  | .d5 => ⟨2, -1⟩
  | .d6 => ⟨2, 0⟩
  | .d7 => ⟨2, 1⟩

/-- Compute the integer translation lower bound from the digit coordinates.

Use the full norm when the imaginary coordinate is nonnegative, only the real square when it is minus one, and the real
square plus the successor imaginary square otherwise. -/
@[expose] public def lambda (t : Data.GaussianInt) : Int :=
  if 0 ≤ t.im then t.re ^ 2 + t.im ^ 2
  else if t.im = -1 then t.re ^ 2
  else t.re ^ 2 + (t.im + 1) ^ 2

/-- The eight exceptional digit lower bounds are respectively two, one, one, two, five, four, four and five.

The original tau selector retains all eight signed coordinate pairs in
order; exact integer computation gives the corresponding eight lower bounds. -/
@[simp] public theorem lambda_tau :
    ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d0) = 2 ∧
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d1) = 1 ∧
    ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d2) = 1 ∧
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d3) = 2 ∧
    ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d4) = 5 ∧
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d5) = 4 ∧
    ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d6) = 4 ∧
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda
      (ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau .d7) = 5 := by
  decide

/-- The real-coordinate square is at most the piecewise integer lower bound.

The other retained square term is nonnegative in each original piecewise
branch, so adding it never decreases the original real-coordinate square. -/
private theorem square_le_lambda (t : Data.GaussianInt) : t.re ^ 2 ≤
  ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda t := by
  rw [lambda]
  split
  · have squareNonnegative : 0 ≤ t.im ^ 2 := by
      rewrite [pow_two]
      exact Int.Order.mul_self_nonneg t.im
    have bound := Int.Order.add_le_add (Int.Order.le_refl (t.re ^ 2)) squareNonnegative
    rewrite [Int.add_zero] at bound
    exact bound
  · split
    · exact Int.Order.le_refl _
    · have squareNonnegative : 0 ≤ (t.im + 1) ^ 2 := by
        rewrite [pow_two]
        exact Int.Order.mul_self_nonneg (t.im + 1)
      have bound := Int.Order.add_le_add (Int.Order.le_refl (t.re ^ 2)) squareNonnegative
      rewrite [Int.add_zero] at bound
      exact bound

/-- Every piecewise integer translation lower bound is nonnegative.

The retained real-coordinate square is nonnegative and bounds the original
piecewise digit value from below. -/
public theorem lambda_nonnegative (t : Data.GaussianInt) : 0 ≤
  ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda t := by
  have realSquareNonnegative : 0 ≤ t.re ^ 2 := by
    rewrite [pow_two]
    exact Int.Order.mul_self_nonneg t.re
  exact Int.Order.le_trans realSquareNonnegative (square_le_lambda t)

/-- A digit with real coordinate at least one in the retained cone has translation lower bound at least one.

The original real coordinate is at least one, so its retained square is
at least one and bounds the same original piecewise value. -/
public theorem one_le_lambda_of_cone (t : Data.GaussianInt)
    (cone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re) :
    1 ≤ ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda t := by
  have realNonnegative : 0 ≤ t.re :=
    Int.Order.le_trans (by decide : (0 : Int) ≤ 1) cone.1
  have squareOne : 1 ≤ t.re ^ 2 := by
    rewrite [pow_two]
    exact Int.Order.le_trans
      (Int.Order.mul_le_mul_of_nonneg_left cone.1 (by decide : (0 : Int) ≤ 1))
      (Int.Order.mul_le_mul_of_nonneg_right cone.1 realNonnegative)
  exact Int.Order.le_trans squareOne (square_le_lambda t)

/-- A cone digit whose translation lower bound is below eight equals one of the eight retained exceptional digits.

The cone retains real coordinate at least one and imaginary coordinate between minus real minus one and real. The strict
lower-bound cutoff limits the real coordinate to one or two and excludes the remaining endpoint cases. -/
public theorem exists_small_of_cone (t : Data.GaussianInt)
    (cone : 1 ≤ t.re ∧ -t.re - 1 ≤ t.im ∧ t.im ≤ t.re)
    (small : ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.lambda t < 8) : ∃ digit :
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.SmallDigit, t =
      ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau digit := by
  have realSquareSmall : t.re ^ 2 < 8 :=
    by
      have squareBound := square_le_lambda t
      omega0
  have realAtMostTwo : t.re ≤ 2 := by
    apply Int.Order.le_of_not_lt
    intro threeOrMore
    have realNonnegative : 0 ≤ t.re :=
      Int.Order.le_trans (by decide : (0 : Int) ≤ 1) cone.1
    have threeLe : (3 : Int) ≤ t.re := by
      change (2 : Int) + 1 ≤ t.re
      omega0
    have nineAtMost : 9 ≤ t.re * t.re :=
      Int.Order.le_trans
        (Int.Order.mul_le_mul_of_nonneg_right threeLe (by decide : (0 : Int) ≤ 3))
        (Int.Order.mul_le_mul_of_nonneg_left threeLe realNonnegative)
    rw [pow_two] at realSquareSmall
    exact (Int.Order.lt_iff_le_and_not_ge.mp realSquareSmall).2
      (Int.Order.le_trans (by decide : (8 : Int) ≤ 9) nineAtMost)
  have realCases : t.re = 1 ∨ t.re = 2 := by
    by_cases realOne : t.re = 1
    · exact Or.inl realOne
    · have twoLe : (2 : Int) ≤ t.re := by
        change (1 : Int) + 1 ≤ t.re
        omega0
      exact Or.inr (Int.Order.le_antisymm realAtMostTwo twoLe)
  rcases realCases with realOne | realTwo
  · have imagCases :
        t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨ t.im = 1 := by
      have imagLower : (-2 : Int) ≤ t.im := by
        calc
          (-2 : Int) = -t.re - 1 := by rw [realOne]; ring1
          _ ≤ t.im := cone.2.1
      have imagUpper : t.im ≤ (1 : Int) := realOne ▸ cone.2.2
      exact Interval.int_cases_neg_two_to_one imagLower imagUpper
    rcases imagCases with imagNegTwo | imagNegOne | imagZero | imagOne
    · refine ⟨.d0, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d1, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d2, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d3, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
  · have imagCases :
        t.im = -3 ∨ t.im = -2 ∨ t.im = -1 ∨ t.im = 0 ∨
          t.im = 1 ∨ t.im = 2 := by
      have imagLower : (-3 : Int) ≤ t.im := by
        calc
          (-3 : Int) = -t.re - 1 := by rw [realTwo]; ring1
          _ ≤ t.im := cone.2.1
      have imagUpper : t.im ≤ (2 : Int) := realTwo ▸ cone.2.2
      exact Interval.int_cases_neg_three_to_two imagLower imagUpper
    rcases imagCases with imagNegThree | imagNegTwo | imagNegOne |
      imagZero | imagOne | imagTwo
    · have value : t = ⟨2, -3⟩ := by
        apply GaussianInt.ext <;> assumption
      rw [value] at small
      change (8 : Int) < 8 at small
      exact (Int.Order.lt_irrefl 8 small).elim
    · refine ⟨.d4, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d5, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d6, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · refine ⟨.d7, ?_⟩
      apply GaussianInt.ext <;>
        simp only [ComplexContinuedFraction.CoordinateFloor.Contraction.Digits.tau] <;> assumption
    · have value : t = ⟨2, 2⟩ := by
        apply GaussianInt.ext <;> assumption
      rw [value] at small
      change (8 : Int) < 8 at small
      exact (Int.Order.lt_irrefl 8 small).elim

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Digits
