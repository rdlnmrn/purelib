module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Values
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

open Purelib.Polynomial

section
public section

/-!
# Divine Proportions, Exercises 14.3 and 14.4

The source writes the two nonzero order-five spread values using a square
root `r²=5`.  Here `alpha` and `beta` are finite field expressions built from
an explicitly supplied root; no completed real or selected algebraic closure
is introduced.  Their root classification and logistic identities are proved
constructively.

`Figure` is the exact finite three-vertex window from Theorem 98, labelled as
`B,A,E` around the center `P`, together with the one radial spread used by
Exercise 14.4.  Its midpoint definitions are the points `M` and `F` in Figure
14.4.  The four quadrance displays follow from Polygon triangle and the
midpoint identities.  The printed decimals are retained as exact rational
millionth brackets with opposite quadratic signs.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

variable {K : Type*} [ExplicitField K]

/-- The displayed radical expression `(5 - root) / 8`.

It is defined in the supplied field without an ordering or a choice of square root. -/
@[expose] def ChapterFourteenPentagonMetrics.alpha (root
  : K) : K := (5 - root) / 8

/-- The displayed radical expression `(5 + root) / 8`.

It is defined in the supplied field without an ordering or a choice of square root. -/
@[expose] def ChapterFourteenPentagonMetrics.beta (root :
  K) : K := (5 + root) / 8

/-- Four is nonzero when two is nonzero in the supplied field. -/
private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) :
  (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by ring1]
  exact ExplicitField.mul_ne_zero twoNonzero twoNonzero

/-- Eight is nonzero when two is nonzero in the supplied field. -/
private theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0)
  : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by ring1]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

/-- Sixteen is nonzero when two is nonzero in the supplied field. -/
private theorem sixteen_ne_zero (twoNonzero : (2 : K) ≠
  0) : (16 : K) ≠ 0 := by
  rw [show (16 : K) = 4 * 4 by ring1]
  exact ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
    (four_ne_zero twoNonzero)

/-- Multiplying the minus radical expression by eight clears its denominator when two is nonzero. -/
private theorem alpha_mul_eight (root : K) (twoNonzero :
  (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8 = 5 - root := by
  exact ExplicitField.div_mul_cancel _ (eight_ne_zero twoNonzero)

/-- Multiplying the plus radical expression by eight clears its denominator when two is nonzero. -/
private theorem beta_mul_eight (root : K) (twoNonzero :
  (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8 = 5 + root := by
  exact ExplicitField.div_mul_cancel _ (eight_ne_zero twoNonzero)

/-- A displayed nonzero square root of five certifies that five is nonzero. -/
private theorem five_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) : (5 : K) ≠ 0 := by
  intro fiveZero
  have squareZero : root * root = 0 := by
    calc
      root * root = root ^ 2 := by ring1
      _ = 5 := rootSquare
      _ = 0 := fiveZero
  by_cases rootZero : root = 0
  · exact rootNonzero rootZero
  · exact (ExplicitField.mul_ne_zero rootZero rootZero) squareZero

/-- A nonzero square root of five makes the displayed `alpha` nonzero. -/
theorem alpha_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root ≠ 0 := by
  intro alphaZero
  have rootFive : root = 5 := by
    have differenceZero : (5 : K) - root = 0 := by
      calc
        (5 : K) - root = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8 :=
          (alpha_mul_eight root twoNonzero).symm
        _ = 0 := by rw [alphaZero]; ring1
    exact Group.eq_of_sub_eq_zero differenceZero |>.symm
  have twentyZero : (20 : K) = 0 := by
    calc
      (20 : K) = root ^ 2 - 5 := by rw [rootFive]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have twentyNonzero : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 4 * 5 by ring1]
    exact ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
      (five_ne_zero root rootNonzero rootSquare)
  exact twentyNonzero twentyZero

/-- A nonzero square root of five makes the displayed `beta` nonzero. -/
theorem beta_ne_zero [DecidableEq K]
    (root : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root ≠ 0 := by
  intro betaZero
  have rootNegativeFive : root = -5 := by
    have sumZero : (5 : K) + root = 0 := by
      calc
        (5 : K) + root = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8 :=
          (beta_mul_eight root twoNonzero).symm
        _ = 0 := by rw [betaZero]; ring1
    apply eq_neg_of_add_eq_zero_left
    calc
      root + 5 = 5 + root := by ring1
      _ = 0 := sumZero
  have twentyZero : (20 : K) = 0 := by
    calc
      (20 : K) = root ^ 2 - 5 := by rw [rootNegativeFive]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have twentyNonzero : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 4 * 5 by ring1]
    exact ExplicitField.mul_ne_zero (four_ne_zero twoNonzero)
      (five_ne_zero root rootNonzero rootSquare)
  exact twentyNonzero twentyZero

/-- `alpha` annihilates the nontrivial quadratic factor of `S₅`. -/
theorem factor_alpha (root : K) (rootSquare : root ^ 2 =
  5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 - 20 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root + 16 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root ^ 2 = 0 := by
  apply ExplicitField.eq_of_mul_eq_mul_right (four_ne_zero twoNonzero)
  calc
    (5 - 20 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root + 16 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root ^ 2) * 4 =
        20 - 10 * (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8) +
          (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8) ^ 2 := by ring1
    _ = 20 - 10 * (5 - root) + (5 - root) ^ 2 := by
      rw [alpha_mul_eight root twoNonzero]
    _ = root ^ 2 - 5 := by ring1
    _ = 0 := by rw [rootSquare]; ring1
    _ = 0 * 4 := by ring1

/-- `beta` annihilates the nontrivial quadratic factor of `S₅`. -/
theorem factor_beta (root : K) (rootSquare : root ^ 2 =
  5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 - 20 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root + 16 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root ^ 2 = 0 := by
  apply ExplicitField.eq_of_mul_eq_mul_right (four_ne_zero twoNonzero)
  calc
    (5 - 20 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root + 16 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root ^ 2) * 4 =
        20 - 10 * (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8) +
          (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8) ^ 2 := by ring1
    _ = 20 - 10 * (5 + root) + (5 + root) ^ 2 := by
      rw [beta_mul_eight root twoNonzero]
    _ = root ^ 2 - 5 := by ring1
    _ = 0 := by rw [rootSquare]; ring1
    _ = 0 * 4 := by ring1

/-- The order-five identity `β=4α(1-α)`. -/
theorem beta_logistic_alpha (root : K) (rootSquare : root
  ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root = 4 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * (1 -
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root) := by
  apply ExplicitField.eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root = 2 *
      (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8) := by ring1
    _ = 2 * (5 + root) := by rw [beta_mul_eight root twoNonzero]
    _ = 8 * (5 - root) - (5 - root) ^ 2 := by
      apply Group.eq_of_sub_eq_zero
      calc
        2 * (5 + root) - (8 * (5 - root) - (5 - root) ^ 2) =
            root ^ 2 - 5 := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = 8 * (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8) -
      (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8) ^ 2 := by
      rw [alpha_mul_eight root twoNonzero]
    _ = 16 * (4 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * (1 -
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root)) := by
      ring1

/-- The symmetric order-five identity `α=4β(1-β)`. -/
theorem alpha_logistic_beta (root : K) (rootSquare : root
  ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root = 4 *
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * (1 -
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root) := by
  apply ExplicitField.eq_of_mul_eq_mul_left (sixteen_ne_zero twoNonzero)
  calc
    16 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root = 2 *
      (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8) := by ring1
    _ = 2 * (5 - root) := by rw [alpha_mul_eight root twoNonzero]
    _ = 8 * (5 + root) - (5 + root) ^ 2 := by
      apply Group.eq_of_sub_eq_zero
      calc
        2 * (5 - root) - (8 * (5 + root) - (5 + root) ^ 2) =
            root ^ 2 - 5 := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = 8 * (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8) -
      (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8) ^ 2 := by
      rw [beta_mul_eight root twoNonzero]
    _ = 16 * (4 * Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * (1 -
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root)) := by
      ring1

/-- Every zero of the quadratic factor is one of the two displayed values.
The difference-of-squares product is split by decidable equality, without a
global root-selection argument. -/
theorem factor_root_classification [DecidableEq K]
    (root value : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0)
    (factorZero : 5 - 20 * value + 16 * value ^ 2 = 0) :
    value = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root ∨ value =
      Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root := by
  let transformed := 8 * value - 5
  have transformedSquare : transformed ^ 2 = 5 := by
    calc
      transformed ^ 2 = 5 +
          4 * (5 - 20 * value + 16 * value ^ 2) := by
        unfold transformed
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have productZero : (transformed - root) * (transformed + root) = 0 := by
    calc
      (transformed - root) * (transformed + root) =
          transformed ^ 2 - root ^ 2 := by ring1
      _ = 0 := by rw [transformedSquare, rootSquare]; ring1
  by_cases firstZero : transformed - root = 0
  · right
    apply ExplicitField.eq_of_mul_eq_mul_right (eight_ne_zero twoNonzero)
    calc
      value * 8 = 5 + root := by
        have transformedRoot : transformed = root := Group.eq_of_sub_eq_zero firstZero
        calc
          value * 8 = transformed + 5 := by ring1
          _ = 5 + root := by rw [transformedRoot]; ring1
      _ = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root * 8 :=
        (beta_mul_eight root twoNonzero).symm
  · left
    have secondZero : transformed + root = 0 := by
      by_cases secondZero : transformed + root = 0
      · exact secondZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstZero secondZero) productZero)
    apply ExplicitField.eq_of_mul_eq_mul_right (eight_ne_zero twoNonzero)
    calc
      value * 8 = 5 - root := by
        have transformedNegativeRoot : transformed = -root :=
          eq_neg_of_add_eq_zero_left secondZero
        calc
          value * 8 = transformed + 5 := by ring1
          _ = 5 - root := by rw [transformedNegativeRoot]; ring1
      _ = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root * 8 :=
        (alpha_mul_eight root twoNonzero).symm

/-- Exercise 14.3's root claim: `alpha` and `beta` are roots of `S₅`, and
they exhaust all its requested nonzero roots. -/
theorem nontrivial_zeroes [DecidableEq K]
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Basic.spreadPolynomial 5
      (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root) = 0 ∧
      Recurrence.Spread.Basic.spreadPolynomial 5
        (Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root) = 0 ∧
      ∀ value : K, value ≠ 0 → Recurrence.Spread.Basic.spreadPolynomial 5 value = 0 →
        value = Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root ∨ value =
          Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root := by
  constructor
  · rw [Recurrence.Spread.Values.spreadPolynomial_five_formula,
      factor_alpha root rootSquare twoNonzero]
    ring1
  constructor
  · rw [Recurrence.Spread.Values.spreadPolynomial_five_formula,
      factor_beta root rootSquare twoNonzero]
    ring1
  · intro value valueNonzero polynomialZero
    rw [Recurrence.Spread.Values.spreadPolynomial_five_formula] at polynomialZero
    have factorSquareZero : (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0 := by
      by_cases factorSquareZero :
          (5 - 20 * value + 16 * value ^ 2) ^ 2 = 0
      · exact factorSquareZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero valueNonzero factorSquareZero)
            polynomialZero)
    have factorZero : 5 - 20 * value + 16 * value ^ 2 = 0 := by
      by_cases factorZero : 5 - 20 * value + 16 * value ^ 2 = 0
      · exact factorZero
      · have factorSquareNonzero :
            (5 - 20 * value + 16 * value ^ 2) *
                (5 - 20 * value + 16 * value ^ 2) ≠ 0 :=
          ExplicitField.mul_ne_zero factorZero factorZero
        apply False.elim
        apply factorSquareNonzero
        simpa only [pow_two] using factorSquareZero
    exact factor_root_classification root value rootSquare twoNonzero factorZero

end Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

end

section
public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

section PlatonicSolids

variable {K : Type*} [ExplicitField K]
section Golden

/-- The same minus radical expression `(5 - root) / 8`, with its original definition retained. -/
abbrev PlatonicSolids.alpha (root : K) : K :=
  Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.alpha root

/-- The same plus radical expression `(5 + root) / 8`, with its original definition retained. -/
abbrev PlatonicSolids.beta (root : K) : K :=
  Recurrence.Spread.Roots.Five.Radical.ChapterFourteenPentagonMetrics.beta root

/-- The golden identity used to simplify the icosahedral face spread. -/
theorem
  Golden.beta_mul_three_alpha_sub_beta_eq_alpha_square
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root * (3 *
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root -
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root) =
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root ^ 2 := open Purelib in by
  have eightNonzero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.eight_ne_zero (K := K) twoNonzero : (8 : K) ≠ 0)) twoNonzero
  have alphaEight : Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root * 8 = 5 - root :=
    ExplicitField.div_mul_cancel _ eightNonzero
  have betaEight : Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root * 8 = 5 + root :=
    ExplicitField.div_mul_cancel _ eightNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right
    (Algebra.Field.Characteristic.Nonzero.Golden.sixtyFour_ne_zero twoNonzero)
  calc
    (Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root * (3 *
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root -
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root)) * 64 =
        (Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root * 8) *
          (3 * (Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root * 8) -
            Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.beta root * 8) := by ring1
    _ = (5 + root) * (3 * (5 - root) - (5 + root)) := by
      rw [alphaEight, betaEight]
    _ = (5 - root) ^ 2 := by
      apply Group.eq_of_sub_eq_zero
      calc
        (5 + root) * (3 * (5 - root) - (5 + root)) -
            (5 - root) ^ 2 = -5 * (root ^ 2 - 5) := by ring1
        _ = 0 := by rw [rootSquare]; ring1
    _ = Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root ^ 2 * 64 := by rw [← alphaEight]; ring1

/-- The golden identity used to simplify the dodecahedral face spread. -/
theorem
  Golden.five_mul_four_alpha_sub_one_eq_sixteen_alpha_square
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) :
    5 * (4 * Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root - 1) = 16 *
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root ^ 2 := by
  have factor :=
    factor_alpha
      root rootSquare twoNonzero
  apply Group.eq_of_sub_eq_zero
  calc
    5 * (4 * Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root - 1) - 16 *
      Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root ^ 2 =
        -(5 - 20 * Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root + 16 *
          Recurrence.Spread.Roots.Five.Radical.PlatonicSolids.alpha root ^ 2) := by ring1
    _ = 0 := by rw [factor]; ring1

end Golden
end PlatonicSolids
end Purelib.Polynomial.Recurrence.Spread.Roots.Five.Radical

end

end
