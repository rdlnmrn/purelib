module
-- Retained public numeral and subtraction parents use their original operations.
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Tactic.Ring

open Purelib.Algebra.Field.ExplicitOrder.Basic
open Purelib.Algebra.Field.ExplicitOrder.Sign

section
open Purelib.Algebra.Field

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, §16.3: the projective circle

The projective circle is stored by its denominator-free equation
`x² + y² - y = 0`.  Its rational parametrization is executable for every
requested field element; the theorem carries the exact finite certificate
`λ² ≠ -1` needed to cancel its denominator.
-/

section

variable {K : Type*} [ExplicitField K]

section

namespace Purelib.Curves.Plane.Conic

/-- One plus a scalar square is nonzero exactly when the square differs from negative one. -/
theorem projectiveParameter_denominator_ne_zero_iff (parameter : K) :
    1 + parameter ^ 2 ≠ 0 ↔ parameter ^ 2 ≠ -1 := by
  constructor
  · intro denominatorNonzero squareNegativeOne
    apply denominatorNonzero
    rw [squareNegativeOne]
    ring1
  · intro squareNotNegativeOne denominatorZero
    apply squareNotNegativeOne
    calc
      parameter ^ 2 = (1 + parameter ^ 2) - 1 := by ring1
      _ = -1 := by rw [denominatorZero]; ring1

end Purelib.Curves.Plane.Conic

end

end

end

section
public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

section

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Field.Squares

/-- No scalar in the explicit field has square negative one.

The predicate is a universal exclusion of displayed roots and assumes no carrier enumeration. -/
@[expose] def NoSquareRootOfNegativeOne : Prop :=
  ∀ value : K, value ^ 2 ≠ -1

/-- A ray-ordered explicit field has no square root of negative one.

Adding any scalar square to the positive unit gives a positive, nonzero
scalar. A square root of negative one would make that same sum zero.
-/
theorem NoSquareRootOfNegativeOne.ofRayOrdered {F : Type*} [RayOrderedExplicitField F] :
    NoSquareRootOfNegativeOne (K := F) := by
  intro value square
  have positive := RayOrderedExplicitField.add_square_pos
    (value := value) OrderedExplicitField.zero_lt_one_direct
  apply RayOrderedExplicitField.positive_ne_zero_direct positive
  rw [square]
  ring1

end Purelib.Algebra.Field.Squares

namespace Purelib.Algebra.Field.Squares

/-- Equal squares have equal or opposite roots.

Decidable equality in the explicit field resolves the two factors of their difference of squares. -/
public theorem eq_or_eq_neg_of_square_eq [DecidableEq K]
    {left right : K} (squaresEqual : left ^ 2 = right ^ 2) :
    left = right ∨ left = -right := by
  by_cases equal : left = right
  · exact Or.inl equal
  · right
    have differenceNonzero : left - right ≠ 0 := by
      intro differenceZero
      apply equal
      calc
        left = (left - right) + right := by ring1
        _ = right := by rw [differenceZero]; ring1
    have productZero : (left - right) * (left + right) = 0 := by
      calc
        (left - right) * (left + right) = left ^ 2 - right ^ 2 := by
          ring1
        _ = 0 := by rw [squaresEqual]; ring1
    have sumZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left differenceNonzero productZero
    calc
      left = (left + right) - right := by ring1
      _ = -right := by rw [sumZero]; ring1

end Purelib.Algebra.Field.Squares

namespace Purelib.Algebra.Field.Squares

end Purelib.Algebra.Field.Squares

end

end

end

section
/-!
# Divine Proportions, §§5.5–5.7: quadrea and four-point identities

These results are polynomial identities over arbitrary constructive explicit
fields.  Characteristic two is excluded only when a zero square factor must
be cancelled or when the source divides by two.
-/

public section

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Field.Squares

/-- A scalar is represented by the sum of two displayed squares.

The existential retains both roots and their squared-sum equation. -/
@[expose] def IsSumOfTwoSquares (value : K) : Prop :=
  ∃ first second : K, first ^ 2 + second ^ 2 = value

/-- A scalar is the square of a displayed nonzero root.

The existential retains the root, its nonzero certificate and its square equation. -/
@[expose] def IsNonzeroSquare (value : K) : Prop :=
  ∃ root : K, root ≠ 0 ∧ value = root ^ 2

end Purelib.Algebra.Field.Squares

end

end

end

section
public section

/-!
# Divine Proportions, Exercises 2.1–2.2: spread-number parameters

The square root in the definition of a spread number is an explicit witness.
Consequently the converse parametrization computes its parameter directly;
it never selects a root or searches a field.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Field.Squares

/-- One plus a square is nonzero if that square differs from negative one. -/
public theorem one_add_square_nonzero {value : K}
    (squareNotNegativeOne : value ^ 2 ≠ -1) :
    1 + value ^ 2 ≠ 0 := by
  intro sumZero
  apply squareNotNegativeOne
  calc
    value ^ 2 = (1 + value ^ 2) - 1 := by ring1
    _ = -1 := by rw [sumZero]; ring1

end Purelib.Algebra.Field.Squares

namespace Purelib.Algebra.Field.Squares

end Purelib.Algebra.Field.Squares

end

end

section
public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Field.Squares

/-- A scalar is the square of a displayed root.

The existential retains the root and its square equation without computing a selected root. -/
@[expose] def IsSquare (value : K) : Prop := ∃ root : K, value = root ^ 2

end Purelib.Algebra.Field.Squares

end

end

section
public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Field.Squares

/-- Dividing a nonzero square by a nonzero scalar preserves its square class.

The quotient is a nonzero square exactly when the denominator is a nonzero square; both directions construct a root by
division. -/
public theorem quotient_square_isNonzeroSquare_iff
    (numerator denominator : K)
    (numeratorNonzero : numerator ≠ 0)
    (denominatorNonzero : denominator ≠ 0) :
    Squares.IsNonzeroSquare (numerator ^ 2 / denominator) ↔
      Squares.IsNonzeroSquare denominator := by
  constructor
  · rintro ⟨quotientRoot, quotientRootNonzero, quotientEquation⟩
    have clearedEquation :
        numerator ^ 2 = quotientRoot ^ 2 * denominator := by
      calc
        numerator ^ 2 =
            (numerator ^ 2 / denominator) * denominator := by
              exact (ExplicitField.div_mul_cancel
                (numerator ^ 2) denominatorNonzero).symm
        _ = quotientRoot ^ 2 * denominator := by rw [quotientEquation]
    have quotientRootSquareNonzero : quotientRoot ^ 2 ≠ 0 := by
      simpa [pow_two] using
        (ExplicitField.mul_ne_zero quotientRootNonzero
          quotientRootNonzero)
    refine ⟨numerator / quotientRoot,
      ExplicitField.div_ne_zero numeratorNonzero quotientRootNonzero, ?_⟩
    apply ExplicitField.eq_of_mul_eq_mul_right quotientRootSquareNonzero
    calc
      denominator * quotientRoot ^ 2 =
          quotientRoot ^ 2 * denominator := by ring1
      _ = numerator ^ 2 := clearedEquation.symm
      _ = ((numerator / quotientRoot) * quotientRoot) ^ 2 := by
        rw [ExplicitField.div_mul_cancel numerator quotientRootNonzero]
      _ = (numerator / quotientRoot) ^ 2 * quotientRoot ^ 2 := by ring1
  · rintro ⟨denominatorRoot, denominatorRootNonzero, denominatorEquation⟩
    refine ⟨numerator / denominatorRoot,
      ExplicitField.div_ne_zero numeratorNonzero denominatorRootNonzero, ?_⟩
    apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      (numerator ^ 2 / denominator) * denominator = numerator ^ 2 :=
        ExplicitField.div_mul_cancel
          (numerator ^ 2) denominatorNonzero
      _ = ((numerator / denominatorRoot) * denominatorRoot) ^ 2 := by
        rw [ExplicitField.div_mul_cancel numerator denominatorRootNonzero]
      _ = (numerator / denominatorRoot) ^ 2 * denominatorRoot ^ 2 := by ring1
      _ = (numerator / denominatorRoot) ^ 2 * denominator := by
        rw [denominatorEquation]

end Purelib.Algebra.Field.Squares

namespace Purelib.Algebra.Field.Squares

end Purelib.Algebra.Field.Squares

end

end

end

section
open Purelib
open Purelib.Algebra.Field
open scoped Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.Squares

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A scalar square is zero exactly when the scalar is zero.

The supplied decidable equality and explicit nonzero-product law give the forward implication. -/
public theorem square_eq_zero_iff [DecidableEq K]
  (value : K) :
    value ^ 2 = 0 ↔ value = 0 := by
  constructor
  · intro squareZero
    by_cases valueZero : value = 0
    · exact valueZero
    · have squareNonzero : value * value ≠ 0 :=
        ExplicitField.mul_ne_zero valueZero valueZero
      exact False.elim (squareNonzero (by simpa [pow_two] using squareZero))
  · intro valueZero
    rw [valueZero]
    ring1

/-- A zero square of the difference forces the two scalars to be equal.

The supplied decidable equality supports the zero-square cancellation. -/
public theorem eq_of_sub_square_eq_zero
  [DecidableEq K]
    (left right : K) (squareZero : (left - right) ^ 2 = 0) :
    left = right := by
  have differenceZero :=
    (Algebra.Field.Squares.square_eq_zero_iff (left - right)).mp squareZero
  calc
    left = (left - right) + right := by ring1
    _ = 0 + right := congrArg (fun value : K => value + right) differenceZero
    _ = right := zero_add right

/-- A zero square of one minus two scalars forces their sum to be one.

The supplied decidable equality supports cancellation of the squared residual. -/
public theorem sum_eq_one_of_square_zero
  [DecidableEq K]
    (left right : K) (squareZero : (1 - left - right) ^ 2 = 0) :
    left + right = 1 := by
  have linearZero := (Algebra.Field.Squares.square_eq_zero_iff (1 - left - right)).mp
    squareZero
  calc
    left + right = 1 - (1 - left - right) := by ring1
    _ = 1 := by rw [linearZero]; ring1

/-- The negative square of a supplied nonzero scalar is nonzero. -/
public theorem negative_square_nonzero
    {value : K} (valueNonzero : value ≠ 0) : -(value ^ 2) ≠ 0 := by
  have squareNonzero : value * value ≠ 0 :=
    ExplicitField.mul_ne_zero valueNonzero valueNonzero
  intro negativeSquareZero
  apply squareNonzero
  calc
    value * value = value ^ 2 := by ring1
    _ = -(-(value ^ 2)) := by ring1
    _ = 0 := by rw [negativeSquareZero]; ring1

/-- A square root of negative one is nonzero in a nontrivial explicit field. -/
public theorem root_ne_zero_of_square_eq_negative_one
  [Nontrivial K]
    (root : K) (rootSquare : root ^ 2 = -1) : root ≠ 0 := by
  intro rootZero
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = -(-1) := by ring1
    _ = -(root ^ 2) := by rw [rootSquare]
    _ = 0 := by rw [rootZero]; ring1

end Purelib.Algebra.Field.Squares
end

end

section
public section
namespace Purelib.Algebra.Field.Squares

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A scalar with zero square is zero. -/
public theorem eq_zero_of_square_eq_zero [DecidableEq K] (value :
  K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        Algebra.Field.ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim

end Purelib.Algebra.Field.Squares
end

end

section
namespace Purelib.Algebra.Field.Squares
open Purelib.Algebra.Field
attribute [local instance high] Purelib.Algebra.Group.Negation.subNegZeroMonoid
variable {K : Type*} [ExplicitField K]

/-- A root of a nonzero square value is nonzero. -/
public theorem
  root_ne_zero_of_nonzero_square
  {value root : K}
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) : root ≠ 0 := by
  intro rootZero
  apply valueNonzero
  calc
    value = root ^ 2 := rootSquare.symm
    _ = 0 := by rw [rootZero, pow_two, MulZeroClass.mul_zero]

/-- Divide two displayed roots to obtain a root of the remaining product factor.

The square value is nonzero, and the supplied equations identify its root and the root of its product with the factor.
-/
public theorem
  quotient_square_of_product_square
    {factor squareValue squareRoot productRoot : K}
    (squareNonzero : squareValue ≠ 0)
    (squareEquation : squareRoot ^ 2 = squareValue)
    (productEquation : productRoot ^ 2 = factor * squareValue) :
    (productRoot / squareRoot) ^ 2 = factor := by
  have rootNonzero := root_ne_zero_of_nonzero_square squareNonzero
    squareEquation
  have cancel := ExplicitField.mul_inv_cancel squareRoot rootNonzero
  rw [ExplicitField.div_eq_mul_inv]
  calc
    (productRoot * squareRoot⁻¹) ^ 2 =
        productRoot ^ 2 * squareRoot⁻¹ ^ 2 := by ring1
    _ = (factor * squareValue) * squareRoot⁻¹ ^ 2 := by
      rw [productEquation]
    _ = (factor * squareRoot ^ 2) * squareRoot⁻¹ ^ 2 := by
      rw [squareEquation]
    _ =
        factor * (squareRoot * squareRoot⁻¹) ^ 2 := by ring1
    _ = factor := by rw [cancel]; ring1

end Purelib.Algebra.Field.Squares
end

section
namespace Purelib.Algebra.Field.Squares

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A pair whose sum of squares is nonzero has a nonzero coordinate. -/
private theorem direction_nonzero_of_norm_nonzero
  [DecidableEq K]
    {first second : K} (normNonzero : first ^ 2 + second ^ 2 ≠ 0) :
    first ≠ 0 ∨ second ≠ 0 := by
  by_cases firstZero : first = 0
  · right
    intro secondZero
    apply normNonzero
    rw [firstZero, secondZero]
    ring1
  · exact Or.inl firstZero

end Purelib.Algebra.Field.Squares
end

section
namespace Purelib.Algebra.Field.Squares

open Purelib

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- In a nonisotropic displayed binary direction, an isotropic perpendicular pair must vanish. This two-coordinate lemma
is the constructive core of the null-line rigidity argument. -/
public theorem
  pair_eq_zero_of_null_of_perpendicular
  [DecidableEq K]
    (first second left right : K)
    (baseNonNull : first ^ 2 + second ^ 2 ≠ 0)
    (perpendicular : first * left + second * right = 0)
    (null : left ^ 2 + right ^ 2 = 0) :
    left = 0 ∧ right = 0 := by
  let determinant := first * right - second * left
  have determinantSquare : determinant ^ 2 = 0 := by
    calc
      determinant ^ 2 =
          (first ^ 2 + second ^ 2) * (left ^ 2 + right ^ 2) -
            (first * left + second * right) ^ 2 := by
        unfold determinant
        ring1
      _ = 0 := by rw [null, perpendicular]; ring1
  have determinantZero : determinant = 0 :=
    Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (value := _) determinantSquare
  constructor
  · apply Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
      baseNonNull
    calc
      (first ^ 2 + second ^ 2) * left =
          first * (first * left + second * right) -
            second * determinant := by
        unfold determinant
        ring1
      _ = 0 := by rw [perpendicular, determinantZero]; ring1
  · apply Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left
      baseNonNull
    calc
      (first ^ 2 + second ^ 2) * right =
          second * (first * left + second * right) +
            first * determinant := by
        unfold determinant
        ring1
      _ = 0 := by rw [perpendicular, determinantZero]; ring1

end Purelib.Algebra.Field.Squares
end

section
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace Purelib.Algebra.Field.Squares
/-- Scaled exchange of two values preserves their weighted sum of squares.

The root squares to the product of the weights, and the first weight and root are nonzero; the two signed exchange
equations supply the exact scaling. -/
public theorem weightedSquares_preserved
    (firstNorm secondNorm root firstValue secondValue
      reflectedFirst reflectedSecond : K)
    (firstNormNonzero : firstNorm ≠ 0) (rootNonzero : root ≠ 0)
    (rootEquation : root ^ 2 = firstNorm * secondNorm)
    (firstSwap : root * reflectedFirst = -firstNorm * secondValue)
    (secondSwap : firstNorm * reflectedSecond = -root * firstValue) :
    secondNorm * reflectedFirst ^ 2 + firstNorm * reflectedSecond ^ 2 =
      secondNorm * firstValue ^ 2 + firstNorm * secondValue ^ 2 := by
  have firstSquare :
      root ^ 2 * reflectedFirst ^ 2 = firstNorm ^ 2 * secondValue ^ 2 := by
    calc
      root ^ 2 * reflectedFirst ^ 2 = (root * reflectedFirst) ^ 2 := by ring1
      _ = (-firstNorm * secondValue) ^ 2 := by rw [firstSwap]
      _ = firstNorm ^ 2 * secondValue ^ 2 := by ring1
  have secondSquare :
      firstNorm ^ 2 * reflectedSecond ^ 2 = root ^ 2 * firstValue ^ 2 := by
    calc
      firstNorm ^ 2 * reflectedSecond ^ 2 =
          (firstNorm * reflectedSecond) ^ 2 := by ring1
      _ = (-root * firstValue) ^ 2 := by rw [secondSwap]
      _ = root ^ 2 * firstValue ^ 2 := by ring1
  have rootSquareNonzero : root ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero rootNonzero rootNonzero
  have factorNonzero : firstNorm * root ^ 2 ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero firstNormNonzero rootSquareNonzero
  apply Purelib.Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left factorNonzero
  calc
    (firstNorm * root ^ 2) *
        (secondNorm * reflectedFirst ^ 2 +
          firstNorm * reflectedSecond ^ 2) =
      firstNorm * secondNorm *
          (root ^ 2 * reflectedFirst ^ 2) +
        root ^ 2 *
          (firstNorm ^ 2 * reflectedSecond ^ 2) := by ring1
    _ = firstNorm * secondNorm *
          (firstNorm ^ 2 * secondValue ^ 2) +
        root ^ 2 * (root ^ 2 * firstValue ^ 2) := by
          rw [firstSquare, secondSquare]
    _ = (firstNorm * root ^ 2) *
        (secondNorm * firstValue ^ 2 +
          firstNorm * secondValue ^ 2) := by
            rw [rootEquation]
            ring1
end Purelib.Algebra.Field.Squares
end
