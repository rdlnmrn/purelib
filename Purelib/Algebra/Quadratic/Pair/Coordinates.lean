module

public import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Algebra.Field.ExplicitField
-- The existing Pair.Basic public path exposes the retained subtraction parent.
import Purelib.Algebra.Group.Negation
-- The existing Pair.Basic public path exposes retained successor certificates.
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-!
# Splitting and circle coordinates for quadratic pairs

Parameter-one pairs retain explicit split and unsplit operations, rational
circle parameters and conjugate-scaled division. Their supplied nonzero scalar
and quadrance witnesses certify the same displayed coordinate computations.
-/

namespace Purelib.Algebra.Quadratic.Pair.Coordinates

-- Preserve the original nominal pair's operation namespace.

open Purelib.Algebra.Field
open _root_.Purelib.Algebra.Quadratic (Pair)
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

public section

variable {K : Type*} [ExplicitField K]

/-- Evaluate a parameter-one pair at a supplied scalar and its negative.

The two outputs are the real coordinate plus or minus the scalar times the imaginary coordinate; a square-root relation
is required separately. -/
@[expose] def split (root : K) (pair : Pair K (1 : K)) : Pair K (1 : K) :=
  ⟨pair.re + root * pair.im,
    pair.re - root * pair.im⟩

/-- Recover quadratic coordinates from two split values by explicit division.

The real coordinate is half their sum and the imaginary coordinate is half their difference times the supplied scalar
inverse. -/
@[expose] def unsplit (root : K) (pair : Pair K (1 : K)) : Pair K (1 : K) :=
  ⟨(pair.re + pair.im) / 2,
    ((pair.re - pair.im) * root⁻¹) / 2⟩

/-- The two split values multiply to the pair quadrance.

The supplied splitting scalar squares to negative one. -/
theorem product_split (root : K) (rootSquare : root ^ 2 = -1)
    (pair : Pair K (1 : K)) :
    (split root pair).re * (split root pair).im = pair.quadrance := by
  change (pair.re + root * pair.im) *
      (pair.re - root * pair.im) =
    pair.re ^ 2 + pair.im ^ 2
  have rootProduct : root * root = -1 := by
    simpa only [pow_two] using rootSquare
  calc
    (pair.re + root * pair.im) *
        (pair.re - root * pair.im) =
      pair.re ^ 2 - (root * root) * pair.im ^ 2 := by ring1
    _ = pair.re ^ 2 + pair.im ^ 2 := by rw [rootProduct]; ring1

/-- A nonzero scalar inverse multiplied by that scalar gives one. -/
private theorem inverse_mul (value : K) (nonzero : value ≠ 0) :
    value⁻¹ * value = 1 := by
  calc
    value⁻¹ * value = value * value⁻¹ := by ring1
    _ = 1 := ExplicitField.mul_inv_cancel value nonzero

/-- Unsplit recovers the original pair from its two split values.

The splitting scalar and two are both supplied as nonzero. -/
theorem unsplit_split (root : K) (rootNonzero : root ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (pair : Pair K (1 : K)) :
    unsplit root (split root pair) = pair := by
  have twoCancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have rootCancel := ExplicitField.mul_inv_cancel root rootNonzero
  apply Pair.ext
  · change ((pair.re + root * pair.im) +
        (pair.re - root * pair.im)) / 2 = pair.re
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      ((pair.re + root * pair.im) +
          (pair.re - root * pair.im)) * (2 : K)⁻¹ =
        pair.re * (2 * (2 : K)⁻¹) := by ring1
      _ = pair.re := by rw [twoCancel, mul_one]
  · change ((((pair.re + root * pair.im) -
        (pair.re - root * pair.im)) * root⁻¹) / 2) = pair.im
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      ((pair.re + root * pair.im -
          (pair.re - root * pair.im)) * root⁻¹) * (2 : K)⁻¹ =
        pair.im * (root * root⁻¹) * (2 * (2 : K)⁻¹) := by ring1
      _ = pair.im := by rw [rootCancel, twoCancel]; ring1

/-- Split recovers the original two values from their unsplit pair.

The splitting scalar and two are both supplied as nonzero. -/
theorem split_unsplit (root : K) (rootNonzero : root ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (pair : Pair K (1 : K)) :
    split root (unsplit root pair) = pair := by
  have twoCancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have rootCancel := ExplicitField.mul_inv_cancel root rootNonzero
  apply Pair.ext
  · change (pair.re + pair.im) / 2 +
      root * (((pair.re - pair.im) * root⁻¹) / 2) = pair.re
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (pair.re + pair.im) * (2 : K)⁻¹ +
          root * ((pair.re - pair.im) * root⁻¹ * (2 : K)⁻¹) =
        ((pair.re + pair.im) +
          (pair.re - pair.im) * (root * root⁻¹)) * (2 : K)⁻¹ := by
            ring1
      _ = pair.re * (2 * (2 : K)⁻¹) := by rw [rootCancel]; ring1
      _ = pair.re := by rw [twoCancel, mul_one]
  · change (pair.re + pair.im) / 2 -
      root * (((pair.re - pair.im) * root⁻¹) / 2) = pair.im
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (pair.re + pair.im) * (2 : K)⁻¹ -
          root * ((pair.re - pair.im) * root⁻¹ * (2 : K)⁻¹) =
        ((pair.re + pair.im) -
          (pair.re - pair.im) * (root * root⁻¹)) * (2 : K)⁻¹ := by
            ring1
      _ = pair.im * (2 * (2 : K)⁻¹) := by rw [rootCancel]; ring1
      _ = pair.im := by rw [twoCancel, mul_one]

/-- Compute the rational parameter pair on the unit circle.

Its coordinates are (one minus the parameter square) and twice the parameter, both divided by one plus the parameter
square. -/
@[expose] def circleParameter (parameter : K) : Pair K (1 : K) :=
  ⟨(1 - parameter ^ 2) / (1 + parameter ^ 2),
    (2 * parameter) / (1 + parameter ^ 2)⟩

/-- The distinguished unit-circle pair with coordinates negative one and zero. -/
@[expose] def circleInfinity : Pair K (1 : K) := ⟨-1, 0⟩

/-- The circle denominator is nonzero when negative one has no square root.

The hypothesis excludes every scalar square equal to negative one. -/
theorem circleDenominator_ne_zero
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    1 + parameter ^ 2 ≠ 0 := by
  intro denominatorZero
  apply minusOneNoRoot parameter
  calc
    parameter ^ 2 = (1 + parameter ^ 2) - 1 := by ring1
    _ = -1 := by rw [denominatorZero]; ring1

/-- The rational circle parameter has quadrance one.

The absence of a square root of negative one certifies the common denominator is nonzero. -/
theorem quadrance_circleParameter
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).quadrance = 1 := by
  have denominatorNonzero :=
    circleDenominator_ne_zero minusOneNoRoot parameter
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold circleParameter Pair.quadrance
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    ((1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 +
        (2 * parameter * (1 + parameter ^ 2)⁻¹) ^ 2 =
      ((1 + parameter ^ 2) * (1 + parameter ^ 2)) *
        ((1 + parameter ^ 2)⁻¹ * (1 + parameter ^ 2)⁻¹) := by
          ring1
    _ = ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) *
        ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) := by ring1
    _ = 1 := by rw [denominatorCancel]; ring1

/-- The distinguished circle pair has quadrance one. -/
theorem circleInfinity_quadrance : (circleInfinity : Pair K (1 : K)).quadrance = 1 := by
  unfold circleInfinity Pair.quadrance
  ring1

/-- The first circle coordinate plus one is two over the circle denominator.

Negative one has no square root, so the denominator can be cancelled. -/
theorem circleParameter_first_add_one
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).re + 1 =
      2 / (1 + parameter ^ 2) := by
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2)
    (circleDenominator_ne_zero minusOneNoRoot parameter)
  unfold circleParameter
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ + 1 =
        (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ +
          (1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ := by
            rw [denominatorCancel]
    _ = 2 * (1 + parameter ^ 2)⁻¹ := by ring1

/-- The first circle coordinate plus one is nonzero.

Two is nonzero and negative one has no square root. -/
theorem circleParameter_first_add_one_ne_zero
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).re + 1 ≠ 0 := by
  rw [circleParameter_first_add_one minusOneNoRoot parameter]
  exact ExplicitField.div_ne_zero twoNonzero
    (circleDenominator_ne_zero minusOneNoRoot parameter)

/-- Every rational circle parameter differs from the distinguished circle pair.

Two is nonzero and negative one has no square root. -/
theorem circleParameter_ne_infinity
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    circleParameter parameter ≠ circleInfinity := by
  intro equal
  apply circleParameter_first_add_one_ne_zero twoNonzero minusOneNoRoot parameter
  calc
    (circleParameter parameter).re + 1 =
        circleInfinity.re + 1 := congrArg (fun pair => pair.re + 1) equal
    _ = 0 := by unfold circleInfinity; ring1

/-- Recover a circle parameter as the second coordinate divided by the first plus one.

Two is nonzero and negative one has no square root, justifying both divisions. -/
theorem circleParameter_inverse
    (twoNonzero : (2 : K) ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (parameter : K) :
    (circleParameter parameter).im /
        ((circleParameter parameter).re + 1) = parameter := by
  have denominatorNonzero :=
    circleDenominator_ne_zero minusOneNoRoot parameter
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  have firstAdd := circleParameter_first_add_one minusOneNoRoot parameter
  have firstAddNonzero := circleParameter_first_add_one_ne_zero
    twoNonzero minusOneNoRoot parameter
  have secondRelation : (circleParameter parameter).im =
      parameter * ((circleParameter parameter).re + 1) := by
    rw [firstAdd]
    unfold circleParameter
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  rw [secondRelation, ExplicitField.div_eq_mul_inv]
  calc
    parameter * ((circleParameter parameter).re + 1) *
        ((circleParameter parameter).re + 1)⁻¹ =
      parameter * (((circleParameter parameter).re + 1) *
        ((circleParameter parameter).re + 1)⁻¹) := by ring1
    _ = parameter := by
      rw [ExplicitField.mul_inv_cancel _ firstAddNonzero, mul_one]

/-- A scalar with zero square is zero in the explicit field.

Decidable equality supplies the constructive nonzero alternative used for cancellation. -/
theorem eq_zero_of_square_eq_zero (eqDecidable : DecidableEq K)
    (value : K) (squareZero : value ^ 2 = 0) : value = 0 := by
  cases eqDecidable value 0 with
  | isTrue equal => exact equal
  | isFalse nonzero =>
      apply False.elim
      apply ExplicitField.mul_ne_zero nonzero nonzero
      simpa only [pow_two] using squareZero

/-- A unit-quadrance pair away from the distinguished point has first coordinate plus one nonzero.

Decidable equality reduces the exceptional case to a zero square in the other coordinate. -/
theorem first_add_one_ne_zero_of_quadrance_one_of_ne_infinity
    (eqDecidable : DecidableEq K) (pair : Pair K (1 : K))
    (quadranceOne : pair.quadrance = 1) (notInfinity : pair ≠ circleInfinity) :
    pair.re + 1 ≠ 0 := by
  intro firstAddZero
  have firstNegOne : pair.re = -1 := by
    calc
      pair.re = (pair.re + 1) - 1 := by ring1
      _ = -1 := by rw [firstAddZero]; ring1
  have secondSquareZero : pair.im ^ 2 = 0 := by
    unfold Pair.quadrance at quadranceOne
    calc
      pair.im ^ 2 =
          (pair.re ^ 2 + pair.im ^ 2) - pair.re ^ 2 := by ring1
      _ = 1 - (-1 : K) ^ 2 := by rw [quadranceOne, firstNegOne]
      _ = 0 := by ring1
  have secondZero :=
    eq_zero_of_square_eq_zero eqDecidable pair.im secondSquareZero
  apply notInfinity
  apply Pair.ext
  · exact firstNegOne
  · exact secondZero

/-- Every unit-quadrance pair away from the distinguished point has its displayed rational parameter.

With decidable equality and no square root of negative one, dividing the second coordinate by the first plus one
reconstructs the pair. -/
theorem circleParameter_complete (eqDecidable : DecidableEq K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (pair : Pair K (1 : K))
    (quadranceOne : pair.quadrance = 1) (notInfinity : pair ≠ circleInfinity) :
    circleParameter (pair.im / (pair.re + 1)) = pair := by
  have firstAddNonzero :=
    first_add_one_ne_zero_of_quadrance_one_of_ne_infinity
      eqDecidable pair quadranceOne notInfinity
  have firstAddCancel := ExplicitField.mul_inv_cancel
    (pair.re + 1) firstAddNonzero
  have secondSquare : pair.im ^ 2 = 1 - pair.re ^ 2 := by
    unfold Pair.quadrance at quadranceOne
    calc
      pair.im ^ 2 =
          (pair.re ^ 2 + pair.im ^ 2) - pair.re ^ 2 := by ring1
      _ = 1 - pair.re ^ 2 := by rw [quadranceOne]
  have parameterSquare :
      (pair.im / (pair.re + 1)) ^ 2 =
        (1 - pair.re) * (pair.re + 1)⁻¹ := by
    rw [ExplicitField.div_eq_mul_inv]
    calc
      (pair.im * (pair.re + 1)⁻¹) ^ 2 =
          pair.im ^ 2 * ((pair.re + 1)⁻¹ ^ 2) := by ring1
      _ = (1 - pair.re ^ 2) * ((pair.re + 1)⁻¹ ^ 2) := by
        rw [secondSquare]
      _ = (1 - pair.re) *
          ((pair.re + 1) * (pair.re + 1)⁻¹) *
            (pair.re + 1)⁻¹ := by ring1
      _ = (1 - pair.re) * (pair.re + 1)⁻¹ := by
        rw [firstAddCancel]
        ring1
  have firstNumerator :
      1 - (pair.im / (pair.re + 1)) ^ 2 =
        pair.re * (1 + (pair.im / (pair.re + 1)) ^ 2) := by
    rw [parameterSquare]
    calc
      1 - (1 - pair.re) * (pair.re + 1)⁻¹ =
          pair.re *
              (1 + (1 - pair.re) * (pair.re + 1)⁻¹) +
            (1 - pair.re) *
              (1 - (pair.re + 1) * (pair.re + 1)⁻¹) := by
                ring1
      _ = pair.re *
          (1 + (1 - pair.re) * (pair.re + 1)⁻¹) := by
        rw [firstAddCancel]
        ring1
  have secondNumerator :
      2 * (pair.im / (pair.re + 1)) =
        pair.im * (1 + (pair.im / (pair.re + 1)) ^ 2) := by
    rw [parameterSquare, ExplicitField.div_eq_mul_inv]
    calc
      2 * (pair.im * (pair.re + 1)⁻¹) =
          pair.im *
              (1 + (1 - pair.re) * (pair.re + 1)⁻¹) +
            pair.im *
              ((pair.re + 1) * (pair.re + 1)⁻¹ - 1) := by
                ring1
      _ = pair.im *
          (1 + (1 - pair.re) * (pair.re + 1)⁻¹) := by
        rw [firstAddCancel]
        ring1
  have denominatorNonzero := circleDenominator_ne_zero minusOneNoRoot
    (pair.im / (pair.re + 1))
  have denominatorCancel := ExplicitField.mul_inv_cancel
    (1 + (pair.im / (pair.re + 1)) ^ 2) denominatorNonzero
  apply Pair.ext
  · change (1 - (pair.im / (pair.re + 1)) ^ 2) /
        (1 + (pair.im / (pair.re + 1)) ^ 2) = pair.re
    rw [firstNumerator, ExplicitField.div_eq_mul_inv]
    calc
      pair.re * (1 + (pair.im / (pair.re + 1)) ^ 2) *
          (1 + (pair.im / (pair.re + 1)) ^ 2)⁻¹ =
        pair.re * ((1 + (pair.im / (pair.re + 1)) ^ 2) *
          (1 + (pair.im / (pair.re + 1)) ^ 2)⁻¹) := by ring1
      _ = pair.re := by rw [denominatorCancel, mul_one]
  · change (2 * (pair.im / (pair.re + 1))) /
        (1 + (pair.im / (pair.re + 1)) ^ 2) = pair.im
    rw [secondNumerator, ExplicitField.div_eq_mul_inv]
    calc
      pair.im * (1 + (pair.im / (pair.re + 1)) ^ 2) *
          (1 + (pair.im / (pair.re + 1)) ^ 2)⁻¹ =
        pair.im * ((1 + (pair.im / (pair.re + 1)) ^ 2) *
          (1 + (pair.im / (pair.re + 1)) ^ 2)⁻¹) := by ring1
      _ = pair.im := by rw [denominatorCancel, mul_one]

/-- Zero quadrance forces a parameter-one pair to be zero when negative one is nonsquare.

Decidable equality separates a zero coordinate from the ratio that would otherwise square to negative one. -/
theorem eq_zero_of_quadrance_eq_zero_of_minus_one_nonsquare
    (eqDecidable : DecidableEq K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) (pair : Pair K (1 : K))
    (quadranceZero : pair.quadrance = 0) : pair = ⟨0, 0⟩ := by
  have secondZero : pair.im = 0 := by
    cases eqDecidable pair.im 0 with
    | isTrue equal => exact equal
    | isFalse secondNonzero =>
        have secondCancel := ExplicitField.mul_inv_cancel
          pair.im secondNonzero
        have firstSquare : pair.re ^ 2 = -(pair.im ^ 2) := by
          unfold Pair.quadrance at quadranceZero
          calc
            pair.re ^ 2 =
                (pair.re ^ 2 + pair.im ^ 2) - pair.im ^ 2 := by ring1
            _ = -(pair.im ^ 2) := by rw [quadranceZero]; ring1
        apply False.elim
        apply minusOneNoRoot (pair.re / pair.im)
        rw [ExplicitField.div_eq_mul_inv]
        calc
          (pair.re * pair.im⁻¹) ^ 2 =
              pair.re ^ 2 * (pair.im⁻¹ ^ 2) := by ring1
          _ = -(pair.im ^ 2) * (pair.im⁻¹ ^ 2) := by
            rw [firstSquare]
          _ = -((pair.im * pair.im⁻¹) *
              (pair.im * pair.im⁻¹)) := by ring1
          _ = -1 := by rw [secondCancel]; ring1
  have firstSquareZero : pair.re ^ 2 = 0 := by
    unfold Pair.quadrance at quadranceZero
    calc
      pair.re ^ 2 =
          (pair.re ^ 2 + pair.im ^ 2) - pair.im ^ 2 := by ring1
      _ = 0 := by rw [quadranceZero, secondZero]; ring1
  have firstZero := eq_zero_of_square_eq_zero eqDecidable
    pair.re firstSquareZero
  apply Pair.ext
  · exact firstZero
  · exact secondZero

/-- Multiply by a conjugate pair and scale by the inverse supplied quadrance.

The definition is total; inverse laws require the supplied scalar to be the divisor quadrance and to be nonzero. -/
@[expose] def divideMul (value : K) (divisor pair : Pair K (1 : K)) : Pair K (1 : K) :=
  Pair.scale value⁻¹ (Pair.multiply divisor.conjugate pair)

/-- Conjugate-scaled division cancels multiplication by its divisor.

The supplied nonzero scalar equals the divisor quadrance. -/
theorem divideMul_mul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : Pair K (1 : K)) (divisorQuadrance : divisor.quadrance = value) :
    divideMul value divisor (Pair.multiply divisor pair) = pair := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  apply Pair.ext
  · calc
      (divideMul value divisor (Pair.multiply divisor pair)).re =
          value⁻¹ * (divisor.quadrance * pair.re) := by
            unfold divideMul Pair.scale Pair.multiply Pair.conjugate Pair.quadrance
            ring1
      _ = value⁻¹ * (value * pair.re) := by rw [divisorQuadrance]
      _ = pair.re := by
        calc
          value⁻¹ * (value * pair.re) =
              (value⁻¹ * value) * pair.re := by ring1
          _ = pair.re := by rw [valueCancel, _root_.one_mul]
  · calc
      (divideMul value divisor (Pair.multiply divisor pair)).im =
          value⁻¹ * (divisor.quadrance * pair.im) := by
            unfold divideMul Pair.scale Pair.multiply Pair.conjugate Pair.quadrance
            ring1
      _ = value⁻¹ * (value * pair.im) := by rw [divisorQuadrance]
      _ = pair.im := by
        calc
          value⁻¹ * (value * pair.im) =
              (value⁻¹ * value) * pair.im := by ring1
          _ = pair.im := by rw [valueCancel, _root_.one_mul]

/-- Multiplication by the divisor cancels its conjugate-scaled division.

The supplied nonzero scalar equals the divisor quadrance. -/
theorem mul_divideMul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : Pair K (1 : K)) (divisorQuadrance : divisor.quadrance = value) :
    Pair.multiply divisor (divideMul value divisor pair) = pair := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  apply Pair.ext
  · calc
      (Pair.multiply divisor (divideMul value divisor pair)).re =
          value⁻¹ * (divisor.quadrance * pair.re) := by
            unfold divideMul Pair.scale Pair.multiply Pair.conjugate Pair.quadrance
            ring1
      _ = value⁻¹ * (value * pair.re) := by rw [divisorQuadrance]
      _ = pair.re := by
        calc
          value⁻¹ * (value * pair.re) =
              (value⁻¹ * value) * pair.re := by ring1
          _ = pair.re := by rw [valueCancel, _root_.one_mul]
  · calc
      (Pair.multiply divisor (divideMul value divisor pair)).im =
          value⁻¹ * (divisor.quadrance * pair.im) := by
            unfold divideMul Pair.scale Pair.multiply Pair.conjugate Pair.quadrance
            ring1
      _ = value⁻¹ * (value * pair.im) := by rw [divisorQuadrance]
      _ = pair.im := by
        calc
          value⁻¹ * (value * pair.im) =
              (value⁻¹ * value) * pair.im := by ring1
          _ = pair.im := by rw [valueCancel, _root_.one_mul]

/-- Dividing pairs of equal nonzero quadrance gives unit quadrance.

Both input quadrances equal the supplied scalar used for the inverse scaling. -/
theorem quadrance_divideMul (value : K) (valueNonzero : value ≠ 0)
    (divisor pair : Pair K (1 : K)) (divisorQuadrance : divisor.quadrance = value)
    (pairQuadrance : pair.quadrance = value) :
    (divideMul value divisor pair).quadrance = 1 := by
  have valueCancel : value⁻¹ * value = 1 := inverse_mul value valueNonzero
  rw [divideMul, Pair.quadrance_scale, Pair.quadrance_mul, Pair.quadrance_conjugate,
    divisorQuadrance, pairQuadrance]
  calc
    value⁻¹ ^ 2 * (value * value) =
        (value⁻¹ * value) * (value⁻¹ * value) := by ring1
    _ = 1 := by rw [valueCancel]; ring1

end

end Purelib.Algebra.Quadratic.Pair.Coordinates
