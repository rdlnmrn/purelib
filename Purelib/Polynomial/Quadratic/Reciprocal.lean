module

public import Purelib.Algebra.Field.Squares.Witness
public import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Squares
import Purelib.Tactic.Ring

/-!
# Roots of a reciprocal quadratic

The polynomial `X² - 2cX + 1` is centered at `c`. A retained square root of
its discriminant computes its two roots and their pointwise factorization
over the original explicit field.
-/

public section

namespace Purelib.Polynomial.Quadratic.Reciprocal

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Squares
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField OrderDifferenceLaw)

variable {K : Type*} [ExplicitField K]

/-- Evaluate the monic reciprocal quadratic with half its linear coefficient supplied as center. -/
@[expose] def eval (center point : K) : K := point ^ 2 - 2 * center * point + 1

/-- The discriminant of the monic reciprocal quadratic. -/
@[expose] def discriminant (center : K) : K := 4 * center ^ 2 - 4

/-- Centering a reciprocal quadratic subtracts the center's square minus one. -/
theorem eval_centered (center point : K) :
    eval center point = (point - center) ^ 2 - (center ^ 2 - 1) := by
  unfold eval
  ring1

/-- A root of a reciprocal quadratic supplies a square root of its centered constant. -/
theorem centered_square_of_root (center point : K) (root : eval center point = 0) :
    (point - center) ^ 2 = center ^ 2 - 1 := by
  calc
    _ = eval center point + (center ^ 2 - 1) := by unfold eval; ring1
    _ = center ^ 2 - 1 := by rw [root, zero_add]

/-- A supplied centered square root gives a pointwise factorization into two linear factors. -/
theorem eval_factor (center radius point : K) (square : radius ^ 2 = center ^ 2 - 1) :
    eval center point = (point - (center + radius)) * (point - (center - radius)) := by
  calc
    eval center point = (point - center) ^ 2 - (center ^ 2 - 1) := eval_centered center point
    _ = (point - center) ^ 2 - radius ^ 2 := congrArg (fun value => (point - center) ^ 2 - value) square.symm
    _ = _ := by ring1

/-- A reciprocal quadratic has a field root exactly when its discriminant has a field square root.

The forward root is twice the centered polynomial root. The reverse polynomial root is the center plus half the
supplied discriminant root, with the nonzero scalar two retained explicitly. -/
theorem exists_root_iff_discriminant_square (center : K) (twoNonzero : (2 : K) ≠ 0) :
    (∃ point : K, eval center point = 0) ↔ ∃ root : K, root ^ 2 = discriminant center := by
  constructor
  · rintro ⟨point, root⟩
    refine ⟨2 * (point - center), ?_⟩
    calc
      _ = 4 * (point - center) ^ 2 := by ring1
      _ = 4 * (center ^ 2 - 1) := congrArg (fun value => 4 * value) (centered_square_of_root center point root)
      _ = discriminant center := by unfold discriminant; ring1
  · rintro ⟨root, square⟩
    have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
    have centeredSquare : (root / 2) ^ 2 = center ^ 2 - 1 := by
      rw [ExplicitField.div_eq_mul_inv]
      calc
        _ = root ^ 2 * (2 : K)⁻¹ ^ 2 := by ring1
        _ = discriminant center * (2 : K)⁻¹ ^ 2 := congrArg (fun value => value * (2 : K)⁻¹ ^ 2) square
        _ = (center ^ 2 - 1) * (2 * (2 : K)⁻¹) ^ 2 := by unfold discriminant; ring1
        _ = center ^ 2 - 1 := by rw [cancel, one_pow, mul_one]
    refine ⟨center + root / 2, ?_⟩
    rw [eval_factor center (root / 2) _ centeredSquare]
    ring1

/-- The reciprocal quadratic with center one minus twice a strict unit-interval amount has negative discriminant.

The retained difference law identifies positivity of the amount's complement.
The negative discriminant is the product of that complement, the positive
amount and four positive copies of two in the original field dictionary.
-/
theorem discriminant_halfSpread_negative {F : Type*} [RayOrderedExplicitField F]
    (law : OrderDifferenceLaw F) (amount : F) (positive : 0 < amount) (belowOne : amount < 1) :
    discriminant (1 - 2 * amount) < 0 := by
  have complement := (law.lt_one_iff amount).mp belowOne
  have fourPositive := OrderedExplicitField.mul_pos_direct
    (RayOrderedExplicitField.two_pos (F := F)) RayOrderedExplicitField.two_pos
  have sixteenPositive := OrderedExplicitField.mul_pos_direct fourPositive fourPositive
  have productPositive := OrderedExplicitField.mul_pos_direct
    (OrderedExplicitField.mul_pos_direct sixteenPositive positive) complement
  apply (law.lt_zero_iff _).mpr
  have value : -discriminant (1 - 2 * amount) =
      (((2 : F) * 2) * (2 * 2)) * amount * (1 - amount) := by unfold discriminant; ring1
  rw [value]
  exact productPositive

/-- A reciprocal quadratic with negative discriminant has no root in the original ray-ordered field. -/
theorem eval_ne_zero_of_discriminant_negative {F : Type*} [RayOrderedExplicitField F]
    (law : OrderDifferenceLaw F) (center : F) (negative : discriminant center < 0) (point : F) :
    eval center point ≠ 0 := by
  intro zero
  rcases (exists_root_iff_discriminant_square center RayOrderedExplicitField.two_ne_zero).mp ⟨point, zero⟩ with
    ⟨root, square⟩
  have negativeDiscriminantPositive := (law.lt_zero_iff _).mp negative
  have sumPositive := RayOrderedExplicitField.add_square_pos (value := root) negativeDiscriminantPositive
  have sumZero : -discriminant center + root ^ 2 = 0 := by rw [square]; ring1
  exact RayOrderedExplicitField.positive_ne_zero_direct sumPositive sumZero

/-- Compute the first reciprocal root from the original retained discriminant root. -/
@[expose] def positiveRoot (center : K) (certificate : Witness.NonzeroSquare (discriminant center)) : K :=
  center + certificate.root / 2

/-- Compute the second reciprocal root from the same retained discriminant root. -/
@[expose] def negativeRoot (center : K) (certificate : Witness.NonzeroSquare (discriminant center)) : K :=
  center - certificate.root / 2

/-- Half the retained discriminant root is a square root of the centered constant. -/
theorem half_root_square (center : K) (certificate : Witness.NonzeroSquare (discriminant center))
    (twoNonzero : (2 : K) ≠ 0) : (certificate.root / 2) ^ 2 = center ^ 2 - 1 := by
  have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  rw [ExplicitField.div_eq_mul_inv]
  calc
    _ = certificate.root ^ 2 * (2 : K)⁻¹ ^ 2 := by ring1
    _ = discriminant center * (2 : K)⁻¹ ^ 2 := congrArg (fun value => value * (2 : K)⁻¹ ^ 2) certificate.square
    _ = (center ^ 2 - 1) * (2 * (2 : K)⁻¹) ^ 2 := by unfold discriminant; ring1
    _ = center ^ 2 - 1 := by rw [cancel, one_pow, mul_one]

/-- The two computed roots factor the original reciprocal quadratic at every supplied field point. -/
theorem eval_factor_roots (center : K) (certificate : Witness.NonzeroSquare (discriminant center))
    (twoNonzero : (2 : K) ≠ 0) (point : K) :
    eval center point = (point - positiveRoot center certificate) * (point - negativeRoot center certificate) :=
  eval_factor center _ point (half_root_square center certificate twoNonzero)

/-- The two computed roots of a nonzero discriminant are distinct. -/
theorem roots_distinct (center : K) (certificate : Witness.NonzeroSquare (discriminant center))
    (twoNonzero : (2 : K) ≠ 0) : positiveRoot center certificate ≠ negativeRoot center certificate := by
  intro equal
  have halfNonzero : certificate.root / 2 ≠ 0 := ExplicitField.div_ne_zero certificate.rootNonzero twoNonzero
  have twiceZero : 2 * (certificate.root / 2) = 0 := by
    calc
      _ = positiveRoot center certificate - negativeRoot center certificate := by
        unfold positiveRoot negativeRoot
        ring1
      _ = 0 := by rw [equal]; ring1
  exact halfNonzero (Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero twoNonzero _ twiceZero)

/-- Every reciprocal root is one of the two roots computed from the retained discriminant certificate. -/
theorem root_iff_eq_roots [DecidableEq K] (center : K)
    (certificate : Witness.NonzeroSquare (discriminant center)) (twoNonzero : (2 : K) ≠ 0) (point : K) :
    eval center point = 0 ↔ point = positiveRoot center certificate ∨ point = negativeRoot center certificate := by
  constructor
  · intro root
    have square := (centered_square_of_root center point root).trans
      (half_root_square center certificate twoNonzero).symm
    rcases Squares.eq_or_eq_neg_of_square_eq square with positive | negative
    · left
      calc
        point = (point - center) + center := by ring1
        _ = positiveRoot center certificate := by rw [positive]; unfold positiveRoot; ring1
    · right
      calc
        point = (point - center) + center := by ring1
        _ = negativeRoot center certificate := by rw [negative]; unfold negativeRoot; ring1
  · intro equal
    rw [eval_factor_roots center certificate twoNonzero point]
    rcases equal with positive | negative
    · rw [positive]; ring1
    · rw [negative]; ring1

end Purelib.Polynomial.Quadratic.Reciprocal
