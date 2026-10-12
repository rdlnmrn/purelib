module

public import Purelib.Algebra.Field.Squares.Witness
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Squares
import Purelib.Tactic.Ring

/-!
# Parameters for a prescribed axis and half spread

A nonzero root of `q p (1-p)` determines the anchor scale for an axis of
quadrance `q`. The retained root gives the scale, its half-twist equation,
the cap denominator and the two opposite solutions over the original field.
-/

public section

namespace Purelib.Geometry.Rotations.Axis.Parameters

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Squares

variable {K : Type*} [ExplicitField K]

/-- The scalar square condition for a prescribed axis quadrance and half spread. -/
@[expose] def squareValue (quadrance amount : K) : K := quadrance * amount * (1 - amount)

/-- Compute the anchor scale from the original root of the prescribed-axis square condition. -/
@[expose] def anchorScale (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount)) : K :=
  certificate.root / (quadrance * (1 - amount))

/-- The root-derived anchor scale is nonzero for nonzero quadrance and half spread different from one. -/
theorem anchorScale_nonzero (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1) :
    anchorScale quadrance amount certificate ≠ 0 :=
  ExplicitField.div_ne_zero certificate.rootNonzero
    (ExplicitField.mul_ne_zero quadranceNonzero (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne))

/-- The computed scale has exactly the half twist prescribed by the half spread.

Multiplication by the original nonzero quadrance and complementary half spread cancels the root denominator. -/
theorem anchorScale_quadrance (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1) :
    anchorScale quadrance amount certificate ^ 2 * quadrance = amount / (1 - amount) := by
  let denominator := quadrance * (1 - amount)
  have complementNonzero := ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne
  have denominatorNonzero : denominator ≠ 0 := ExplicitField.mul_ne_zero quadranceNonzero complementNonzero
  have cancel := ExplicitField.mul_inv_cancel denominator denominatorNonzero
  apply Inverse.eq_div_of_mul_eq complementNonzero
  unfold anchorScale
  simp only [ExplicitField.div_eq_mul_inv]
  change (certificate.root * denominator⁻¹) ^ 2 * quadrance * (1 - amount) = amount
  calc
    _ = certificate.root ^ 2 * denominator⁻¹ * (denominator * denominator⁻¹) := by
      unfold denominator
      ring1
    _ = certificate.root ^ 2 * denominator⁻¹ := by rw [cancel, mul_one]
    _ = (quadrance * amount * (1 - amount)) * denominator⁻¹ :=
      congrArg (fun value => value * denominator⁻¹) certificate.square
    _ = amount * (denominator * denominator⁻¹) := by unfold denominator; ring1
    _ = amount := by rw [cancel, mul_one]

/-- The cap denominator of the computed anchor times the complementary half spread is one. -/
theorem denominator_mul_complement (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1) :
    (1 + anchorScale quadrance amount certificate ^ 2 * quadrance) * (1 - amount) = 1 := by
  rw [anchorScale_quadrance quadrance amount certificate quadranceNonzero amountNotOne]
  have complementNonzero := ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne
  calc
    (1 + amount / (1 - amount)) * (1 - amount) =
        (1 - amount) + (amount / (1 - amount)) * (1 - amount) := by ring1
    _ = (1 - amount) + amount := by rw [ExplicitField.div_mul_cancel _ complementNonzero]
    _ = 1 := by ring1

/-- The computed anchor has nonzero cap denominator. -/
theorem denominator_nonzero (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1) :
    1 + anchorScale quadrance amount certificate ^ 2 * quadrance ≠ 0 := by
  intro zero
  have product := denominator_mul_complement quadrance amount certificate quadranceNonzero amountNotOne
  rw [zero, zero_mul] at product
  exact (Characteristic.Nonzero.one_ne_zero_of_nonzero quadranceNonzero) product.symm

/-- Reading half spread from the computed anchor quadrance returns the original requested amount. -/
theorem halfSpread (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1) :
    (anchorScale quadrance amount certificate ^ 2 * quadrance) /
      (1 + anchorScale quadrance amount certificate ^ 2 * quadrance) = amount := by
  have inverseEqual := Inverse.inverse_eq_of_mul_eq_one
    (denominator_nonzero quadrance amount certificate quadranceNonzero amountNotOne)
    (denominator_mul_complement quadrance amount certificate quadranceNonzero amountNotOne)
  calc
    _ = (anchorScale quadrance amount certificate ^ 2 * quadrance) *
        (1 + anchorScale quadrance amount certificate ^ 2 * quadrance)⁻¹ := ExplicitField.div_eq_mul_inv _ _
    _ = (amount / (1 - amount)) * (1 - amount) :=
      congrArg₂ (fun left right => left * right)
        (anchorScale_quadrance quadrance amount certificate quadranceNonzero amountNotOne) inverseEqual
    _ = amount := ExplicitField.div_mul_cancel _ (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)

/-- Negating the retained square root negates the computed anchor scale. -/
theorem anchorScale_neg (quadrance amount : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount)) :
    anchorScale quadrance amount certificate.neg = -anchorScale quadrance amount certificate := by
  unfold anchorScale Witness.NonzeroSquare.neg
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- A retained nonzero scale satisfying the half-twist equation constructs the original nonzero square certificate.

The root is the same scale multiplied by the original quadrance and complementary half spread. -/
@[expose] def squareCertificate (quadrance amount scale : K) (scaleNonzero : scale ≠ 0)
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1)
    (halfTwist : scale ^ 2 * quadrance = amount / (1 - amount)) :
    Witness.NonzeroSquare (squareValue quadrance amount) where
  root := scale * quadrance * (1 - amount)
  rootNonzero := ExplicitField.mul_ne_zero (ExplicitField.mul_ne_zero scaleNonzero quadranceNonzero)
    (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)
  square := by
    have cancel := ExplicitField.mul_inv_cancel (1 - amount)
      (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)
    unfold squareValue
    calc
      (scale * quadrance * (1 - amount)) ^ 2 =
          (scale ^ 2 * quadrance) * (quadrance * (1 - amount) ^ 2) := by ring1
      _ = (amount / (1 - amount)) * (quadrance * (1 - amount) ^ 2) :=
        congrArg (fun value => value * (quadrance * (1 - amount) ^ 2)) halfTwist
      _ = quadrance * amount * (1 - amount) := by
        simp only [ExplicitField.div_eq_mul_inv]
        calc
          _ = quadrance * amount * (1 - amount) * ((1 - amount) * (1 - amount)⁻¹) := by ring1
          _ = _ := by rw [cancel, mul_one]

/-- The same square condition can be written with full spread instead of half spread.

The two roots differ by the original nonzero scalar two. -/
theorem square_iff_spread (quadrance amount : K) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (Witness.NonzeroSquare (squareValue quadrance amount)) ↔
      Nonempty (Witness.NonzeroSquare (quadrance * (4 * amount * (1 - amount)))) := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨⟨2 * certificate.root, ExplicitField.mul_ne_zero twoNonzero certificate.rootNonzero, ?_⟩⟩
    calc
      (2 * certificate.root) ^ 2 = 4 * certificate.root ^ 2 := by ring1
      _ = 4 * squareValue quadrance amount := congrArg (fun value => 4 * value) certificate.square
      _ = quadrance * (4 * amount * (1 - amount)) := by unfold squareValue; ring1
  · rintro ⟨certificate⟩
    refine ⟨⟨certificate.root / 2, ExplicitField.div_ne_zero certificate.rootNonzero twoNonzero, ?_⟩⟩
    have cancel := ExplicitField.mul_inv_cancel (2 : K) twoNonzero
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (certificate.root * (2 : K)⁻¹) ^ 2 = certificate.root ^ 2 * (2 : K)⁻¹ ^ 2 := by ring1
      _ = (quadrance * (4 * amount * (1 - amount))) * (2 : K)⁻¹ ^ 2 :=
        congrArg (fun value => value * (2 : K)⁻¹ ^ 2) certificate.square
      _ = squareValue quadrance amount * (2 * (2 : K)⁻¹) ^ 2 := by unfold squareValue; ring1
      _ = squareValue quadrance amount := by rw [cancel, one_pow, mul_one]

/-- Every scale with the prescribed half twist is one of the two scales computed from the retained square root. -/
theorem scale_eq_or_eq_neg [DecidableEq K] (quadrance amount scale : K)
    (certificate : Witness.NonzeroSquare (squareValue quadrance amount))
    (quadranceNonzero : quadrance ≠ 0) (amountNotOne : amount ≠ 1)
    (halfTwist : scale ^ 2 * quadrance = amount / (1 - amount)) :
    scale = anchorScale quadrance amount certificate ∨ scale = anchorScale quadrance amount certificate.neg := by
  have squareEqual : scale ^ 2 = anchorScale quadrance amount certificate ^ 2 :=
    ExplicitField.eq_of_mul_eq_mul_right quadranceNonzero
      (halfTwist.trans (anchorScale_quadrance quadrance amount certificate quadranceNonzero amountNotOne).symm)
  rcases Squares.eq_or_eq_neg_of_square_eq squareEqual with positive | negative
  · exact Or.inl positive
  · exact Or.inr (negative.trans (anchorScale_neg quadrance amount certificate).symm)

end Purelib.Geometry.Rotations.Axis.Parameters
