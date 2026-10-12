module
import Purelib.Geometry.Rotations.Cayley.Cap
public import Purelib.Examples.Geometry.Rotations.Caps
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Five
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Rotations.Orientation.Handedness
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, section 8: handedness

Handedness is stored as the determinant of the displayed frame formed by an
anchor axis, a perpendicular vector, and its rotated image.  The determinant
formula is valid over every explicit field.  Positivity is separated into a
small coherent ordered-field interface so the algebraic theorem remains
available over finite fields.
-/

namespace Purelib.Examples.Geometry.Rotations.Handedness

open Purelib.Examples

open Purelib.Examples.Geometry.Rotations.Caps
open Purelib.Geometry.Rotations.Orientation
open Purelib.Geometry.Rotations.Cayley

variable {K : Type*} [ExplicitField K]

namespace ExampleFortyThree

/-- The rational transversal vector `(1, 3, -1)`. -/
def transversal : Vector3 Fraction.Rational :=
  ⟨1, 3, -1⟩

/-- The retained transversal is perpendicular to the original cap anchor. -/
theorem perpendicular :
    transversal.Perpendicular
      ExampleTwentyFive.vector := by
  unfold transversal ExampleTwentyFive.vector
    Vector3.Perpendicular Vector3.dot
  ring1

/-- The retained transversal has quadrance eleven. -/
theorem quadrance :
  transversal.quadrance = (11 : Fraction.Rational) := by
  unfold transversal Vector3.quadrance Vector3.dot
  ring1

/-- The cap's handedness determinant relative to the retained axis and transversal is `1452/67`. -/
theorem handedness_value :
    Handedness.handednessDet ExampleTwentyFive.vector
      transversal
        (Cap.cap ExampleTwentyFive.vector
          ExampleTwentyFive.defined) =
      (1452 : Fraction.Rational) / 67 := by
  rw [Handedness.handednessDet_cap ExampleTwentyFive.vector
    ExampleTwentyFive.defined
      transversal
        perpendicular]
  unfold Cap.capDenominator
  rw [ExampleTwentyFive.quadrance, quadrance]
  rw [show (1 + 66 : Fraction.Rational) = 67 by ring1]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The displayed rational cap has positive handedness. -/
theorem handedness_positive :
    0 < Handedness.handednessDet ExampleTwentyFive.vector
      transversal
      (Cap.cap ExampleTwentyFive.vector
        ExampleTwentyFive.defined) := by
  rw [handedness_value]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (by decide))
    (Fraction.Cast.Order.natCast_pos_direct (by decide))

/-- The inverse cap's handedness relative to the same axis and transversal is `-1452/67`. -/
theorem inverse_handedness_value :
    Handedness.handednessDet ExampleTwentyFive.vector
      transversal
        (Cap.cap (Vector3.neg ExampleTwentyFive.vector)
          (Cap.cap_neg_defined ExampleTwentyFive.vector
            ExampleTwentyFive.defined)) =
      (-1452 : Fraction.Rational) / 67 := by
  rw [Handedness.handednessDet_cap_neg_sameAxis ExampleTwentyFive.vector
      ExampleTwentyFive.defined transversal
        perpendicular]
  unfold Cap.capDenominator
  rw [ExampleTwentyFive.quadrance, quadrance]
  rw [show (1 + 66 : Fraction.Rational) = 67 by ring1]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- The displayed inverse rational cap has negative handedness. -/
theorem inverse_handedness_negative :
    Handedness.handednessDet ExampleTwentyFive.vector
      transversal
        (Cap.cap (Vector3.neg ExampleTwentyFive.vector)
          (Cap.cap_neg_defined ExampleTwentyFive.vector
            ExampleTwentyFive.defined)) < 0 := by
  rw [inverse_handedness_value]
  simp only [ExplicitField.div_eq_mul_inv]
  change -((1452 : Fraction.Rational)) * (67 : Fraction.Rational)⁻¹ < 0
  rw [neg_mul]
  change -((1452 : Fraction.Rational) * (67 : Fraction.Rational)⁻¹) < -(0 : Fraction.Rational)
  exact Fraction.Order.Arithmetic.neg_lt_neg_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (by decide))
      (Fraction.Order.Field.inv_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (by decide))))

end ExampleFortyThree

namespace ExampleFortyFour

/-- The null-axis cap over the five-element field has zero handedness for every perpendicular transversal. -/
theorem handedness_invisible (transversal :
  Vector3 Algebra.Field.Finite.Five.Element)
    (perpendicular :
      transversal.Perpendicular ExampleTwentySeven.vector) :
    Handedness.handednessDet ExampleTwentySeven.vector transversal
        (Cap.cap ExampleTwentySeven.vector
          ExampleTwentySeven.defined) = 0 := by
  exact Handedness.handednessDet_cap_of_null ExampleTwentySeven.vector
    ExampleTwentySeven.defined transversal perpendicular
    ExampleTwentySeven.null

/-- The five-element cap multiplied by its negative-anchor cap is the identity. -/
theorem inverse_product :
    Coordinates3.Matrix3.mul
        (Cap.cap ExampleTwentySeven.vector
          ExampleTwentySeven.defined)
        (Cap.cap (Vector3.neg ExampleTwentySeven.vector)
          (Cap.cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined)) = Coordinates3.Matrix3.identity :=
  Cap.cap_mul_cap_neg ExampleTwentySeven.vector
    ExampleTwentySeven.defined

/-- The negative-anchor cap multiplied by the original five-element cap is the identity. -/
theorem reverse_inverse_product :
    Coordinates3.Matrix3.mul
        (Cap.cap (Vector3.neg ExampleTwentySeven.vector)
          (Cap.cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined))
        (Cap.cap ExampleTwentySeven.vector
          ExampleTwentySeven.defined) =
      Coordinates3.Matrix3.identity :=
  Cap.cap_neg_mul_cap ExampleTwentySeven.vector
    ExampleTwentySeven.defined

/-- The displayed five-element cap differs from its inverse. -/
theorem inverse_distinct :
    Cap.cap ExampleTwentySeven.vector
      ExampleTwentySeven.defined ≠
      Cap.cap (Vector3.neg ExampleTwentySeven.vector)
        (Cap.cap_neg_defined ExampleTwentySeven.vector
          ExampleTwentySeven.defined) := by
  decide

/-- The displayed five-element cap is not an involution. -/
theorem not_involution :
    Coordinates3.Matrix3.mul
        (Cap.cap ExampleTwentySeven.vector
          ExampleTwentySeven.defined)
        (Cap.cap ExampleTwentySeven.vector
          ExampleTwentySeven.defined) ≠
      Coordinates3.Matrix3.identity := by
  decide

/-- The inverse of the displayed five-element cap is not an involution. -/
theorem inverse_not_involution :
    Coordinates3.Matrix3.mul
        (Cap.cap (Vector3.neg ExampleTwentySeven.vector)
          (Cap.cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined))
        (Cap.cap (Vector3.neg ExampleTwentySeven.vector)
          (Cap.cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined)) ≠ Coordinates3.Matrix3.identity := by
  decide

end ExampleFortyFour

end Purelib.Examples.Geometry.Rotations.Handedness

end
