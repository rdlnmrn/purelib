module
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Coordinates3.Vector

import Purelib.Geometry.Rotations.Cayley.Cap
public import Purelib.Geometry.Rotations.Spread
public import Purelib.Algebra.Field.Finite.Five
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

namespace Purelib.Examples.Geometry.Rotations.Caps

open Purelib.Examples

open Purelib.Algebra.Field.Finite.Five renaming Element -> F5

open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3.Antisymmetric
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Cayley.Cap

variable {K : Type*} [ExplicitField K]

namespace ExampleTwentyFive

/-- The cap numerator at (4,1,7) equals the displayed integer matrix over every explicit field. -/
private theorem numerator_displayed {F : Type*}
  [ExplicitField F] :
    (⟨(4 : F) ^ 2 - 1 ^ 2 - 7 ^ 2 + 1,
        2 * (7 + 1 * 4),
        2 * (-1 + 7 * 4),
        2 * (-7 + 1 * 4),
        -(4 : F) ^ 2 + 1 ^ 2 - 7 ^ 2 + 1,
        2 * (4 + 1 * 7),
        2 * (1 + 7 * 4),
        2 * (-4 + 1 * 7),
        -(4 : F) ^ 2 - 1 ^ 2 + 7 ^ 2 + 1⟩ : Matrix3 F) =
      ⟨-33, 22, 54, -6, -63, 22, 58, 6, 33⟩ := by
  ext <;> ring1

/-- The rational cap anchor (4,1,7). -/
def vector : Vector Fraction.Rational := ⟨4, 1, 7⟩

/-- The displayed rational anchor has quadrance 66. -/
theorem quadrance : vector.quadrance = 66 := by
  unfold vector Vector3.quadrance Vector3.dot
  ring1

/-- The displayed rational cap has nonzero denominator 67. -/
theorem defined : capDenominator vector ≠ 0 := by decide

/-- The explicit cap matrix, with numerator rows (-33,22,54), (-6,-63,22), (58,6,33) and denominator 67. -/
def displayed : Matrix3 Fraction.Rational :=
  Matrix3.scale (1 / 67) ⟨-33, 22, 54, -6, -63, 22, 58, 6, 33⟩

/-- The rational Cayley cap equals the displayed matrix. -/
theorem cap_displayed : cap vector defined = displayed := by
  rw [cap_coordinate_formula]
  have denominator : capDenominator vector = 67 := by
    unfold capDenominator
    rw [quadrance]
    ring1
  rw [denominator]
  simpa only [vector, displayed] using
    congrArg (Matrix3.scale (1 / 67 : Fraction.Rational))
      (numerator_displayed (F := Fraction.Rational))

/-- The displayed rational cap matrix fixes its original anchor vector. -/
theorem vector_fixed : Matrix3.rowMul vector displayed = vector := by
  rw [← cap_displayed]
  exact rowMul_self_cap vector defined

end ExampleTwentyFive

namespace ExampleTwentySix

/-- The anchor (2,0,0) over the executable field F₅. -/
def vector : Vector F5 := ⟨2, 0, 0⟩

/-- The displayed F₅ anchor has quadrance minus one. -/
theorem quadrance : vector.quadrance = -1 := by decide

/-- The displayed F₅ cap denominator vanishes. -/
theorem denominator_zero : capDenominator vector = 0 := by decide

/-- Identity minus the displayed antisymmetric anchor matrix has determinant zero. -/
theorem identity_sub_anchor_singular :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (anchor vector)) = 0 := by
  rw [determinant_identity_sub_anchor, denominator_zero]

end ExampleTwentySix

namespace ExampleTwentySeven

/-- The nonzero null anchor (1,2,0) over F₅. -/
def vector : Vector F5 := ⟨1, 2, 0⟩

/-- The displayed F₅ anchor has quadrance zero. -/
theorem null : vector.quadrance = 0 := by decide

/-- The null-anchor cap has nonzero denominator. -/
theorem defined : capDenominator vector ≠ 0 := by decide

/-- The explicit F₅ cap matrix with rows (3,4,1), (4,4,2), (4,3,1). -/
def displayed : Matrix3 F5 := ⟨3, 4, 1, 4, 4, 2, 4, 3, 1⟩

/-- The null-anchor Cayley cap equals the displayed F₅ matrix. -/
theorem cap_displayed : cap vector defined = displayed := by decide

/-- The displayed F₅ cap matrix fixes its original null anchor. -/
theorem vector_fixed : Matrix3.rowMul vector displayed = vector := by decide

/-- The displayed null-anchor cap is not the identity matrix. -/
theorem not_identity : displayed ≠ Matrix3.identity := by decide

/-- The characteristic polynomial of the displayed F₅ cap is (X-1) cubed. -/
theorem characteristic_unipotent (X : F5) :
    Matrix3.characteristicValue displayed X = (X - 1) ^ 3 := by
  decide +revert

end ExampleTwentySeven

namespace CoordinateAxis

/-- A coordinate-axis cap fixes its axis and has the rational two-coordinate rotation block.

The parameter is the anchor coordinate, and its cap denominator must be
nonzero. The formula uses the original cap and its row-vector signs.
-/
theorem cap_parameter (parameter : K) (defined : capDenominator (⟨parameter, 0, 0⟩ : Vector3 K) ≠ 0) :
    cap (⟨parameter, 0, 0⟩ : Vector3 K) defined =
      ⟨1, 0, 0, 0, (1 - parameter ^ 2) / (1 + parameter ^ 2),
        2 * parameter / (1 + parameter ^ 2), 0,
        -(2 * parameter / (1 + parameter ^ 2)), (1 - parameter ^ 2) / (1 + parameter ^ 2)⟩ := by
  have denominator : capDenominator (⟨parameter, 0, 0⟩ : Vector3 K) = 1 + parameter ^ 2 := by
    unfold capDenominator Vector3.quadrance Vector3.dot
    ring1
  have cancel := ExplicitField.mul_inv_cancel _ defined
  rw [denominator] at cancel
  rw [cap_coordinate_formula, denominator]
  apply Matrix3.ext
  · change (1 / (1 + parameter ^ 2)) * (parameter ^ 2 - 0 ^ 2 - 0 ^ 2 + 1) = 1
    simp only [ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
    calc
      (1 * (1 + parameter ^ 2)⁻¹) * (parameter ^ 2 - 0 ^ 2 - 0 ^ 2 + 1) =
          (1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ := by ring1
      _ = 1 := cancel
  all_goals
    unfold Matrix3.scale
    simp only [ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
    ring1

/-- The rational anchor vector for the three-four-five rotation about the first coordinate axis. -/
def firstVector : Vector3 Fraction.Rational := ⟨1 / 2, 0, 0⟩

/-- The first coordinate-axis anchor has a nonzero cap denominator. -/
theorem firstDefined : capDenominator firstVector ≠ 0 := by decide

/-- The coordinate-axis cap is the three-four-five rotation.

It fixes the first coordinate and has the displayed two-dimensional block
on the other coordinates, with the row-vector cross-product convention.
-/
theorem first_cap : cap firstVector firstDefined =
    ⟨1, 0, 0, 0, 3 / 5, 4 / 5, 0, -4 / 5, 3 / 5⟩ := by decide

/-- The doubled coordinate-axis anchor parameter is four thirds. -/
def secondVector : Vector3 Fraction.Rational := ⟨4 / 3, 0, 0⟩

/-- The doubled coordinate-axis anchor has a nonzero cap denominator. -/
theorem secondDefined : capDenominator secondVector ≠ 0 := by decide

/-- The doubled coordinate-axis cap is the seven-twenty-four-twenty-five rotation.

The first coordinate stays fixed. The remaining block has cosine entry
minus seven twenty-fifths and the original positive upper sine entry.
-/
theorem second_cap : cap secondVector secondDefined =
    ⟨1, 0, 0, 0, -7 / 25, 24 / 25, 0, -24 / 25, -7 / 25⟩ := by decide

/-- Squaring the three-four-five cap gives the cap with parameter four thirds. -/
theorem square : Matrix3.mul (cap firstVector firstDefined) (cap firstVector firstDefined) =
    cap secondVector secondDefined := by decide

/-- The three-four-five cap has half spread one fifth. -/
theorem first_halfSpread : Spread.halfSpread
    (capRotation firstVector firstDefined) = (1 : Fraction.Rational) / 5 := by decide

/-- The doubled coordinate-axis cap has half spread sixteen twenty-fifths. -/
theorem second_halfSpread : Spread.halfSpread
    (capRotation secondVector secondDefined) = (16 : Fraction.Rational) / 25 := by decide

end CoordinateAxis

end Purelib.Examples.Geometry.Rotations.Caps
