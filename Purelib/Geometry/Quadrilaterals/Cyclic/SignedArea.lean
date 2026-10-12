module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Circles.Unit.Parametrization
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Polygons.SignedArea.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Polygons

open Purelib.Geometry.Quadrilaterals.Basic

/-!
# Divine Proportions, Theorem 113: cyclic signed area

The source's unit-circle points are explicit finite coordinate pairs.  The
proof clears the product of their four certified denominators and computes
the shoelace sum.  No orientation quotient, square root, or completed circle
is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [ExplicitField K]

section

/-- The antisymmetric numerator printed in Theorem 113. -/
def cyclicSignedAreaNumerator (parameter₁ parameter₂
  parameter₃ parameter₄ : K) : K :=
  2 * (parameter₁ - parameter₃) * (parameter₂ - parameter₄) *
    (parameter₁ + parameter₃ - parameter₂ - parameter₄ +
      parameter₁ * parameter₂ * parameter₃ + parameter₁ * parameter₃ * parameter₄ -
      parameter₂ * parameter₃ * parameter₄ - parameter₁ * parameter₂ * parameter₄)

/-- The product of the four unit-circle chart denominators. -/
def cyclicSignedAreaDenominator (parameter₁ parameter₂
  parameter₃ parameter₄ : K) : K :=
  (1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) *
    (1 + parameter₃ ^ 2) * (1 + parameter₄ ^ 2)

/-- Theorem 113 (Cyclic signed area), with every chart denominator and the signed-area normalization certified nonzero.
-/
theorem cyclic_signed_area
    (parameter₁ parameter₂ parameter₃ parameter₄ : K)
    (parameter₁SquareNotNegativeOne : parameter₁ ^ 2 ≠ -1)
    (parameter₂SquareNotNegativeOne : parameter₂ ^ 2 ≠ -1)
    (parameter₃SquareNotNegativeOne : parameter₃ ^ 2 ≠ -1)
    (parameter₄SquareNotNegativeOne : parameter₄ ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    SignedArea.Basic.polygonSignedArea
        [Quadrilateral.orientedUnitCirclePoint parameter₁, Quadrilateral.orientedUnitCirclePoint parameter₂,
          Quadrilateral.orientedUnitCirclePoint parameter₃, Quadrilateral.orientedUnitCirclePoint parameter₄] =
      cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄ /
        cyclicSignedAreaDenominator parameter₁ parameter₂ parameter₃ parameter₄ := by
  let d₁ := 1 + parameter₁ ^ 2
  let d₂ := 1 + parameter₂ ^ 2
  let d₃ := 1 + parameter₃ ^ 2
  let d₄ := 1 + parameter₄ ^ 2
  let denominator := d₁ * d₂ * d₃ * d₄
  let doubleArea := SignedArea.Basic.polygonDoubleSignedArea
    [Quadrilateral.orientedUnitCirclePoint parameter₁, Quadrilateral.orientedUnitCirclePoint parameter₂,
      Quadrilateral.orientedUnitCirclePoint parameter₃, Quadrilateral.orientedUnitCirclePoint parameter₄]
  let numerator := cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄
  have d₁Nonzero : d₁ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₁).2
      parameter₁SquareNotNegativeOne
  have d₂Nonzero : d₂ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₂).2
      parameter₂SquareNotNegativeOne
  have d₃Nonzero : d₃ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₃).2
      parameter₃SquareNotNegativeOne
  have d₄Nonzero : d₄ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₄).2
      parameter₄SquareNotNegativeOne
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero d₁Nonzero d₂Nonzero) d₃Nonzero)
      d₄Nonzero
  have firstEdge := Quadrilateral.orientedUnitCircle_positionDeterminant_cleared parameter₁ parameter₂
    parameter₁SquareNotNegativeOne parameter₂SquareNotNegativeOne
  have secondEdge := Quadrilateral.orientedUnitCircle_positionDeterminant_cleared parameter₂ parameter₃
    parameter₂SquareNotNegativeOne parameter₃SquareNotNegativeOne
  have thirdEdge := Quadrilateral.orientedUnitCircle_positionDeterminant_cleared parameter₃ parameter₄
    parameter₃SquareNotNegativeOne parameter₄SquareNotNegativeOne
  have fourthEdge := Quadrilateral.orientedUnitCircle_positionDeterminant_cleared parameter₄ parameter₁
    parameter₄SquareNotNegativeOne parameter₁SquareNotNegativeOne
  change Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₁)
      (Quadrilateral.orientedUnitCirclePoint parameter₂) * (d₁ * d₂) =
        (2 * parameter₁) * (1 - parameter₂ ^ 2) -
          (2 * parameter₂) * (1 - parameter₁ ^ 2) at firstEdge
  change Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₂)
      (Quadrilateral.orientedUnitCirclePoint parameter₃) * (d₂ * d₃) =
        (2 * parameter₂) * (1 - parameter₃ ^ 2) -
          (2 * parameter₃) * (1 - parameter₂ ^ 2) at secondEdge
  change Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₃)
      (Quadrilateral.orientedUnitCirclePoint parameter₄) * (d₃ * d₄) =
        (2 * parameter₃) * (1 - parameter₄ ^ 2) -
          (2 * parameter₄) * (1 - parameter₃ ^ 2) at thirdEdge
  change Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₄)
      (Quadrilateral.orientedUnitCirclePoint parameter₁) * (d₄ * d₁) =
        (2 * parameter₄) * (1 - parameter₁ ^ 2) -
          (2 * parameter₁) * (1 - parameter₄ ^ 2) at fourthEdge
  have doubleAreaScaled : doubleArea * denominator = 2 * numerator := by
    calc
      doubleArea * denominator =
          (Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₁)
              (Quadrilateral.orientedUnitCirclePoint parameter₂) * (d₁ * d₂)) * (d₃ * d₄) +
            (Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₂)
              (Quadrilateral.orientedUnitCirclePoint parameter₃) * (d₂ * d₃)) * (d₁ * d₄) +
            (Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₃)
              (Quadrilateral.orientedUnitCirclePoint parameter₄) * (d₃ * d₄)) * (d₁ * d₂) +
            (Determinant.positionDeterminant (Quadrilateral.orientedUnitCirclePoint parameter₄)
              (Quadrilateral.orientedUnitCirclePoint parameter₁) * (d₄ * d₁)) * (d₂ * d₃) := by
        simp only [doubleArea, SignedArea.Basic.polygonDoubleSignedArea,
          SignedArea.Basic.polygonDoubleSignedAreaAux]
        unfold denominator
        ring1
      _ = 2 * numerator := by
        rw [firstEdge, secondEdge, thirdEdge, fourthEdge]
        unfold numerator cyclicSignedAreaNumerator d₁ d₂ d₃ d₄
        ring1
  have twoDenominatorNonzero : 2 * denominator ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  have doubleAreaTwoCancel : (doubleArea / 2) * 2 = doubleArea :=
    ExplicitField.div_mul_cancel doubleArea twoNonzero
  have numeratorDenominatorCancel :
      (numerator / denominator) * denominator = numerator :=
    ExplicitField.div_mul_cancel numerator denominatorNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right twoDenominatorNonzero
  calc
    SignedArea.Basic.polygonSignedArea
          [Quadrilateral.orientedUnitCirclePoint parameter₁, Quadrilateral.orientedUnitCirclePoint parameter₂,
            Quadrilateral.orientedUnitCirclePoint parameter₃, Quadrilateral.orientedUnitCirclePoint parameter₄] *
        (2 * denominator) = doubleArea * denominator := by
      unfold SignedArea.Basic.polygonSignedArea doubleArea
      calc
        (SignedArea.Basic.polygonDoubleSignedArea
              [Quadrilateral.orientedUnitCirclePoint parameter₁,
                Quadrilateral.orientedUnitCirclePoint parameter₂,
                Quadrilateral.orientedUnitCirclePoint parameter₃,
                Quadrilateral.orientedUnitCirclePoint parameter₄] / 2) *
            (2 * denominator) =
          ((SignedArea.Basic.polygonDoubleSignedArea
              [Quadrilateral.orientedUnitCirclePoint parameter₁,
                Quadrilateral.orientedUnitCirclePoint parameter₂,
                Quadrilateral.orientedUnitCirclePoint parameter₃,
                Quadrilateral.orientedUnitCirclePoint parameter₄] / 2) * 2) *
            denominator := by ring1
        _ = SignedArea.Basic.polygonDoubleSignedArea
              [Quadrilateral.orientedUnitCirclePoint parameter₁,
                Quadrilateral.orientedUnitCirclePoint parameter₂,
                Quadrilateral.orientedUnitCirclePoint parameter₃,
                Quadrilateral.orientedUnitCirclePoint parameter₄] * denominator := by
          rw [doubleAreaTwoCancel]
    _ = 2 * numerator := doubleAreaScaled
    _ = (numerator / denominator) * (2 * denominator) := by
      calc
        2 * numerator = 2 * ((numerator / denominator) * denominator) := by
          rw [numeratorDenominatorCancel]
        _ = (numerator / denominator) * (2 * denominator) := by ring1
    _ = (cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₄ /
        cyclicSignedAreaDenominator parameter₁ parameter₂ parameter₃ parameter₄) *
          (2 * denominator) := by
      unfold numerator denominator cyclicSignedAreaDenominator d₁ d₂ d₃ d₄
      rfl
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
