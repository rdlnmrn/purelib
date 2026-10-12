module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Circles.Unit.Parametrization
import Purelib.Geometry.Plane.Point.Determinant
public import Purelib.Geometry.Polygons.SignedArea.Basic
import Purelib.Geometry.Quadrilaterals.Cyclic.SignedArea
public import Purelib.Geometry.Triangles.SignedArea
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Curves.Plane (Conic)

open Purelib.Geometry.Polygons

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Triangles

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

/-- The signed area of three parametrized unit-circle points is a rational product of parameter differences.

Each parameter square differs from minus one, and two is nonzero, so all displayed denominators may be cancelled. -/
theorem exercise_17_2
    (parameter₁ parameter₂ parameter₃ : K)
    (parameter₁SquareNotNegativeOne : parameter₁ ^ 2 ≠ -1)
    (parameter₂SquareNotNegativeOne : parameter₂ ^ 2 ≠ -1)
    (parameter₃SquareNotNegativeOne : parameter₃ ^ 2 ≠ -1)
    (twoNonzero : (2 : K) ≠ 0) :
    SignedArea.triangleSignedArea (Quadrilateral.orientedUnitCirclePoint parameter₁)
        (Quadrilateral.orientedUnitCirclePoint parameter₂) (Quadrilateral.orientedUnitCirclePoint parameter₃) =
      (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        ((1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) * (1 + parameter₃ ^ 2)) := by
  let d₁ := 1 + parameter₁ ^ 2
  let d₂ := 1 + parameter₂ ^ 2
  let d₃ := 1 + parameter₃ ^ 2
  let shortDenominator := d₁ * d₂ * d₃
  let longDenominator := shortDenominator * d₃
  have d₁Nonzero : d₁ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₁).2
      parameter₁SquareNotNegativeOne
  have d₂Nonzero : d₂ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₂).2
      parameter₂SquareNotNegativeOne
  have d₃Nonzero : d₃ ≠ 0 :=
    (Conic.projectiveParameter_denominator_ne_zero_iff parameter₃).2
      parameter₃SquareNotNegativeOne
  have shortDenominatorNonzero : shortDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero d₁Nonzero d₂Nonzero) d₃Nonzero
  have longDenominatorNonzero : longDenominator ≠ 0 :=
    ExplicitField.mul_ne_zero shortDenominatorNonzero d₃Nonzero
  have quadrilateralFormula := Quadrilateral.cyclic_signed_area parameter₁ parameter₂ parameter₃ parameter₃
    parameter₁SquareNotNegativeOne parameter₂SquareNotNegativeOne
    parameter₃SquareNotNegativeOne parameter₃SquareNotNegativeOne twoNonzero
  have repeatedPointArea :
      SignedArea.Basic.polygonSignedArea
          [Quadrilateral.orientedUnitCirclePoint parameter₁, Quadrilateral.orientedUnitCirclePoint parameter₂,
            Quadrilateral.orientedUnitCirclePoint parameter₃, Quadrilateral.orientedUnitCirclePoint parameter₃] =
        SignedArea.triangleSignedArea (Quadrilateral.orientedUnitCirclePoint parameter₁)
          (Quadrilateral.orientedUnitCirclePoint parameter₂) (Quadrilateral.orientedUnitCirclePoint parameter₃) := by
    unfold SignedArea.Basic.polygonSignedArea SignedArea.triangleSignedArea
    congr 1
    simp only [SignedArea.Basic.polygonDoubleSignedArea, SignedArea.Basic.polygonDoubleSignedAreaAux]
    unfold SignedArea.triangleDoubleSignedArea
    unfold Geometry.Plane.Point.Determinant.positionDeterminant
    ring1
  rw [repeatedPointArea] at quadrilateralFormula
  change SignedArea.triangleSignedArea (Quadrilateral.orientedUnitCirclePoint parameter₁)
      (Quadrilateral.orientedUnitCirclePoint parameter₂) (Quadrilateral.orientedUnitCirclePoint parameter₃) =
    Quadrilateral.cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ /
      longDenominator at quadrilateralFormula
  have shortCancel :
      ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
          (parameter₁ - parameter₃)) / shortDenominator) *
        shortDenominator =
      2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
        (parameter₁ - parameter₃) :=
    ExplicitField.div_mul_cancel _ shortDenominatorNonzero
  calc
    SignedArea.triangleSignedArea (Quadrilateral.orientedUnitCirclePoint parameter₁)
        (Quadrilateral.orientedUnitCirclePoint parameter₂) (Quadrilateral.orientedUnitCirclePoint parameter₃) =
      Quadrilateral.cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ / longDenominator :=
        quadrilateralFormula
    _ = (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        shortDenominator := by
      apply ExplicitField.eq_of_mul_eq_mul_right longDenominatorNonzero
      calc
        (Quadrilateral.cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ / longDenominator) *
            longDenominator = Quadrilateral.cyclicSignedAreaNumerator parameter₁ parameter₂ parameter₃ parameter₃ :=
          ExplicitField.div_mul_cancel _ longDenominatorNonzero
        _ = 2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃) * d₃ := by
          unfold Quadrilateral.cyclicSignedAreaNumerator d₃
          ring1
        _ = ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
              shortDenominator) * longDenominator := by
          calc
            2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                (parameter₁ - parameter₃) * d₃ =
              (((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                  (parameter₁ - parameter₃)) / shortDenominator) *
                shortDenominator) * d₃ := by rw [shortCancel]
            _ = ((2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) *
                  (parameter₁ - parameter₃)) / shortDenominator) *
                longDenominator := by unfold longDenominator; ring1
    _ = (2 * (parameter₁ - parameter₂) * (parameter₂ - parameter₃) * (parameter₁ - parameter₃)) /
        ((1 + parameter₁ ^ 2) * (1 + parameter₂ ^ 2) * (1 + parameter₃ ^ 2)) := by
      rfl

end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
