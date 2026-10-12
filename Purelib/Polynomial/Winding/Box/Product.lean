module
import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
public import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Edge.Product
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free finite product assembly for constructive winding

The local Cauchy-index product identity carries one explicit endpoint
correction.  This module records that identity as finite proof data, proves
its exact interval arithmetic, and telescopes the four corrections around a
closed box.  The remaining local theorem can therefore be developed and
audited independently of the global winding calculation.
-/

namespace Purelib.Polynomial.Winding.Box.Product

/-- Four local product formulas in positive box-boundary orientation. -/
structure BoxProductFormula
    (p q : CoefficientPolynomial) (box : Box) : Prop where
  /-- The edge product formula along the bottom side, oriented left to right. -/ bottom :
    Winding.Edge.Product.LineProductFormula p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
    box.xLower box.xUpper
  /-- The edge product formula along the right side, oriented bottom to top. -/ right :
    Winding.Edge.Product.LineProductFormula p q
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
    box.yLower box.yUpper
  /-- The edge product formula along the top side, oriented right to left. -/ top :
    Winding.Edge.Product.LineProductFormula p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    box.xUpper box.xLower
  /-- The edge product formula along the left side, oriented top to bottom. -/ left :
    Winding.Edge.Product.LineProductFormula p q
    (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    box.yUpper box.yLower

/-- Boundary clearance for both factors supplies all four constructive line
formulas.  The top and left sides are obtained by exact orientation reversal. -/
theorem boxProductFormula_of_boundaryClearances
    (p q : CoefficientPolynomial) (box : Box)
    (proper : box.Proper)
    (leftClearance : BoundaryClearance p box)
    (rightClearance : BoundaryClearance q box) :
    BoxProductFormula p q box := by
  open Purelib.Polynomial.Geometry.BoxClearance in
  have pBottomLeft : p.eval (Gaussian.Components.Basic.point box.xLower box.yLower) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩, Or.inl rfl⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have qBottomLeft : q.eval (Gaussian.Components.Basic.point box.xLower box.yLower) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩, Or.inl rfl⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have pBottomRight : p.eval (Gaussian.Components.Basic.point box.xUpper box.yLower) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩,
        Or.inr (Or.inl rfl)⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have qBottomRight : q.eval (Gaussian.Components.Basic.point box.xUpper box.yLower) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩,
        Or.inr (Or.inl rfl)⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have pTopRight : p.eval (Gaussian.Components.Basic.point box.xUpper box.yUpper) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩,
        Or.inr (Or.inl rfl)⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have qTopRight : q.eval (Gaussian.Components.Basic.point box.xUpper box.yUpper) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩,
        Or.inr (Or.inl rfl)⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have pTopLeft : p.eval (Gaussian.Components.Basic.point box.xLower box.yUpper) ≠ 0 :=
    leftClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩, Or.inl rfl⟩
  open Purelib.Polynomial.Geometry.BoxClearance in
  have qTopLeft : q.eval (Gaussian.Components.Basic.point box.xLower box.yUpper) ≠ 0 :=
    rightClearance.eval_ne_zero
      ⟨⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩, Or.inl rfl⟩
  have bottom := Winding.Edge.Product.lineProductFormula_of_clearances p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection proper.1
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      leftClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [Affine.Axis.line_horizontal] using pBottomLeft)
    (by simpa only [Affine.Axis.line_horizontal] using qBottomLeft)
    (by simpa only [Affine.Axis.line_horizontal] using pBottomRight)
    (by simpa only [Affine.Axis.line_horizontal] using qBottomRight)
  have right := Winding.Edge.Product.lineProductFormula_of_clearances p q
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit proper.2
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      leftClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [Affine.Axis.line_vertical] using pBottomRight)
    (by simpa only [Affine.Axis.line_vertical] using qBottomRight)
    (by simpa only [Affine.Axis.line_vertical] using pTopRight)
    (by simpa only [Affine.Axis.line_vertical] using qTopRight)
  have topIncreasing := Winding.Edge.Product.lineProductFormula_of_clearances p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection proper.1
    (Clearance.Box.Boundary.Lines.topOfBoundary
      leftClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.topOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [Affine.Axis.line_horizontal] using pTopLeft)
    (by simpa only [Affine.Axis.line_horizontal] using qTopLeft)
    (by simpa only [Affine.Axis.line_horizontal] using pTopRight)
    (by simpa only [Affine.Axis.line_horizontal] using qTopRight)
  have leftIncreasing := Winding.Edge.Product.lineProductFormula_of_clearances p q
    (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit proper.2
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      leftClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      rightClearance).toPathCertificate
    (by simpa only [Affine.Axis.line_vertical] using pBottomLeft)
    (by simpa only [Affine.Axis.line_vertical] using qBottomLeft)
    (by simpa only [Affine.Axis.line_vertical] using pTopLeft)
    (by simpa only [Affine.Axis.line_vertical] using qTopLeft)
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }

/-- The four finite endpoint corrections telescope exactly, yielding raw
closed-box multiplicativity from the four local certificates. -/
theorem quadrupledBoxWinding_mul_of_formula
    (p q : CoefficientPolynomial) (box : Box)
    (formula : BoxProductFormula p q box) :
    Winding.Box.Basic.quadrupledBoxWinding (p * q) box =
      Winding.Box.Basic.quadrupledBoxWinding p box + Winding.Box.Basic.quadrupledBoxWinding q box := by
  have bottom := formula.bottom
  have right := formula.right
  have top := formula.top
  have left := formula.left
  unfold Winding.Edge.Product.LineProductFormula Winding.Edge.Product.lineProductCorrection2 at bottom right top left
  simp only [Affine.Axis.line_horizontal] at bottom top
  simp only [Affine.Axis.line_vertical] at right left
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq, Winding.Box.Basic.quadrupledBoxWinding_eq,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  simp only [Dense.Gaussian.Path.Box.Sides.horizontalEdge, Dense.Gaussian.Path.Box.Sides.verticalEdge]
  rw [bottom, right, top, left]
  ring1

/-- Choice-free closed-box winding multiplicativity from two quantitative
boundary-clearance certificates. -/
theorem quadrupledBoxWinding_mul_of_boundaryClearances
    (p q : CoefficientPolynomial) (box : Box)
    (proper : box.Proper)
    (leftClearance : BoundaryClearance p box)
    (rightClearance : BoundaryClearance q box) :
    Winding.Box.Basic.quadrupledBoxWinding (p * q) box =
      Winding.Box.Basic.quadrupledBoxWinding p box + Winding.Box.Basic.quadrupledBoxWinding q box :=
  quadrupledBoxWinding_mul_of_formula p q box
    (boxProductFormula_of_boundaryClearances
      p q box proper leftClearance rightClearance)
end Purelib.Polynomial.Winding.Box.Product

end
