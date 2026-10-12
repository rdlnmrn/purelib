module
import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
public import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RationalFunctions.Winding.Box.Basic
public import Purelib.RationalFunctions.Winding.Line.Quotient
import Purelib.RationalFunctions.Winding.Path.Correction
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Winding.Line.Quotient (LineQuotientFormula)

section
@[expose] public section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

namespace Purelib.RationalFunctions.Winding.Box.Quotient

section
open Purelib.Data
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- The quotient winding identities for all four positively oriented box edges.

Bottom and right use increasing coordinates; top and left use reversed intervals. Each edge retains the same numerator
and denominator polynomial pair. -/
structure BoxQuotientFormula
    (numerator denominator : CoefficientPolynomial) (box :
      Rational.Box) : Prop where
  /-- The quotient identity along the bottom edge, oriented left to right. -/ bottom :
    LineQuotientFormula numerator denominator
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
    box.xLower box.xUpper
  /-- The quotient identity along the right edge, oriented bottom to top. -/ right :
    LineQuotientFormula numerator denominator
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
    box.yLower box.yUpper
  /-- The quotient identity along the top edge, oriented right to left. -/ top :
    LineQuotientFormula numerator denominator
    (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    box.xUpper box.xLower
  /-- The quotient identity along the left edge, oriented top to bottom. -/ left :
    LineQuotientFormula numerator denominator
    (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    box.yUpper box.yLower

/-- Construct the four oriented edge quotient identities from boundary clearances.

The box is proper and both polynomials have retained clearances on its boundary. The top and left identities follow by
exact interval reversal. -/
theorem boxQuotientFormula_of_boundaryClearances
    (numerator denominator : CoefficientPolynomial) (box :
      Rational.Box)
    (proper : box.Proper)
    (numeratorClearance : BoundaryClearance numerator box)
    (denominatorClearance : BoundaryClearance denominator box) :
    BoxQuotientFormula numerator denominator box := by
  have bottom := Winding.Line.Quotient.lineQuotientFormula_of_clearances numerator denominator
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection proper.1
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      numeratorClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      denominatorClearance).toPathCertificate
  have right := Winding.Line.Quotient.lineQuotientFormula_of_clearances numerator denominator
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit proper.2
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      numeratorClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      denominatorClearance).toPathCertificate
  have topIncreasing := Winding.Line.Quotient.lineQuotientFormula_of_clearances
    numerator denominator (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    proper.1
    (Clearance.Box.Boundary.Lines.topOfBoundary
      numeratorClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.topOfBoundary
      denominatorClearance).toPathCertificate
  have leftIncreasing := Winding.Line.Quotient.lineQuotientFormula_of_clearances
    numerator denominator (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    proper.2
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      numeratorClearance).toPathCertificate
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      denominatorClearance).toPathCertificate
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }

end

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Quotient winding on a clear proper box is numerator winding minus denominator winding.

The identity uses the quadrupled winding convention. Summing the four oriented edge identities cancels all endpoint
corrections. -/
theorem rationalQuadrupledWinding_eq_sub_of_boundaryClearances
    (numerator denominator : CoefficientPolynomial) (box :
      Rational.Box)
    (proper : box.Proper)
    (numeratorClearance : BoundaryClearance numerator box)
    (denominatorClearance : BoundaryClearance denominator box) :
    Winding.Box.Basic.rationalQuadrupledWinding numerator denominator box =
      Winding.Box.Basic.quadrupledBoxWinding numerator box -
        Winding.Box.Basic.quadrupledBoxWinding denominator box := by
  let formula := boxQuotientFormula_of_boundaryClearances
    numerator denominator box proper numeratorClearance denominatorClearance
  have bottom := formula.bottom
  have right := formula.right
  have top := formula.top
  have left := formula.left
  unfold LineQuotientFormula Winding.Path.Correction.lineQuotientCorrection2
    at bottom right top left
  simp only [Rational.Affine.Axis.line_horizontal] at bottom top
  simp only [Rational.Affine.Axis.line_vertical] at right left
  rw [Winding.Box.Basic.rationalQuadrupledWinding_eq, Winding.Box.Basic.quadrupledBoxWinding_eq,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  simp only [Dense.Gaussian.Path.Box.Sides.horizontalEdge, Dense.Gaussian.Path.Box.Sides.verticalEdge]
  rw [bottom, right, top, left]
  ring1

end Purelib.RationalFunctions.Winding.Box.Quotient

end
