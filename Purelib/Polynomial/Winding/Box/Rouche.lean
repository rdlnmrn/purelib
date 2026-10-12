module
import Purelib.Polynomial.Clearance.Box.Line.Path

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Int.Telescope.Four
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Uniform
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
public import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Edge.Rouche
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Winding.Edge.Rouche (PolynomialLineData)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche

/-- Four finite Rouché records in positive box-boundary orientation. -/
structure BoxData
    (p q : CoefficientPolynomial) (box : Box) : Prop where
  /-- The finite perturbation comparison on the bottom side, oriented left to right. -/ bottom :
    PolynomialLineData p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
    box.xLower box.xUpper
  /-- The finite perturbation comparison on the right side, oriented bottom to top. -/ right :
    PolynomialLineData p q
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
    box.yLower box.yUpper
  /-- The finite perturbation comparison on the top side, oriented right to left. -/ top :
    PolynomialLineData p q
    (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    box.xUpper box.xLower
  /-- The finite perturbation comparison on the left side, oriented top to bottom. -/ left :
    PolynomialLineData p q
    (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    box.yUpper box.yLower
end Purelib.Polynomial.Winding.Box.Rouche

end

end

section
section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche

/-- Boundary clearances for the dominant path and its sum, together with one
strict norm margin, construct all four finite Rouché records. -/
theorem boxData_of_boundaryNormDominance
    (p q : CoefficientPolynomial) (box : Box) (proper :
      box.Proper)
    (pClearance : BoundaryClearance p box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box) :
    BoxData p q box := by
  have bottom := Winding.Edge.Rouche.lineData_of_boundaryNormDominance p q box dominance
    (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection proper.1
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [Affine.Axis.line_horizontal]
        exact ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩)
  have right := Winding.Edge.Rouche.lineData_of_boundaryNormDominance p q box dominance
    (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit proper.2
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [Affine.Axis.line_vertical]
        exact ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
          Or.inr (Or.inl rfl)⟩)
  have topIncreasing := Winding.Edge.Rouche.lineData_of_boundaryNormDominance p q box dominance
    (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection proper.1
    (Clearance.Box.Boundary.Lines.topOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [Affine.Axis.line_horizontal]
        exact ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩)
  have leftIncreasing := Winding.Edge.Rouche.lineData_of_boundaryNormDominance p q box dominance
    (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit proper.2
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      pClearance).toPathCertificate (by
        intro t inside
        rw [Affine.Axis.line_vertical]
        exact ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  exact
    { bottom := bottom
      right := right
      top := topIncreasing.reverse
      left := leftIncreasing.reverse }
end Purelib.Polynomial.Winding.Box.Rouche

end

end

section
section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche

/-- The four finite Rouché records telescope to equality of the two raw box
windings. -/
theorem quadrupledBoxWinding_add_of_data
    (p q : CoefficientPolynomial) (box : Box)
    (pClearance : BoundaryClearance p box)
    (data : BoxData p q box) :
    Winding.Box.Basic.quadrupledBoxWinding (p + q) box = Winding.Box.Basic.quadrupledBoxWinding p box := open Purelib in
      by
  let bottomClearance :=
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      pClearance).toPathCertificate
  let rightClearance :=
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      pClearance).toPathCertificate
  let topClearance :=
    (Clearance.Box.Boundary.Lines.topOfBoundary
      pClearance).toPathCertificate
  let leftClearance :=
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      pClearance).toPathCertificate
  have bottomStart := bottomClearance.eval_ne_zero
    (x := box.xLower) ⟨le_rfl, box.x_valid⟩
  have bottomStop := bottomClearance.eval_ne_zero
    (x := box.xUpper) ⟨box.x_valid, le_rfl⟩
  have rightStart := rightClearance.eval_ne_zero
    (x := box.yLower) ⟨le_rfl, box.y_valid⟩
  have rightStop := rightClearance.eval_ne_zero
    (x := box.yUpper) ⟨box.y_valid, le_rfl⟩
  have topStart := topClearance.eval_ne_zero
    (x := box.xUpper) ⟨box.x_valid, le_rfl⟩
  have topStop := topClearance.eval_ne_zero
    (x := box.xLower) ⟨le_rfl, box.x_valid⟩
  have leftStart := leftClearance.eval_ne_zero
    (x := box.yUpper) ⟨box.y_valid, le_rfl⟩
  have leftStop := leftClearance.eval_ne_zero
    (x := box.yLower) ⟨le_rfl, box.y_valid⟩
  have bottomConjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    bottomStart bottomStop
  have rightConjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    rightStart rightStop
  have topConjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    topStart topStop
  have leftConjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    leftStart leftStop
  have bottomHalf := data.bottom.halfPlane
  have rightHalf := data.right.halfPlane
  have topHalf := data.top.halfPlane
  have leftHalf := data.left.halfPlane
  have bottomProduct := data.bottom.product
  have rightProduct := data.right.product
  have topProduct := data.top.product
  have leftProduct := data.left.product
  unfold Dense.Rational.CauchyIndex.HalfPlane.Formula at bottomHalf rightHalf topHalf leftHalf
  unfold Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula
    Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2
    at bottomProduct rightProduct topProduct leftProduct
  simp only [Dense.Rational.Pair.ConjugateProduct.eval_roucheReal, Dense.Rational.Pair.ConjugateProduct.eval_roucheImag,
    Dense.Basic.DensePolynomial.eval_neg,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Affine.Axis.line_horizontal] at bottomHalf topHalf bottomProduct topProduct
  simp only [Dense.Rational.Pair.ConjugateProduct.eval_roucheReal, Dense.Rational.Pair.ConjugateProduct.eval_roucheImag,
    Dense.Basic.DensePolynomial.eval_neg,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Affine.Axis.line_vertical] at rightHalf leftHalf rightProduct leftProduct
  rw [bottomConjugate] at bottomProduct
  rw [rightConjugate] at rightProduct
  rw [topConjugate] at topProduct
  rw [leftConjugate] at leftProduct
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq, Winding.Box.Basic.quadrupledBoxWinding_eq]
  simp only [Dense.Gaussian.Path.Box.Sides.horizontalEdge, Dense.Gaussian.Path.Box.Sides.verticalEdge,
    Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding, Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine]
  exact Purelib.Data.Int.Telescope.Four.fourEdgeRoucheTelescope bottomProduct rightProduct topProduct
    leftProduct bottomHalf rightHalf topHalf leftHalf
end Purelib.Polynomial.Winding.Box.Rouche

end

end

section
section
@[expose] public section

/-!
# Choice-free finite winding transfer under boundary dominance

The pointwise conjugate of a polynomial value is represented only along one
displayed affine path, as the coordinate pair `(A,-B)`.  It is never promoted
to a global polynomial in the complex variable.  Finite Cauchy-product cells
then compare that conjugate path with the sum path, while the constructive
half-plane theorem makes their product contribution telescope on a box.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche

/-- Finite constructive Rouché transfer on one box boundary. -/
theorem quadrupledBoxWinding_add_of_boundaryNormDominance
    (p q : CoefficientPolynomial) (box : Box) (proper :
      box.Proper)
    (pClearance : BoundaryClearance p box)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box) :
    Winding.Box.Basic.quadrupledBoxWinding (p + q) box = Winding.Box.Basic.quadrupledBoxWinding p box :=
  quadrupledBoxWinding_add_of_data p q box pClearance
    (boxData_of_boundaryNormDominance p q box proper
      pClearance dominance)

end Purelib.Polynomial.Winding.Box.Rouche

end

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.Polynomial.Winding.Box.Rouche
open Purelib.Data.Gaussian

/-- Constructive Rouché transfer preserves the exact quadrupled winding of
the displayed box. -/
theorem quadrupledBoxWinding_add_eq_of_uniformBound
    (base perturbation : CoefficientPolynomial) (box : Box)
    (proper : box.Proper)
    (clearance : BoundaryClearance base box)
    (bound : Fraction.Rational)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian.Basic.Canonical, Box.Boundary.OnBoxBoundary box z →
      Gaussian.Basic.Canonical.normSq (perturbation.eval z) ≤ bound) :
    Winding.Box.Basic.quadrupledBoxWinding (base + perturbation) box =
      Winding.Box.Basic.quadrupledBoxWinding base box :=
  quadrupledBoxWinding_add_of_boundaryNormDominance
    base perturbation box proper clearance
    (Clearance.Box.Dominance.Uniform.boundaryNormDominanceOfUniformBound base perturbation box clearance
        bound strict uniform)

end Purelib.Polynomial.Winding.Box.Rouche

end
