module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Tactic.Ring
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

namespace Purelib.Polynomial.Winding.Box.HalfPlane

/-- A polynomial path contained in the open right half-plane has zero raw
winding around a positively oriented constructive box. -/
theorem quadrupledBoxWinding_eq_zero_of_positive_real
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (box : Box)
    (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box)
    (realPositive : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary box z →
        0 < (p.eval z).re) :
    Winding.Box.Basic.quadrupledBoxWinding p box = 0 := by
  have bottom := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real
    (Clearance.Box.Boundary.Lines.bottomOfBoundary
      clearance).toPathCertificate proper.1 (by
        intro x inside
        rw [Dense.Gaussian.Path.Components.eval_pathReal, Affine.Axis.line_horizontal]
        exact realPositive (Gaussian.Basic.point x box.yLower)
          ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
            Or.inr (Or.inr (Or.inl rfl))⟩)
  have right := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real
    (Clearance.Box.Boundary.Lines.rightOfBoundary
      clearance).toPathCertificate proper.2 (by
        intro y inside
        rw [Dense.Gaussian.Path.Components.eval_pathReal, Affine.Axis.line_vertical]
        exact realPositive (Gaussian.Basic.point box.xUpper y)
          ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
            Or.inr (Or.inl rfl)⟩)
  have topIncreasing := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real
    (Clearance.Box.Boundary.Lines.topOfBoundary
      clearance).toPathCertificate proper.1 (by
        intro x inside
        rw [Dense.Gaussian.Path.Components.eval_pathReal, Affine.Axis.line_horizontal]
        exact realPositive (Gaussian.Basic.point x box.yUpper)
          ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
            Or.inr (Or.inr (Or.inr rfl))⟩)
  have leftIncreasing := Dense.Rational.CauchyIndex.HalfPlane.formula_of_positive_real
    (Clearance.Box.Boundary.Lines.leftOfBoundary
      clearance).toPathCertificate proper.2 (by
        intro y inside
        rw [Dense.Gaussian.Path.Components.eval_pathReal, Affine.Axis.line_vertical]
        exact realPositive (Gaussian.Basic.point box.xLower y)
          ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  have top := topIncreasing.reverse
  have left := leftIncreasing.reverse
  unfold Dense.Rational.CauchyIndex.HalfPlane.Formula at bottom right top left
  simp only [Dense.Gaussian.Path.Components.eval_pathReal,
    Dense.Gaussian.Path.Components.eval_pathImag,
    Affine.Axis.line_horizontal] at bottom top
  simp only [Dense.Gaussian.Path.Components.eval_pathReal,
    Dense.Gaussian.Path.Components.eval_pathImag,
    Affine.Axis.line_vertical] at right left
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  simp only [Dense.Gaussian.Path.Box.Sides.horizontalEdge, Dense.Gaussian.Path.Box.Sides.verticalEdge,
    Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding, Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine]
  rw [bottom, right, top, left]
  ring1

end Purelib.Polynomial.Winding.Box.HalfPlane

end
