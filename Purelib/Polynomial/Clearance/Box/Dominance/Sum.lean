module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
public import Purelib.Polynomial.Clearance.Box.Dominance.Path
public import Purelib.Polynomial.Clearance.Box.Dominance.Uniform
public import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

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

namespace Purelib.Polynomial.Clearance.Box.Dominance.Sum

/-- One finite norm margin constructs boundary clearance for the sum on all
four sides, with no root search or coprimality inference. -/
def boundaryClearance_add_of_boundaryNormDominance
    (p q : CoefficientPolynomial) (box : Box) (proper :
      box.Proper)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box) :
    BoundaryClearance (p + q) box := by
  let bottomCertificate := Clearance.Box.Dominance.Path.sumCertificate_of_boundaryNormDominance
    p q box dominance (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
    proper.1.le (by
      intro t inside
      rw [Affine.Axis.line_horizontal]
      exact ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
        Or.inr (Or.inr (Or.inl rfl))⟩)
  let rightCertificate := Clearance.Box.Dominance.Path.sumCertificate_of_boundaryNormDominance
    p q box dominance (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
    proper.2.le (by
      intro t inside
      rw [Affine.Axis.line_vertical]
      exact ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
        Or.inr (Or.inl rfl)⟩)
  let topCertificate := Clearance.Box.Dominance.Path.sumCertificate_of_boundaryNormDominance
    p q box dominance (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    proper.1.le (by
      intro t inside
      rw [Affine.Axis.line_horizontal]
      exact ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
        Or.inr (Or.inr (Or.inr rfl))⟩)
  let leftCertificate := Clearance.Box.Dominance.Path.sumCertificate_of_boundaryNormDominance
    p q box dominance (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    proper.2.le (by
      intro t inside
      rw [Affine.Axis.line_vertical]
      exact ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  exact Clearance.Box.Boundary.Lines.boundaryOfLines
    (Clearance.Box.Line.Path.verticalOfPathCertificate
      (p + q) box box.xLower leftCertificate)
    (Clearance.Box.Line.Path.verticalOfPathCertificate
      (p + q) box box.xUpper rightCertificate)
    (Clearance.Box.Line.Path.horizontalOfPathCertificate
      (p + q) box box.yLower bottomCertificate)
    (Clearance.Box.Line.Path.horizontalOfPathCertificate
      (p + q) box box.yUpper topCertificate)
end Purelib.Polynomial.Clearance.Box.Dominance.Sum

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

namespace Purelib.Polynomial.Clearance.Box.Dominance.Sum
open Purelib.Data.Gaussian

/-- The same finite coefficient estimate constructs a boundary-clearance
certificate for the perturbed polynomial. -/
def boundaryClearance_add_of_uniformBound
    (base perturbation : CoefficientPolynomial) (box : Box)
    (proper : box.Proper)
    (clearance : BoundaryClearance base box)
    (bound : Fraction.Rational)
    (strict : bound < clearance.bound)
    (uniform : ∀ z : Gaussian.Basic.Canonical, Box.Boundary.OnBoxBoundary box z →
      Gaussian.Basic.Canonical.normSq (perturbation.eval z) ≤ bound) :
    BoundaryClearance (base + perturbation) box :=
  boundaryClearance_add_of_boundaryNormDominance
    base perturbation box proper
      (Clearance.Box.Dominance.Uniform.boundaryNormDominanceOfUniformBound base perturbation box clearance
        bound strict uniform)

end Purelib.Polynomial.Clearance.Box.Dominance.Sum

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

namespace Purelib.Polynomial.Clearance.Box.Dominance.Sum

/-- Exact four-side minimum stored by a boundary-dominance clearance. -/
@[simp] theorem
  boundaryClearance_add_of_boundaryNormDominance_bound
    (p q : CoefficientPolynomial) (box : Box) (proper :
      box.Proper)
    (dominance : Clearance.Box.Dominance.Basic.BoundaryNormDominance p q box) :
    (boundaryClearance_add_of_boundaryNormDominance
      p q box proper dominance).bound =
      min
        (dominance.margin ^ 2 /
          (4 * Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant p (Gaussian.Cast.Winding.verticalBase
            box.xLower)
            Gaussian.Constants.imaginaryUnit ⟨box.yLower, box.yUpper, box.y_valid⟩))
        (min
          (dominance.margin ^ 2 /
            (4 * Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant p (Gaussian.Cast.Winding.verticalBase
              box.xUpper)
              Gaussian.Constants.imaginaryUnit ⟨box.yLower, box.yUpper, box.y_valid⟩))
          (min
            (dominance.margin ^ 2 /
              (4 * Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant p (Gaussian.Cast.Imaginary.horizontalBase
                box.yLower)
                Gaussian.Constants.horizontalDirection
                ⟨box.xLower, box.xUpper, box.x_valid⟩))
            (dominance.margin ^ 2 /
              (4 * Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant p (Gaussian.Cast.Imaginary.horizontalBase
                box.yUpper)
                Gaussian.Constants.horizontalDirection
                ⟨box.xLower, box.xUpper, box.x_valid⟩)))) := by
  rfl
end Purelib.Polynomial.Clearance.Box.Dominance.Sum

end

end
