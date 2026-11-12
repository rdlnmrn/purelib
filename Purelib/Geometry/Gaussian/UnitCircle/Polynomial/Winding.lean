module

public import Purelib.Geometry.Gaussian.UnitCircle.Polynomial
public import Purelib.Polynomial.Winding.Edge.Product
import Purelib.Polynomial.Winding.Edge.Constant
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Multiplication.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Geometry.Rational.Affine
import Purelib.Tactic.Ring

/-! # Winding of the joined polynomial quarter circuit

The finite Cauchy-index algorithm computes the four actual cubic edges.
Multiplication by an arbitrary nonzero Gaussian displacement preserves their
closed sum: the original local product formula retains both endpoint
corrections, and the literal quarter joins cancel them in order.
-/

public section

namespace Purelib.Geometry.Gaussian.UnitCircle.Polynomial

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Winding.Edge
open Purelib.Geometry.Rational
open Quarter (UnitCircuitQuarter)

/-- The original finite edge algorithm computes raw closed winding four for the actual joined cubic quarters. -/
theorem winding :
    (edge .first).doubledWinding + (edge .second).doubledWinding +
      (edge .third).doubledWinding + (edge .fourth).doubledWinding = 4 := by
  decide +kernel

/-- Dividing the SAME actual closed polynomial index sum by four gives ordinary winding one. -/
theorem winding_one :
    ((edge .first).doubledWinding + (edge .second).doubledWinding +
      (edge .third).doubledWinding + (edge .fourth).doubledWinding) / 4 = 1 :=
  (congrArg (fun value : Int => value / 4) winding).trans (by decide +kernel : (4 : Int) / 4 = 1)

/-- The retained four-edge list has the same original finite winding sum. -/
theorem edges_winding : (edges.map PolynomialEdge.doubledWinding).sum = 4 := by
  simp only [edges, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  calc
    _ = (edge .first).doubledWinding + (edge .second).doubledWinding +
        (edge .third).doubledWinding + (edge .fourth).doubledWinding := by ring1
    _ = 4 := winding

/-- Multiply one original polynomial quarter by the given Gaussian displacement. -/
@[expose] def scaledPolynomial (factor : Canonical) (quarter : UnitCircuitQuarter) : CoefficientPolynomial :=
  Constants.gaussianConstant factor * polynomial quarter

/-- The original polynomial point scaled by the same retained Gaussian displacement. -/
theorem scaledPolynomial_eval (factor : Canonical) (quarter : UnitCircuitQuarter) (time : Fraction.Rational) :
    (scaledPolynomial factor quarter).eval (Affine.line 0 1 time) = factor * point quarter time := by
  unfold scaledPolynomial
  rewrite [DensePolynomial.eval_mul, Constants.gaussianConstant_eval]
  rfl

/-- The actual displaced quarter retains its original orientation and ordered unit-interval endpoints. -/
@[expose] def scaledEdge (factor : Canonical) (quarter : UnitCircuitQuarter) : PolynomialEdge :=
  PolynomialEdge.ofLine (scaledPolynomial factor quarter) 0 1 0 1

/-- The same original constant factor has positive uniform clearance on the retained unit interval. -/
private def constantClearance (factor : Canonical) (nonzero : factor ≠ 0) :
    Certificate
      (Path.Components.pathReal (Constants.gaussianConstant factor) 0 1)
      (Path.Components.pathImag (Constants.gaussianConstant factor) 0 1) ⟨0, 1, by decide +kernel⟩ :=
  { bound := Norm.Basic.normSq factor
    positive := Norm.Basic.normSq_pos nonzero
    lower := fun time _ => by
      rewrite [Path.Components.eval_pathReal, Path.Components.eval_pathImag, Constants.gaussianConstant_eval]
      exact Fraction.Order.Basic.le_refl _ }

/-- A nonzero given displacement preserves each actual point's nonzero certificate. -/
theorem scaledPolynomial_ne_zero (factor : Canonical) (nonzero : factor ≠ 0)
    (quarter : UnitCircuitQuarter) {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) :
    (scaledPolynomial factor quarter).eval (Affine.line 0 1 time) ≠ 0 := by
  rewrite [scaledPolynomial_eval]
  exact Field.mul_ne_zero_direct nonzero (point_ne_zero quarter inside)

/-- The original local winding product formula retains both actual endpoint corrections for the displaced quarter. -/
theorem scaledEdge_winding (factor : Canonical) (nonzero : factor ≠ 0) (quarter : UnitCircuitQuarter) :
    (scaledEdge factor quarter).doubledWinding = (edge quarter).doubledWinding -
      (Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial quarter) 0 1 0 : Int) +
      Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial quarter) 0 1 1 := by
  have actual := Product.lineProductFormula_of_clearances
    (Constants.gaussianConstant factor) (polynomial quarter) 0 1
    (by decide +kernel : (0 : Fraction.Rational) < 1)
    (constantClearance factor nonzero) (clearance quarter)
    (by rewrite [Constants.gaussianConstant_eval]; exact nonzero)
    (point_ne_zero quarter ⟨Fraction.Order.Basic.le_refl 0, by decide +kernel⟩)
    (by rewrite [Constants.gaussianConstant_eval]; exact nonzero)
    (point_ne_zero quarter ⟨by decide +kernel, Fraction.Order.Basic.le_refl 1⟩)
  change (scaledEdge factor quarter).doubledWinding =
    (PolynomialEdge.ofLine (Constants.gaussianConstant factor) 0 1 0 1).doubledWinding +
      (edge quarter).doubledWinding -
      (Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial quarter) 0 1 0 : Int) +
      Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial quarter) 0 1 1 at actual
  rewrite [Constant.gaussianConstant_edge_winding_zero nonzero] at actual
  exact actual.trans (by ring1)

/-- Equal actual polynomial endpoint values identify the original correction for both unchanged polynomials. -/
private theorem correction_eq (factor : Canonical) (firstQuarter lastQuarter : UnitCircuitQuarter)
    (joined : point firstQuarter 1 = point lastQuarter 0) :
    Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial firstQuarter) 0 1 1 =
      Product.lineProductCorrection2 (Constants.gaussianConstant factor) (polynomial lastQuarter) 0 1 0 := by
  unfold Product.lineProductCorrection2 Product.vertexProductCorrection2
  rewrite [Constants.gaussianConstant_eval, Constants.gaussianConstant_eval]
  change Purelib.Data.Rat.Sign.Jump.signJump 1
      ((factor * point firstQuarter 1).im * factor.im * (point firstQuarter 1).im) =
    Purelib.Data.Rat.Sign.Jump.signJump 1
      ((factor * point lastQuarter 0).im * factor.im * (point lastQuarter 0).im)
  rewrite [joined]
  rfl

/-- Multiplication by the same nonzero displacement preserves the closed winding of all four actual joined arcs. -/
theorem scaled_winding (factor : Canonical) (nonzero : factor ≠ 0) :
    (scaledEdge factor .first).doubledWinding + (scaledEdge factor .second).doubledWinding +
      (scaledEdge factor .third).doubledWinding + (scaledEdge factor .fourth).doubledWinding = 4 := by
  rewrite [scaledEdge_winding factor nonzero .first, scaledEdge_winding factor nonzero .second,
    scaledEdge_winding factor nonzero .third, scaledEdge_winding factor nonzero .fourth,
    correction_eq factor .first .second points_join.1,
    correction_eq factor .second .third points_join.2.1,
    correction_eq factor .third .fourth points_join.2.2.1,
    correction_eq factor .fourth .first points_join.2.2.2]
  calc
    _ = (edge .first).doubledWinding + (edge .second).doubledWinding +
        (edge .third).doubledWinding + (edge .fourth).doubledWinding := by ring1
    _ = 4 := winding

end Purelib.Geometry.Gaussian.UnitCircle.Polynomial

end
