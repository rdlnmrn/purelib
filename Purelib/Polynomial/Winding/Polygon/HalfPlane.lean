module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Sign.Jump
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace Purelib.Polynomial.Winding.Polygon.HalfPlane

/-! ## Open half-plane chains -/

/-- The endpoint quadrant correction in the right-half-plane formula. -/
def vertexHalfPlaneCorrection2 (p :
  CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) : Nat :=
  Data.Rat.Sign.Jump.signJump 1 ((p.eval point).re * (p.eval point).im)

/-- One right-half-plane formula for every edge of an open polygonal
chain. -/
inductive ChainHalfPlaneFormula (p :
  CoefficientPolynomial) :
    Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical → Prop
  /-- The empty chain carries no edge obligations. -/ | nil (start : Gaussian.Basic.Canonical) :
    ChainHalfPlaneFormula p start []
  /-- Prepend one certified half-plane edge to the remaining chain. -/ | cons {start finish : Gaussian.Basic.Canonical}
    {remaining : List Gaussian.Basic.Canonical}
      (edge : Dense.Rational.CauchyIndex.HalfPlane.Formula
        (Dense.Gaussian.Path.Components.pathReal p start (finish - start))
        (Dense.Gaussian.Path.Components.pathImag p start (finish - start)) 0 1)
      (tail : ChainHalfPlaneFormula p finish remaining) :
      ChainHalfPlaneFormula p start (finish :: remaining)

/-- Concatenate half-plane formula chains at their shared terminal vertex. -/
theorem ChainHalfPlaneFormula.append
    {p : CoefficientPolynomial} :
    ∀ {start : Gaussian.Basic.Canonical} {vertices remaining : List Gaussian.Basic.Canonical},
      ChainHalfPlaneFormula p start vertices →
        ChainHalfPlaneFormula p (Polygon.Chain.terminal start vertices) remaining →
        ChainHalfPlaneFormula p start (vertices ++ remaining)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons edge rest, tail =>
      .cons edge (rest.append tail)

/-- Half-plane edge formulas telescope to the two endpoint quadrant
corrections of an open chain. -/
theorem chainRaw_eq_endpoint_corrections_of_halfPlane
    (p : CoefficientPolynomial) :
    ∀ (start : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical),
      ChainHalfPlaneFormula p start vertices →
        Winding.Polygon.Basic.chainRaw p start vertices =
          (vertexHalfPlaneCorrection2 p start : Int) -
            vertexHalfPlaneCorrection2 p (Polygon.Chain.terminal start vertices)
  | start, [], .nil _ => by
      simp only [Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      ring1
  | start, finish :: remaining, .cons edge tail => by
      have tailIdentity :=
        chainRaw_eq_endpoint_corrections_of_halfPlane p finish remaining
          tail
      unfold Dense.Rational.CauchyIndex.HalfPlane.Formula at edge
      simp only [Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal, Dense.Gaussian.Path.Segment.segment,
        Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding]
      dsimp only [Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine] at edge ⊢
      simp only [Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
        Affine.Segment.line_segment_zero,
        Affine.Segment.line_segment_one] at edge
      unfold vertexHalfPlaneCorrection2 at tailIdentity ⊢
      rw [edge, tailIdentity]
      ring1

/-- A closed finite polygon retained in the open right half-plane has raw
winding zero. -/
theorem closedRaw_eq_zero_of_halfPlane
    (p : CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical)
    (formula : ChainHalfPlaneFormula p base (vertices ++ [base])) :
    Winding.Polygon.Basic.closedRaw p base vertices = 0 := by
  unfold Winding.Polygon.Basic.closedRaw
  rw [chainRaw_eq_endpoint_corrections_of_halfPlane p base
    (vertices ++ [base]) formula, Polygon.Chain.terminal_append_singleton]
  ring1
end Purelib.Polynomial.Winding.Polygon.HalfPlane

end
