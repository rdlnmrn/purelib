module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Sign.CauchyComparison
import Purelib.Data.Rat.Sign.Jump
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Components.Nonzero
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.HalfPlane
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.Pair.ConjugateProduct
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

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

namespace Purelib.Polynomial.Winding.Polygon.Comparison

/-- Complete finite data comparing one source segment with one target
segment.  `LineData` contains the signed-remainder-chain product and
right-half-plane formulas; the endpoint facts justify conjugating the source
index. -/
structure SegmentHomotopyFormula
    (p q : CoefficientPolynomial)
    (sourceStart sourceFinish targetStart targetFinish : Gaussian.Basic.Canonical) : Prop where
  /-- The source polynomial is nonzero at the source segment's initial vertex. -/ sourceStartNonzero : p.eval
    sourceStart ≠ 0
  /-- The source polynomial is nonzero at the source segment's final vertex. -/ sourceFinishNonzero : p.eval
    sourceFinish ≠ 0
  /-- The synchronized coordinate pairs carry both the conjugate-product and half-plane formulas. -/ data :
    Dense.Rational.CauchyIndex.Comparison.Basic.LineData
    (Dense.Gaussian.Path.Components.pathReal p sourceStart (sourceFinish - sourceStart))
    (Dense.Gaussian.Path.Components.pathImag p sourceStart (sourceFinish - sourceStart))
    (Dense.Gaussian.Path.Components.pathReal q targetStart (targetFinish - targetStart))
    (Dense.Gaussian.Path.Components.pathImag q targetStart (targetFinish - targetStart)) 0 1

/-- One synchronized Rouché segment changes raw winding only by the
difference of its two displayed endpoint corrections. -/
theorem segmentRaw_eq_of_homotopy
    {p q : CoefficientPolynomial}
    {sourceStart sourceFinish targetStart targetFinish : Gaussian.Basic.Canonical}
    (formula : SegmentHomotopyFormula p q
      sourceStart sourceFinish targetStart targetFinish) :
    (Dense.Gaussian.Path.Segment.segment q targetStart targetFinish).doubledWinding =
      (Dense.Gaussian.Path.Segment.segment p sourceStart sourceFinish).doubledWinding +
        Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
          (p.eval sourceStart) (q.eval targetStart) -
        Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
          (p.eval sourceFinish) (q.eval targetFinish) := open Purelib in by
  have sourceStartPair :=
    Dense.Gaussian.Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p
      sourceStart (sourceFinish - sourceStart) 0 (by
        simpa only [Affine.Segment.line_segment_zero] using formula.sourceStartNonzero)
  have sourceFinishPair :=
    Dense.Gaussian.Path.Components.Nonzero.ofLine_coordinatePair_ne_zero p
      sourceStart (sourceFinish - sourceStart) 1 (by
        simpa only [Affine.Segment.line_segment_one] using formula.sourceFinishNonzero)
  have conjugate := Dense.Rational.CauchyIndex.Basic.cauchyIndex2_neg_denominator
    sourceStartPair sourceFinishPair
  have half := formula.data.halfPlane
  have product := formula.data.product
  unfold Dense.Rational.CauchyIndex.HalfPlane.Formula at half
  unfold Dense.Rational.CauchyIndex.Product.Basic.AuxiliaryProductFormula
    Dense.Rational.CauchyIndex.Product.Basic.auxiliaryEndpointCorrection2 at product
  simp only [Dense.Rational.Pair.ConjugateProduct.eval_roucheReal,
    Dense.Rational.Pair.ConjugateProduct.eval_roucheImag, Dense.Basic.DensePolynomial.eval_neg,
    Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
      Affine.Segment.line_segment_zero,
    Affine.Segment.line_segment_one] at half product
  rw [conjugate] at product
  unfold Dense.Gaussian.Path.Segment.segment Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding
    Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
  dsimp only [Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine]
  have targetIdentity :
      Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
          (Dense.Gaussian.Path.Components.pathReal q targetStart (targetFinish - targetStart))
          (Dense.Gaussian.Path.Components.pathImag q targetStart (targetFinish - targetStart)) 0 1 =
        Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
            (Dense.Gaussian.Path.Components.pathReal p sourceStart (sourceFinish - sourceStart))
            (Dense.Gaussian.Path.Components.pathImag p sourceStart (sourceFinish - sourceStart)) 0 1 +
          Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
            (Dense.Rational.Pair.ConjugateProduct.roucheReal
              (Dense.Gaussian.Path.Components.pathReal p sourceStart (sourceFinish - sourceStart))
              (Dense.Gaussian.Path.Components.pathImag p sourceStart (sourceFinish - sourceStart))
              (Dense.Gaussian.Path.Components.pathReal q targetStart (targetFinish - targetStart))
              (Dense.Gaussian.Path.Components.pathImag q targetStart (targetFinish - targetStart)))
            (Dense.Rational.Pair.ConjugateProduct.roucheImag
              (Dense.Gaussian.Path.Components.pathReal p sourceStart (sourceFinish - sourceStart))
              (Dense.Gaussian.Path.Components.pathImag p sourceStart (sourceFinish - sourceStart))
              (Dense.Gaussian.Path.Components.pathReal q targetStart (targetFinish - targetStart))
              (Dense.Gaussian.Path.Components.pathImag q targetStart (targetFinish - targetStart))) 0 1 +
          (Data.Rat.Sign.Jump.signJump 1
            (((p.eval sourceStart).re * (q.eval targetStart).im -
              (p.eval sourceStart).im * (q.eval targetStart).re) *
              (-(p.eval sourceStart).im * (q.eval targetStart).im)) : Int) -
          (Data.Rat.Sign.Jump.signJump 1
            (((p.eval sourceFinish).re * (q.eval targetFinish).im -
              (p.eval sourceFinish).im * (q.eval targetFinish).re) *
              (-(p.eval sourceFinish).im * (q.eval targetFinish).im)) : Int) := by
    rw [product]
    ring1
  rw [targetIdentity, half]
  ring1

/-- Synchronized segment formulas for two open chains with the same finite
number of edges. -/
inductive ChainHomotopyFormula (p q :
  CoefficientPolynomial) :
    Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical → Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical
      → Prop
  /-- Two empty chains carry the trivial synchronized comparison. -/ | nil (sourceStart targetStart :
    Gaussian.Basic.Canonical) :
      ChainHomotopyFormula p q sourceStart [] targetStart []
  /-- Prepend one certified synchronized segment to the comparison of the remaining chains. -/ | cons
      {sourceStart sourceFinish targetStart targetFinish : Gaussian.Basic.Canonical}
      {sourceRemaining targetRemaining : List Gaussian.Basic.Canonical}
      (edge : SegmentHomotopyFormula p q
        sourceStart sourceFinish targetStart targetFinish)
      (tail : ChainHomotopyFormula p q
        sourceFinish sourceRemaining targetFinish targetRemaining) :
      ChainHomotopyFormula p q
        sourceStart (sourceFinish :: sourceRemaining)
        targetStart (targetFinish :: targetRemaining)

/-- Concatenate synchronized finite homotopies at their explicitly displayed
terminal vertices. -/
theorem ChainHomotopyFormula.append
    {p q : CoefficientPolynomial} :
    ∀ {sourceStart targetStart : Gaussian.Basic.Canonical}
      {sourceVertices targetVertices sourceRemaining targetRemaining :
        List Gaussian.Basic.Canonical},
      ChainHomotopyFormula p q sourceStart sourceVertices
          targetStart targetVertices →
        ChainHomotopyFormula p q
          (Polygon.Chain.terminal sourceStart sourceVertices) sourceRemaining
          (Polygon.Chain.terminal targetStart targetVertices) targetRemaining →
        ChainHomotopyFormula p q sourceStart
          (sourceVertices ++ sourceRemaining) targetStart
          (targetVertices ++ targetRemaining)
  | _, _, [], [], _, _, .nil _ _, tail => tail
  | _, _, _ :: _, _ :: _, _, _, .cons edge remaining, tail =>
      .cons edge (remaining.append tail)

/-- Open synchronized chains retain the two uncancelled endpoint
corrections. -/
theorem chainRaw_eq_of_homotopy
    (p q : CoefficientPolynomial) :
    ∀ (sourceStart : Gaussian.Basic.Canonical) (sourceVertices : List Gaussian.Basic.Canonical)
      (targetStart : Gaussian.Basic.Canonical) (targetVertices : List Gaussian.Basic.Canonical),
      ChainHomotopyFormula p q sourceStart sourceVertices
        targetStart targetVertices →
      Winding.Polygon.Basic.chainRaw q targetStart targetVertices =
        Winding.Polygon.Basic.chainRaw p sourceStart sourceVertices +
          Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
            (p.eval sourceStart) (q.eval targetStart) -
          Gaussian.Sign.CauchyComparison.vertexHomotopyCorrection2
            (p.eval (Polygon.Chain.terminal sourceStart sourceVertices))
            (q.eval (Polygon.Chain.terminal targetStart targetVertices))
  | sourceStart, [], targetStart, [], .nil _ _ => by
      simp only [Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      ring1
  | sourceStart, sourceFinish :: sourceRemaining,
      targetStart, targetFinish :: targetRemaining, .cons edge tail => by
      have edgeFormula := segmentRaw_eq_of_homotopy edge
      have tailFormula := chainRaw_eq_of_homotopy p q
        sourceFinish sourceRemaining targetFinish targetRemaining tail
      simp only [Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      rw [edgeFormula, tailFormula]
      ring1

/-- Synchronized formulas for two explicitly closed finite polygons. -/
abbrev ClosedHomotopyFormula
    (p q : CoefficientPolynomial)
    (sourceBase : Gaussian.Basic.Canonical) (sourceVertices : List Gaussian.Basic.Canonical)
    (targetBase : Gaussian.Basic.Canonical) (targetVertices : List Gaussian.Basic.Canonical) :=
  ChainHomotopyFormula p q
    sourceBase (sourceVertices ++ [sourceBase])
    targetBase (targetVertices ++ [targetBase])

/-- All endpoint corrections telescope when both synchronized chains close. -/
theorem closedRaw_eq_of_homotopy
    (p q : CoefficientPolynomial)
    (sourceBase : Gaussian.Basic.Canonical) (sourceVertices : List Gaussian.Basic.Canonical)
    (targetBase : Gaussian.Basic.Canonical) (targetVertices : List Gaussian.Basic.Canonical)
    (formula : ClosedHomotopyFormula p q
      sourceBase sourceVertices targetBase targetVertices) :
    Winding.Polygon.Basic.closedRaw q targetBase targetVertices =
      Winding.Polygon.Basic.closedRaw p sourceBase sourceVertices := by
  unfold Winding.Polygon.Basic.closedRaw
  rw [chainRaw_eq_of_homotopy p q
    sourceBase (sourceVertices ++ [sourceBase])
    targetBase (targetVertices ++ [targetBase]) formula,
    Polygon.Chain.terminal_append_singleton, Polygon.Chain.terminal_append_singleton]
  ring1
end Purelib.Polynomial.Winding.Polygon.Comparison

end
