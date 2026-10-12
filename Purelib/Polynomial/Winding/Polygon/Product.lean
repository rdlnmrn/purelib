module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
public import Purelib.Polynomial.Winding.Edge.Product
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Tactic.Ring

/-!
# Product corrections along polygonal chains

Each edge retains its supplied polynomial product identity. Integer endpoint
corrections telescope at the actual shared vertices and cancel on returning to
the retained base vertex.
-/

namespace Purelib.Polynomial.Winding.Polygon.Product

open Purelib
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-! ## Products on a closed walk -/

/-- One existing finite affine product certificate for every segment of an
open polygonal chain.

Every constructor retains the displayed affine edge product identity and the certificates for its ordered tail. The
empty chain has no edge obligations. -/
public inductive ChainProductFormula (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical → Prop
  /-- The empty chain requires no edge product certificates. -/ | nil (start : Gaussian.Basic.Canonical) :
    Purelib.Polynomial.Winding.Polygon.Product.ChainProductFormula p q start []
  /-- Retain the first edge's product identity and the remaining chain's certificates. -/ | cons {start finish :
    Gaussian.Basic.Canonical} {remaining : List Gaussian.Basic.Canonical}
      (edge : Winding.Edge.Product.LineProductFormula p q
        start (finish - start) 0 1)
      (tail : Purelib.Polynomial.Winding.Polygon.Product.ChainProductFormula p q finish remaining) :
      Purelib.Polynomial.Winding.Polygon.Product.ChainProductFormula p q start (finish :: remaining)

/-- Append edge product certificates along two consecutive polygonal chains.

The second certificate begins at the actual terminal vertex of the first chain. Recursion retains each edge identity in
the same concatenated order. -/
public theorem ChainProductFormula.append
    {p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
    ∀ {start : Gaussian.Basic.Canonical} {vertices remaining : List Gaussian.Basic.Canonical},
      Winding.Polygon.Product.ChainProductFormula p q start vertices →
        Winding.Polygon.Product.ChainProductFormula p q (Polygon.Chain.terminal start vertices) remaining →
        Winding.Polygon.Product.ChainProductFormula p q start (vertices ++ remaining)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons edge rest, tail =>
      .cons edge (rest.append tail)

/-- Product certificates for every edge, including the final return edge.

The appended base vertex supplies the final return edge. Each retained product identity concerns the same two
polynomials on that explicitly closed list. -/
public abbrev ClosedProductFormula (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (base : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical) :=
  Winding.Polygon.Product.ChainProductFormula p q base (vertices ++ [base])

/-- The correction at parameter zero is the correction at the segment's first vertex.

The original affine parameter-zero equation identifies the starting vertex. Scalar transport through the correction
function preserves the same two polynomial operands. -/
@[simp] public theorem lineProductCorrection2_segment_zero
    (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Winding.Edge.Product.lineProductCorrection2
        p q start (finish - start) 0 =
      Winding.Edge.Product.vertexProductCorrection2 p q start := by
  rw [Winding.Edge.Product.lineProductCorrection2, Affine.Segment.line_segment_zero]

/-- The correction at parameter one is the correction at the segment's last vertex.

The original affine parameter-one equation identifies the finishing vertex. Scalar transport through the correction
function preserves the same two polynomial operands. -/
@[simp] public theorem lineProductCorrection2_segment_one
    (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Winding.Edge.Product.lineProductCorrection2
        p q start (finish - start) 1 =
      Winding.Edge.Product.vertexProductCorrection2 p q finish := by
  rw [Winding.Edge.Product.lineProductCorrection2, Affine.Segment.line_segment_one]

/-- Open-chain product formula with the two uncancelled endpoint
corrections displayed explicitly.

The retained edge identities combine the two polynomial windings. Intermediate vertex corrections cancel while the
actual first and terminal corrections remain displayed. -/
public theorem chainRaw_mul_of_formula
    (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    ∀ (start : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical),
      Winding.Polygon.Product.ChainProductFormula p q start vertices →
        Winding.Polygon.Basic.chainRaw (p * q) start vertices =
          Winding.Polygon.Basic.chainRaw p start vertices + Winding.Polygon.Basic.chainRaw q start vertices -
            (Winding.Edge.Product.vertexProductCorrection2
              p q start : Int) +
            Winding.Edge.Product.vertexProductCorrection2
              p q (Polygon.Chain.terminal start vertices)
  | start, [], .nil _ => by
      simp only [Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      ring1
  | start, finish :: remaining, .cons edge tail => by
      have tailFormula := Purelib.Polynomial.Winding.Polygon.Product.chainRaw_mul_of_formula p q finish remaining tail
      unfold Winding.Edge.Product.LineProductFormula at edge
      simp only [Dense.Gaussian.Path.Segment.segment, Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal,
        Winding.Polygon.Product.lineProductCorrection2_segment_zero,
        Winding.Polygon.Product.lineProductCorrection2_segment_one] at edge ⊢
      rw [edge, tailFormula]
      ring1

/-- The local product corrections telescope around any explicitly closed
rational polygon.

The final return edge makes the terminal vertex the same retained base. Its two scalar corrections cancel in the
closed-chain integer identity. -/
public theorem closedRaw_mul_of_formula
    (p q : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical)
    (formula : Winding.Polygon.Product.ClosedProductFormula p q base vertices) :
    Winding.Polygon.Basic.closedRaw (p * q) base vertices =
      Winding.Polygon.Basic.closedRaw p base vertices + Winding.Polygon.Basic.closedRaw q base vertices := by
  unfold Winding.Polygon.Basic.closedRaw
  rw [Winding.Polygon.Product.chainRaw_mul_of_formula p q base (vertices ++ [base]) formula,
    Polygon.Chain.terminal_append_singleton]
  ring1
end Purelib.Polynomial.Winding.Polygon.Product
