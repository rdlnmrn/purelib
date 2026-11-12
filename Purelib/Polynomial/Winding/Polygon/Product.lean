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

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients

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
public inductive ChainProductFormula (p q : CoefficientPolynomial) :
    Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical → Prop
  /-- The empty chain requires no edge product certificates. -/ | nil (start : Gaussian.Basic.Canonical) :
    Product.ChainProductFormula p q start []
  /-- Retain the first edge's product identity and the remaining chain's certificates. -/ | cons {start finish :
    Gaussian.Basic.Canonical} {remaining : List Gaussian.Basic.Canonical}
      (edge : Edge.Product.LineProductFormula p q
        start (finish - start) 0 1)
      (tail : Product.ChainProductFormula p q finish remaining) :
      Product.ChainProductFormula p q start (finish :: remaining)

/-- Append edge product certificates along two consecutive polygonal chains.

The second certificate begins at the actual terminal vertex of the first chain. Recursion retains each edge identity in
the same concatenated order. -/
public theorem ChainProductFormula.append
    {p q : CoefficientPolynomial} :
    ∀ {start : Gaussian.Basic.Canonical} {vertices remaining : List Gaussian.Basic.Canonical},
      ChainProductFormula p q start vertices →
        ChainProductFormula p q (Polygon.Chain.terminal start vertices) remaining →
        ChainProductFormula p q start (vertices ++ remaining)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons edge rest, tail =>
      .cons edge (rest.append tail)

/-- Product certificates for every edge, including the final return edge.

The appended base vertex supplies the final return edge. Each retained product identity concerns the same two
polynomials on that explicitly closed list. -/
public abbrev ClosedProductFormula (p q : CoefficientPolynomial)
    (base : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical) :=
  ChainProductFormula p q base (vertices ++ [base])

/-- The correction at parameter zero is the correction at the segment's first vertex.

The original affine parameter-zero equation identifies the starting vertex. Scalar transport through the correction
function preserves the same two polynomial operands. -/
@[simp] public theorem lineProductCorrection2_segment_zero
    (p q : CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Edge.Product.lineProductCorrection2
        p q start (finish - start) 0 =
      Edge.Product.vertexProductCorrection2 p q start := by
  rw [Edge.Product.lineProductCorrection2, Affine.Segment.line_segment_zero]

/-- The correction at parameter one is the correction at the segment's last vertex.

The original affine parameter-one equation identifies the finishing vertex. Scalar transport through the correction
function preserves the same two polynomial operands. -/
@[simp] public theorem lineProductCorrection2_segment_one
    (p q : CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    Edge.Product.lineProductCorrection2
        p q start (finish - start) 1 =
      Edge.Product.vertexProductCorrection2 p q finish := by
  rw [Edge.Product.lineProductCorrection2, Affine.Segment.line_segment_one]

/-- Open-chain product formula with the two uncancelled endpoint
corrections displayed explicitly.

The retained edge identities combine the two polynomial windings. Intermediate vertex corrections cancel while the
actual first and terminal corrections remain displayed. -/
public theorem chainRaw_mul_of_formula
    (p q : CoefficientPolynomial) :
    ∀ (start : Gaussian.Basic.Canonical) (vertices : List Gaussian.Basic.Canonical),
      ChainProductFormula p q start vertices →
        Basic.chainRaw (p * q) start vertices =
          Basic.chainRaw p start vertices + Basic.chainRaw q start vertices -
            (Edge.Product.vertexProductCorrection2
              p q start : Int) +
            Edge.Product.vertexProductCorrection2
              p q (Polygon.Chain.terminal start vertices)
  | start, [], .nil _ => by
      simp only [Basic.chainRaw, Polygon.Chain.terminal]
      ring1
  | start, finish :: remaining, .cons edge tail => by
      have tailFormula := Product.chainRaw_mul_of_formula p q finish remaining tail
      unfold Edge.Product.LineProductFormula at edge
      simp only [Dense.Gaussian.Path.Segment.segment, Basic.chainRaw, Polygon.Chain.terminal,
        lineProductCorrection2_segment_zero,
        lineProductCorrection2_segment_one] at edge ⊢
      rw [edge, tailFormula]
      ring1

/-- The local product corrections telescope around any explicitly closed
rational polygon.

The final return edge makes the terminal vertex the same retained base. Its two scalar corrections cancel in the
closed-chain integer identity. -/
public theorem closedRaw_mul_of_formula
    (p q : CoefficientPolynomial) (base : Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical)
    (formula : ClosedProductFormula p q base vertices) :
    Basic.closedRaw (p * q) base vertices =
      Basic.closedRaw p base vertices + Basic.closedRaw q base vertices := by
  unfold Basic.closedRaw
  rw [chainRaw_mul_of_formula p q base (vertices ++ [base]) formula,
    Polygon.Chain.terminal_append_singleton]
  ring1
end Purelib.Polynomial.Winding.Polygon.Product
