module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
public import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Data.Int.Arithmetic

/-!
# Integer winding of finite polygonal chains

The ordered target list and current source vertex determine the affine segment
sequence. Closing the list appends the retained base vertex; concatenation
continues at the actual terminal vertex of the first chain.
-/

namespace Purelib.Polynomial.Winding.Polygon.Basic

open Purelib
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Raw winding along a finite open chain.  The list contains the successive
target vertices and `start` is its current source vertex.

Each consecutive segment consumes the supplied polynomial at the retained source and target vertices. The finite
recursion keeps their order and adds the displayed integer segment winding to the remaining chain. -/
@[expose] public def chainRaw (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  Gaussian.Basic.Canonical →
  List Gaussian.Basic.Canonical → Int
  | _, [] => 0
  | start, finish :: remaining =>
      (Dense.Gaussian.Path.Segment.segment p start finish).doubledWinding +
        Purelib.Polynomial.Winding.Polygon.Basic.chainRaw p finish remaining

/-- Raw winding of the explicitly closed polygon obtained by returning from
the last displayed vertex to `base`.

The final appended base vertex supplies the closing segment from the terminal displayed vertex. The original open-chain
computation consumes the same polynomial and ordered vertices. -/
@[expose] public def closedRaw (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base :
  Gaussian.Basic.Canonical)
    (vertices : List Gaussian.Basic.Canonical) : Int :=
  Winding.Polygon.Basic.chainRaw p base (vertices ++ [base])

/-- The raw winding of concatenated vertex lists is the sum of the two chain windings.

The second chain starts at the actual terminal vertex of the first chain. -/
public theorem chainRaw_append (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    ∀ (start : Gaussian.Basic.Canonical) (first second : List Gaussian.Basic.Canonical),
      Winding.Polygon.Basic.chainRaw p start (first ++ second) =
        Winding.Polygon.Basic.chainRaw p start first +
          Winding.Polygon.Basic.chainRaw p (Polygon.Chain.terminal start first) second
  | start, [], second => by
      simp only [List.nil_append, Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      rw [Data.Int.Arithmetic.zero_add]
  | start, finish :: remaining, second => by
      simp only [List.cons_append, Winding.Polygon.Basic.chainRaw, Polygon.Chain.terminal]
      rw [Purelib.Polynomial.Winding.Polygon.Basic.chainRaw_append p finish remaining second]
      exact (Data.Int.Arithmetic.add_assoc _ _ _).symm
end Purelib.Polynomial.Winding.Polygon.Basic
