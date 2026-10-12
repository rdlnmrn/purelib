module
import Purelib.Data.Int.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Comparison
import Purelib.Polynomial.Winding.Polygon.Coordinate

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

@[expose] public section

/-!
# Removing stationary vertices from nonvanishing polynomial walks

A repeated base coordinate has constant polynomial value.  Compare it with
that constant coordinate walk using zero Rouché error; the two endpoint
corrections agree.  This proof uses the existing finite winding formulas,
without polynomial extensionality or a change to the Cauchy-index program.
-/

namespace Purelib.Polynomial.Winding.Polygon.Stationary

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Path

/-- A stationary polynomial edge has no index when its displayed value is
nonzero.  This includes values on either coordinate axis. -/
theorem segment_self_doubledWinding (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (point : Gaussian.Basic.Canonical) (nonzero : polynomial.eval point ≠ 0) :
    (Dense.Gaussian.Path.Segment.segment polynomial point point).doubledWinding = 0 := open Purelib in open
      Purelib.Geometry.Rational in by
  let value := polynomial.eval point
  let coordinate := Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
  let A := Dense.Gaussian.Path.Components.pathReal coordinate value (value - value)
  let B := Dense.Gaussian.Path.Components.pathImag coordinate value (value - value)
  let U := Dense.Gaussian.Path.Components.pathReal polynomial point (point - point)
  let V := Dense.Gaussian.Path.Components.pathImag polynomial point (point - point)
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide⟩
  let clearance : Clearance.Pair.Basic.Certificate A B interval :=
    { bound := Data.Gaussian.Norm.Basic.normSq value
      positive := Gaussian.Norm.Basic.normSq_pos nonzero
      lower := by
        intro time _inside
        simp only [A, B, Dense.Gaussian.Path.Components.eval_pathReal, Dense.Gaussian.Path.Components.eval_pathImag,
          Affine.Segment.line_self,
          coordinate, Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, Data.Gaussian.Norm.Basic.normSq]
        exact le_rfl }
  have formula : Winding.Polygon.Comparison.SegmentHomotopyFormula coordinate polynomial value value point point := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [coordinate, Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval] using nonzero
    · simpa only [coordinate, Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval] using nonzero
    apply Dense.Rational.CauchyIndex.Comparison.Dominance.lineData_of_normDominance
      (C := U - A) (D := V - B) (root := interval)
      (by decide) clearance (Data.Gaussian.Norm.Basic.normSq value) (Gaussian.Norm.Basic.normSq_pos nonzero)
    · intro time _inside
      simp only [U, V, A, B, Dense.Basic.DensePolynomial.eval_sub, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag,
        Affine.Segment.line_self, coordinate, Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, value,
          Data.Gaussian.Norm.Basic.normSq]
      apply le_of_eq
      ring1
    · intro time
      rw [Dense.Basic.DensePolynomial.eval_sub]
      ring1
    · intro time
      rw [Dense.Basic.DensePolynomial.eval_sub]
      ring1
  have equality := Winding.Polygon.Comparison.segmentRaw_eq_of_homotopy formula
  rw [Winding.Polygon.Coordinate.coordinate_segment_self_doubledWinding] at equality
  exact equality.trans (by ring1)

/-- Removing a repeated initial vertex preserves the chain winding when the polynomial value there is nonzero.

The repeated point contributes the original stationary edge with zero doubled winding. Its removal preserves the same
ordered tail vertices and polynomial values. -/
theorem chainRaw_cons_self (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (point :
  Gaussian.Basic.Canonical)
    (nonzero : polynomial.eval point ≠ 0) (remaining : List Gaussian.Basic.Canonical) :
    Winding.Polygon.Basic.chainRaw polynomial point (point :: remaining) = Winding.Polygon.Basic.chainRaw polynomial
      point remaining := by
  rw [Winding.Polygon.Basic.chainRaw, Winding.Polygon.Stationary.segment_self_doubledWinding polynomial point nonzero,
    Data.Int.Arithmetic.zero_add]

end Purelib.Polynomial.Winding.Polygon.Stationary
