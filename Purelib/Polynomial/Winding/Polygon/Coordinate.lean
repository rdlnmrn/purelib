module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Data.Int.Arithmetic
import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Stationary coordinate segments in polygonal chains

A coordinate polynomial along a repeated endpoint becomes a constant
polynomial pair. Its retained endpoint variations agree, so the integer winding
vanishes and consecutive copies of the current vertex can be removed.
-/

namespace Purelib.Polynomial.Winding.Polygon.Coordinate

open Purelib
open Purelib.Data
open Purelib.Polynomial

/-- A stationary coordinate segment contributes no Cauchy index.

The affine substitution has zero direction at a repeated endpoint. Its constant real and imaginary coefficient lists
give equal endpoint variation readings, including zero real or Gaussian coordinates. -/
@[simp] public theorem coordinate_segment_self_doubledWinding
    (point : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Path.Segment.segment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial point
      point).doubledWinding =
      0 := by
  unfold Dense.Gaussian.Path.Segment.segment Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding
    Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine
    Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Components.realPart
      Dense.Gaussian.Components.imagPart Dense.Gaussian.Substitution.Affine.composeLine
      Dense.Gaussian.Substitution.Affine.composeLineCoeffs
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial Dense.Gaussian.Substitution.Affine.mulLine
  simp only [List.foldl_cons, List.foldl_nil,
    Dense.Basic.DensePolynomial.scale_zero_right, Dense.Basic.DensePolynomial.shift_zero,
      Dense.Basic.DensePolynomial.zero_add_normalize,
    Dense.Basic.DensePolynomial.normalize_zero]
  rw [Gaussian.Basic.sub_self]
  rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne one_ne_zero]
  simp only [Dense.Basic.DensePolynomial.scale_constant,
    Gaussian.Basic.mul_one,
    Dense.Basic.DensePolynomial.shift_zero, Dense.Basic.DensePolynomial.add_zero_normalize,
      Dense.Basic.DensePolynomial.normalize_constant_zero]
  rw [Dense.Basic.DensePolynomial.normalize_normalize, Dense.Basic.DensePolynomial.add_constant_zero,
    Dense.Basic.DensePolynomial.normalize_normalize]
  by_cases pointZero : point = 0
  · subst point
    rw [Dense.Basic.DensePolynomial.normalize_constant_zero]
    rfl
  · rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne pointZero]
    change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Basic.DensePolynomial.constant point.re)
      (Dense.Basic.DensePolynomial.constant point.im) 0 1 = 0
    by_cases realZero : point.re = 0
    · have secondZero : (Dense.Basic.DensePolynomial.constant point.re).isZero = true := by
        change (Dense.Basic.DensePolynomial.constant point.re).normalize.coeffs.isEmpty = true
        rw [realZero, Dense.Basic.DensePolynomial.normalize_constant_zero]
        exact Eq.refl _
      unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
      have secondCount := Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero secondZero
      rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF, secondCount]
      simp only [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_zero,
        Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2,
        List.map_cons, List.map_nil, Dense.Basic.DensePolynomial.eval_constant]
      exact Data.Int.Arithmetic.sub_eq_zero_of_eq rfl
    · have secondNonzero : (Dense.Basic.DensePolynomial.constant point.re).isZero = false := by
        change (Dense.Basic.DensePolynomial.constant point.re).normalize.coeffs.isEmpty = false
        rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne realZero]
        exact Eq.refl _
      have secondCount : (Dense.Basic.DensePolynomial.constant point.re).degreeCount = 1 := by
        change (Dense.Basic.DensePolynomial.constant point.re).normalize.coeffs.length = 1
        rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne realZero]
        exact Eq.refl _
      rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
        Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
          secondNonzero secondCount]
      simp only [Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
        Dense.Basic.DensePolynomial.eval_constant]
      exact Data.Int.Arithmetic.sub_eq_zero_of_eq rfl

/-- Consecutive copies of the current vertex are semantically stationary
and can be removed from an open polygonal chain.

The first segment has the same source and target coordinate and therefore contributes zero. The remaining chain keeps
its original ordered vertices and source. -/
@[simp] public theorem coordinate_chainRaw_cons_self
    (point : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) :
    Winding.Polygon.Basic.chainRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial point
        (point :: remaining) =
      Winding.Polygon.Basic.chainRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial point remaining := by
  change
    (Dense.Gaussian.Path.Segment.segment Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial point
      point).doubledWinding +
      Winding.Polygon.Basic.chainRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial point remaining = _
  rw [coordinate_segment_self_doubledWinding, Data.Int.Arithmetic.zero_add]

end Purelib.Polynomial.Winding.Polygon.Coordinate
