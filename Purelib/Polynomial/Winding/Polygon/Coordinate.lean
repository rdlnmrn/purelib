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

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Monomial

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
    (Gaussian.Path.Segment.segment Coordinate.coordinatePolynomial point
      point).doubledWinding =
      0 := by
  unfold Gaussian.Path.Segment.segment Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding
    Rational.Pair.Path.Basic.PolynomialEdge.ofLine
  simp only [Gaussian.Path.Components.pathParts_eq]
  unfold Gaussian.Path.Components.pathReal Gaussian.Path.Components.pathImag Gaussian.Components.realPart
      Gaussian.Components.imagPart Gaussian.Substitution.Affine.composeLine
      Gaussian.Substitution.Affine.composeLineCoeffs
    Coordinate.coordinatePolynomial Gaussian.Substitution.Affine.mulLine
  simp only [List.foldl_cons, List.foldl_nil,
    Basic.DensePolynomial.scale_zero_right, Basic.DensePolynomial.shift_zero,
      Basic.DensePolynomial.zero_add_normalize,
    Basic.DensePolynomial.normalize_zero]
  rw [Gaussian.Basic.sub_self]
  rw [Basic.DensePolynomial.normalize_constant_of_ne one_ne_zero]
  simp only [Basic.DensePolynomial.scale_constant,
    Gaussian.Basic.mul_one,
    Basic.DensePolynomial.shift_zero, Basic.DensePolynomial.add_zero_normalize,
      Basic.DensePolynomial.normalize_constant_zero]
  rw [Basic.DensePolynomial.normalize_normalize, Basic.DensePolynomial.add_constant_zero,
    Basic.DensePolynomial.normalize_normalize]
  by_cases pointZero : point = 0
  · subst point
    rw [Basic.DensePolynomial.normalize_constant_zero]
    rfl
  · rw [Basic.DensePolynomial.normalize_constant_of_ne pointZero]
    change Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Basic.DensePolynomial.constant point.re)
      (Basic.DensePolynomial.constant point.im) 0 1 = 0
    by_cases realZero : point.re = 0
    · have secondZero : (Basic.DensePolynomial.constant point.re).isZero = true := by
        change (Basic.DensePolynomial.constant point.re).normalize.coeffs.isEmpty = true
        rw [realZero, Basic.DensePolynomial.normalize_constant_zero]
        exact Eq.refl _
      unfold Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
      have secondCount := Basic.DensePolynomial.degreeCount_eq_zero_of_isZero secondZero
      rw [Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
        Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF, secondCount]
      simp only [Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_zero,
        Rational.SignedRemainder.Variation.Sturm.endpointVariation2,
        List.map_cons, List.map_nil, Basic.DensePolynomial.eval_constant]
      exact Data.Int.Arithmetic.sub_eq_zero_of_eq rfl
    · have secondNonzero : (Basic.DensePolynomial.constant point.re).isZero = false := by
        change (Basic.DensePolynomial.constant point.re).normalize.coeffs.isEmpty = false
        rw [Basic.DensePolynomial.normalize_constant_of_ne realZero]
        exact Eq.refl _
      have secondCount : (Basic.DensePolynomial.constant point.re).degreeCount = 1 := by
        change (Basic.DensePolynomial.constant point.re).normalize.coeffs.length = 1
        rw [Basic.DensePolynomial.normalize_constant_of_ne realZero]
        exact Eq.refl _
      rw [Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
        Rational.SignedRemainder.Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
          secondNonzero secondCount]
      simp only [Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons, List.map_nil,
        Basic.DensePolynomial.eval_constant]
      exact Data.Int.Arithmetic.sub_eq_zero_of_eq rfl

/-- Consecutive copies of the current vertex are semantically stationary
and can be removed from an open polygonal chain.

The first segment has the same source and target coordinate and therefore contributes zero. The remaining chain keeps
its original ordered vertices and source. -/
@[simp] public theorem coordinate_chainRaw_cons_self
    (point : Gaussian.Basic.Canonical)
    (remaining : List Gaussian.Basic.Canonical) :
    Basic.chainRaw Coordinate.coordinatePolynomial point
        (point :: remaining) =
      Basic.chainRaw Coordinate.coordinatePolynomial point remaining := by
  change
    (Gaussian.Path.Segment.segment Coordinate.coordinatePolynomial point
      point).doubledWinding +
      Basic.chainRaw Coordinate.coordinatePolynomial point remaining = _
  rw [coordinate_segment_self_doubledWinding, Data.Int.Arithmetic.zero_add]

end Purelib.Polynomial.Winding.Polygon.Coordinate
