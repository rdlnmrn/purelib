module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Constant
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Winding.Edge.Constant

section
/-- A constant Gaussian edge reduces to the Cauchy index of its scalar components.

The Gaussian constant is nonzero; the affine origin, direction and endpoints are arbitrary. -/
theorem gaussianConstant_edge_winding
    (c origin direction : Gaussian.Basic.Canonical) (a b : Fraction.Rational) (nonzero : c ≠ 0) :
    (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c) origin direction
      a b).doubledWinding =
      Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 (Dense.Basic.DensePolynomial.constant c.re)
        (Dense.Basic.DensePolynomial.constant c.im) a b := by
  rw [Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding]
  change Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
      (Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.Constants.gaussianConstant c) origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.Constants.gaussianConstant c) origin direction) a b = _
  rw [Purelib.Polynomial.Dense.Gaussian.Path.Constant.gaussianConstant_pathReal c origin direction nonzero,
    Purelib.Polynomial.Dense.Gaussian.Path.Constant.gaussianConstant_pathImag c origin direction nonzero]
end

/-- Every affine traversal of a nonzero constant Gaussian polynomial has
zero Cauchy index. -/
theorem gaussianConstant_edge_winding_zero
    {c : Gaussian.Basic.Canonical} (nonzero : c ≠ 0)
    (origin direction : Gaussian.Basic.Canonical) (a b : Fraction.Rational) :
    (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c) origin direction
      a b).doubledWinding =
      0 := by
  rw [Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding c origin direction a b nonzero]
  by_cases realZero : c.re = 0
  · have secondZero : (Dense.Basic.DensePolynomial.constant c.re).isZero = true := by
      unfold Dense.Basic.DensePolynomial.isZero
      rw [realZero, Dense.Basic.DensePolynomial.normalize_constant_zero]
      rfl
    unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
    rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
    rw [secondZero, if_pos rfl]
    simp only [-eq_self, -iff_self, Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2,
      List.map_cons, List.map_nil, Dense.Basic.DensePolynomial.eval_constant]
    omega0
  · have secondNonzero : (Dense.Basic.DensePolynomial.constant c.re).isZero = false := by
      unfold Dense.Basic.DensePolynomial.isZero
      rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne realZero]
      rfl
    have secondCount : (Dense.Basic.DensePolynomial.constant c.re).degreeCount = 1 := by
      have positive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false secondNonzero
      have atMostOne := Dense.Basic.DensePolynomial.degreeCount_constant_le_one c.re
      omega
    rw [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2,
      Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_pair_of_second_degreeCount_one
        secondNonzero secondCount]
    simp only [-eq_self, -iff_self, Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2, List.map_cons,
      List.map_nil,
      Dense.Basic.DensePolynomial.eval_constant]
    omega0
end Purelib.Polynomial.Winding.Edge.Constant

end
