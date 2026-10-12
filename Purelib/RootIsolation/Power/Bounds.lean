module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Fold
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
import Purelib.Polynomial.Dense.Gaussian.Coefficients.Tail
import Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm.Weighted
import Purelib.Polynomial.Dense.Gaussian.Majorant

public import Purelib.Polynomial.Power.Gaussian
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring

import Purelib.Data.List.Reverse
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! Coefficient-computed bounds for the original positive-degree power family. -/

namespace Purelib.RootIsolation.Power.Bounds

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Gaussian

/-- For the sparse power polynomial the global-square coefficient weight is
exactly `d N(w)`.

In particular, parameters with equal squared norm use the
same computed ambient box; no completed circle or compactness argument is
needed to identify their finite isolations' supports. -/
public theorem denseLowerCoefficientWeight_polynomial
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) =
      (degree.value : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq parameter := by
  rw [Dense.Gaussian.Bounds.RootRadius.denseLowerCoefficientWeight,
    Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree, Dense.Gaussian.Coefficients.Tail.lowerCoefficients,
    Purelib.Polynomial.Power.Gaussian.rootPolynomial_normalized]
  have reverseLast : ([-parameter] : List Gaussian.Basic.Canonical).reverse = [-parameter] := rfl
  simp only [Purelib.Polynomial.Power.Gaussian.rootPolynomial, Power.Gaussian.rootPolynomial, List.tail_cons,
    Data.List.Reverse.reverse_append, Data.List.Reverse.reverse_replicate, reverseLast]
  rw [Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum_append]
  simp only [Dense.Gaussian.Evaluation.Norm.Weighted.weightedNormSum, Gaussian.Norm.Basic.normSq_neg, pow_zero,
    List.length_singleton, Nat.zero_add, Dense.Gaussian.Majorant.weightedNormSum_replicate_zero]
  ring1

/-- The displayed positive-degree power polynomial is monic.

Its original normalized coefficient list begins with one. The retained
positive degree ensures this same leading coefficient is present. -/
public theorem leadingCoeff_polynomial
    (parameter : Gaussian.Basic.Canonical) (degree : Data.Nat.Positive.RootDegree) :
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).leadingCoeff = 1 := by
  rw [Dense.Basic.DensePolynomial.leadingCoeff,
    Purelib.Polynomial.Power.Gaussian.rootPolynomial_normalized]
  rfl

/-- On the unit parameter circuit the computed global square has exact
radius `d+1`.

The coefficient weight and monic leading coefficient determine the same
retained radius from the supplied unit quadrance and positive degree. -/
public theorem denseLargeSquareRadius_polynomial_of_unit
    {parameter : Gaussian.Basic.Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      degree)
      =
      (degree.value : Fraction.Rational) + 1 := open Purelib.Algebra.Field in by
  unfold Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
  rw [denseLowerCoefficientWeight_polynomial, leadingCoeff_polynomial,
    Gaussian.Norm.Basic.normSq_one, parameterUnit]
  have oneLeDegree : (1 : Fraction.Rational) ≤ (degree.value : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct degree.positive
  have expression :
      (degree.value : Fraction.Rational) * 1 / 1 + 1 =
        (degree.value : Fraction.Rational) + 1 := by
    have inverseOne : (1 : Fraction.Rational)⁻¹ = 1 := by decide
    rw [ExplicitField.div_eq_mul_inv, inverseOne]
    ring1
  rw [expression]
  exact Fraction.Order.Basic.max_eq_right (by
    calc
      (1 : Fraction.Rational) ≤ (degree.value : Fraction.Rational) := oneLeDegree
      _ ≤ (degree.value : Fraction.Rational) + 1 := by
        have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
          (by decide : (0 : Fraction.Rational) ≤ 1) (degree.value : Fraction.Rational)
        calc
          (degree.value : Fraction.Rational) = 0 + (degree.value : Fraction.Rational) := by ring1
          _ ≤ 1 + (degree.value : Fraction.Rational) := shifted
          _ = (degree.value : Fraction.Rational) + 1 := by ring1)

/-- Equal-norm parameters in the power family have definitionally equal
coefficient-computed global square radii.

Their original coefficient weights and leading coefficients agree at the
same positive degree, so the retained boxes have equal defining radii. -/
public theorem largeSquareBox_polynomial_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical} (equalNorm : Data.Gaussian.Norm.Basic.normSq source =
      Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
      =
      Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
        degree) :=
        by
  unfold Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
  congr 1
  unfold Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius
  rw [denseLowerCoefficientWeight_polynomial,
    denseLowerCoefficientWeight_polynomial, leadingCoeff_polynomial,
    leadingCoeff_polynomial, Gaussian.Norm.Basic.normSq_one, equalNorm]

/-- The first-order Horner majorant has the same equal-quadrance invariance.

The original Horner scan reads the final parameter coefficient through its
quadrance in the same coefficient-computed ambient box. -/
public theorem denseLipschitzBound_polynomial_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical} (equalNorm : Data.Gaussian.Norm.Basic.normSq source =
      Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          degree))
          =
      Dense.Gaussian.Bounds.Box.denseLipschitzBound
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
          degree))
          := by
  rw [← largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
  unfold Dense.Gaussian.Bounds.Box.denseLipschitzBound
    Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound
    Dense.Gaussian.Bounds.Box.denseHornerNormBounds
  simp only [Purelib.Polynomial.Power.Gaussian.rootPolynomial, Power.Gaussian.rootPolynomial, List.foldl_cons,
    Data.List.Fold.foldl_append, List.foldl_nil,
    Dense.Gaussian.Bounds.Horner.step, Gaussian.Norm.Basic.normSq_neg, equalNorm, -eq_self, -iff_self]
  rfl

/-- The coefficient-scanned Taylor budget is likewise identical for
equal-quadrance parameters.

The Horner scan sees the parameter only through
the quadrance of the final coefficient `-w`. -/
public theorem denseTaylorRemainderBound_polynomial_eq_of_normSq_eq
    {source target : Gaussian.Basic.Canonical} (equalNorm : Data.Gaussian.Norm.Basic.normSq source =
      Data.Gaussian.Norm.Basic.normSq target)
    (degree : Data.Nat.Positive.RootDegree) :
    Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          degree))
          =
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial target
          degree))
          := by
  rw [← largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
  unfold Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound
    Dense.Gaussian.Bounds.Box.Taylor.denseEvalTaylorRemainderBound
    Dense.Gaussian.Bounds.Box.Taylor.denseHornerTaylorNormBounds
  simp only [Purelib.Polynomial.Power.Gaussian.rootPolynomial, Power.Gaussian.rootPolynomial, List.foldl_cons,
    Data.List.Fold.foldl_append, List.foldl_nil,
    Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds.step, Gaussian.Norm.Basic.normSq_neg, equalNorm, -eq_self,
      -iff_self]
  rfl

end Purelib.RootIsolation.Power.Bounds
