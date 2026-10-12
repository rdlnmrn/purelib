module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelDifferentialResidual

@[expose] public section

/-!
# Polynomial cap comparison on reciprocal coordinate segments

Let A approximate the reciprocal inverse root and B the cap's regular
inverse root. The polynomial q A B w^(1-k) G is the finite candidate cap
value. Its derivative differs from -w^m A by the regular root residual
and the two inverse-root differential residuals. All three residuals have
checked geometric bounds. The factor G and the actual domain restrictions
remain explicit; endpoint ownership comparison and the whole-boundary error
bound are separate obligations.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (DifferentialResidualBounds)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Model half)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {localBox :
    Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- The initial derivative residual polynomials and their finite ceilings are prepared once and shared by all later
comparison stages. -/
structure Preparation (cap : ReciprocalInnerInverse.Data curve collar)
    (initial : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) localBox) where
  /-- The retained derivative-residual bounds of the original reciprocal inverse model. -/ reciprocal :
    InverseModelDifferentialResidual.DifferentialResidualBounds initial
  /-- The retained derivative-residual bounds of the original regular cap model. -/ regular :
    InverseModelDifferentialResidual.DifferentialResidualBounds cap.model

constructive_injectivity Preparation

/-- Cache the derivative-residual bounds of the two original inverse models once. -/
def Preparation.build (cap : ReciprocalInnerInverse.Data curve collar)
    (initial : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) localBox) :
      Preparation cap initial :=
  ⟨DifferentialResidualBounds.build initial, DifferentialResidualBounds.build cap.model⟩

/-- Shifting a dense Gaussian polynomial by zero preserves its derivative evaluation. -/
public theorem derivative_shift_zero (polynomial : InverseRootPolynomial.Polynomial) (point :
  InverseRootPolynomial.Gaussian) :
    (Derivative.derivative (DensePolynomial.shift 0 polynomial)).eval point = (Derivative.derivative polynomial).eval
      point := by
  apply Derivative.eval_derivative_eq_of_sub_isZero
  apply NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro sample _
  rw [DensePolynomial.eval_shift, pow_zero, Data.Gaussian.Basic.mul_one]

variable {initial : Model
  (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) localBox}
  {differential : Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- A cached polynomial cap comparison at one retained reciprocal refinement.

The original cap sample, exact candidate value, coefficient and three residual terms remain linked by the
derivative-error identity. -/
structure Sample (preparation : Preparation cap initial)
    (capSample : Primitives.Sample cap differential index box) where
  /-- The cached original reciprocal inverse-root model at the retained refinement index. -/ reciprocal :
    InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) localBox
  /-- The cached reciprocal model is exactly the original model refined at the cap sample index. -/ reciprocal_eq :
    reciprocal = initial.refine index
  /-- The cached finite polynomial candidate for the cap primitive comparison. -/ value :
    InverseRootPolynomial.Polynomial
  /-- The cached candidate evaluates to the original radicand, reciprocal inverse, cap inverse, coordinate factor and
    primitive factor product. -/ value_eq : ∀ point, value.eval point =
    (HyperellipticReciprocal.polynomial curve).eval point * reciprocal.value.eval point *
      capSample.inverse.value.eval point * point ^ (1 - HyperellipticReciprocal.originOrder curve) *
        capSample.factor.eval point
  /-- The cached negative reciprocal differential coefficient polynomial. -/ coefficient :
    InverseRootPolynomial.Polynomial
  /-- The cached coefficient is the negative reversed-differential monomial times the same retained reciprocal inverse.
  -/
  coefficient_eq : ∀ point, coefficient.eval point =
    -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval point)
  /-- The exact derivative discrepancy splits into the original regular-root residual and the two retained differential
    residual terms. -/ derivative_error : ∀ point, (Derivative.derivative value).eval point - coefficient.eval point =
    point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval point *
      capSample.inverse.residual.eval point + InverseRootPolynomial.half * capSample.factor.eval point *
        (point ^ (1 - HyperellipticReciprocal.originOrder curve) * capSample.inverse.value.eval point *
          InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
            reciprocal.value point +
          point * reciprocal.value.eval point * InverseModelDifferentialResidual.differentialResidual cap.polynomial
            capSample.inverse.value point)

constructive_injectivity Sample

namespace Sample

/-- Consume a retained reciprocal refinement when another boundary consumer has already materialized it. -/
def ofModel (preparation : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Preparation cap initial)
    (capSample : Primitives.Sample cap differential index box)
    (reciprocal : InverseRootPolynomial.Model (HyperellipticReciprocal.polynomial curve) localBox)
    (reciprocal_eq : reciprocal = initial.refine index) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample preparation capSample := by
  let ratio := HyperellipticReciprocal.polynomial curve * reciprocal.value * capSample.inverse.value
  let factor := DensePolynomial.shift (1 - HyperellipticReciprocal.originOrder curve) capSample.factor
  let value := ratio * factor
  let coefficient := -(DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
    reciprocal.value)
  refine ⟨reciprocal, reciprocal_eq, value, ?_, coefficient, ?_, ?_⟩
  · intro point
    simp only [value, ratio, factor, DensePolynomial.eval_mul, DensePolynomial.eval_shift]
    ring1
  · intro point
    simp only [coefficient, DensePolynomial.eval_neg, DensePolynomial.eval_shift]
    ring1
  · intro point
    have derivative_value : (Derivative.derivative value).eval point =
        (Derivative.derivative ratio).eval point * factor.eval point + ratio.eval point * (Derivative.derivative
          factor).eval point :=
      Derivative.eval_derivative_mul ratio factor point
    have twiceHalf : (2 : InverseRootPolynomial.Gaussian) * InverseRootPolynomial.half = 1 := by decide
    apply Data.Gaussian.Field.mul_right_cancel_of_ne (show (2 : InverseRootPolynomial.Gaussian) ≠ 0 by decide)
    rw [Data.Gaussian.Basic.mul_comm _ (2 : InverseRootPolynomial.Gaussian),
      Data.Gaussian.Basic.mul_comm _ (2 : InverseRootPolynomial.Gaussian)]
    rw [derivative_value]
    have normalizedError :
        2 * (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval point
          *
          capSample.inverse.residual.eval point + InverseRootPolynomial.half * capSample.factor.eval point *
            (point ^ (1 - HyperellipticReciprocal.originOrder curve) * capSample.inverse.value.eval point *
              InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
                reciprocal.value point +
              point * reciprocal.value.eval point * InverseModelDifferentialResidual.differentialResidual cap.polynomial
                capSample.inverse.value point)) =
        2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval point *
          capSample.inverse.residual.eval point + capSample.factor.eval point *
            (point ^ (1 - HyperellipticReciprocal.originOrder curve) * capSample.inverse.value.eval point *
              InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
                reciprocal.value point +
              point * reciprocal.value.eval point * InverseModelDifferentialResidual.differentialResidual cap.polynomial
                capSample.inverse.value point) := by
      calc
        _ = 2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval
          point *
            capSample.inverse.residual.eval point + (2 * InverseRootPolynomial.half) * capSample.factor.eval point *
              (point ^ (1 - HyperellipticReciprocal.originOrder curve) * capSample.inverse.value.eval point *
                InverseModelDifferentialResidual.differentialResidual (HyperellipticReciprocal.polynomial curve)
                  reciprocal.value point +
                point * reciprocal.value.eval point * InverseModelDifferentialResidual.differentialResidual
                  cap.polynomial capSample.inverse.value point) := by ring1
        _ = _ := by rw [twiceHalf, Data.Gaussian.Basic.one_mul]
    rw [normalizedError]
    have capFactor := capSample.factor_derivative point
    change capSample.factor.eval point + (Primitives.degree curve : InverseRootPolynomial.Gaussian) * point *
      (Derivative.derivative capSample.factor).eval point = _ at capFactor
    rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
    · have qValue : (HyperellipticReciprocal.polynomial curve).eval point = cap.polynomial.eval point := by
        rw [HyperellipticReciprocal.polynomial_eval, regular, pow_zero, Data.Gaussian.Basic.mul_one, cap.polynomial_eq]
      have qDerivative : (Derivative.derivative (HyperellipticReciprocal.polynomial curve)).eval point =
          (Derivative.derivative cap.polynomial).eval point := by
        rw [HyperellipticReciprocal.polynomial, regular,
          Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.derivative_shift_zero, cap.polynomial_eq]
      have factorDerivative : (Derivative.derivative factor).eval point =
          -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * capSample.inverse.value.eval
            point) := by
        change (Derivative.derivative (DensePolynomial.shift (1 - HyperellipticReciprocal.originOrder curve)
          capSample.factor)).eval point = _
        rw [regular, Nat.sub_zero, Derivative.eval_derivative_shift_one]
        have plain : capSample.factor.eval point + point * (Derivative.derivative capSample.factor).eval point =
            -(point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
              capSample.inverse.value.eval point) := by
          simpa only [Primitives.degree, regular, Nat.zero_add, Nat.cast_one,
            Data.Gaussian.Basic.one_mul, neg_one_mul, neg_mul] using capFactor
        exact (by ring1 : (Derivative.derivative capSample.factor).eval point * point + capSample.factor.eval point =
          capSample.factor.eval point + point * (Derivative.derivative capSample.factor).eval point).trans plain
      rw [factorDerivative]
      simp only [ratio, factor, coefficient, Derivative.eval_derivative_mul, DensePolynomial.eval_mul,
        DensePolynomial.eval_shift, DensePolynomial.eval_neg,
        regular, Nat.sub_zero, pow_one, qValue, qDerivative, InverseModelDifferentialResidual.differentialResidual,
          capSample.inverse.residual_eq]
      ring1
    · have qValue : (HyperellipticReciprocal.polynomial curve).eval point = cap.polynomial.eval point * point := by
        rw [HyperellipticReciprocal.polynomial_eval, branch, pow_one, cap.polynomial_eq]
      have qDerivative : (Derivative.derivative (HyperellipticReciprocal.polynomial curve)).eval point =
          (Derivative.derivative cap.polynomial).eval point * point + cap.polynomial.eval point := by
        rw [HyperellipticReciprocal.polynomial, branch, Derivative.eval_derivative_shift_one, cap.polynomial_eq]
      have twiceFactor : capSample.factor.eval point + 2 * point * (Derivative.derivative capSample.factor).eval point =
          -2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
            capSample.inverse.value.eval point := by
        simpa only [Primitives.degree, branch, show ((1 + 1 : Nat) : InverseRootPolynomial.Gaussian) = 2 by rfl] using
          capFactor
      have correction :
          cap.polynomial.eval point * reciprocal.value.eval point * capSample.inverse.value.eval point *
            (capSample.factor.eval point + 2 * point * (Derivative.derivative capSample.factor).eval point) =
          cap.polynomial.eval point * reciprocal.value.eval point * capSample.inverse.value.eval point *
            (-2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
              capSample.inverse.value.eval point) :=
        congrArg (fun x => cap.polynomial.eval point * reciprocal.value.eval point * capSample.inverse.value.eval point
          * x) twiceFactor
      simp only [ratio, factor, coefficient, Derivative.eval_derivative_mul, DensePolynomial.eval_mul,
        DensePolynomial.eval_shift, DensePolynomial.eval_neg,
        branch, Nat.sub_self, pow_zero, Data.Gaussian.Basic.mul_one,
        Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.derivative_shift_zero, qValue, qDerivative,
          InverseModelDifferentialResidual.differentialResidual,
        capSample.inverse.residual_eq]
      calc
        _ = (2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent * reciprocal.value.eval
          point *
            (1 - cap.polynomial.eval point * capSample.inverse.value.eval point ^ 2) + capSample.factor.eval point *
            (capSample.inverse.value.eval point *
              (2 * (cap.polynomial.eval point * point) * (Derivative.derivative reciprocal.value).eval point +
                ((Derivative.derivative cap.polynomial).eval point * point + cap.polynomial.eval point) *
                  reciprocal.value.eval point) +
              point * reciprocal.value.eval point *
                (2 * cap.polynomial.eval point * (Derivative.derivative capSample.inverse.value).eval point +
                  (Derivative.derivative cap.polynomial).eval point * capSample.inverse.value.eval point))) +
            cap.polynomial.eval point * reciprocal.value.eval point * capSample.inverse.value.eval point *
              (capSample.factor.eval point + 2 * point * (Derivative.derivative capSample.factor).eval point) -
            cap.polynomial.eval point * reciprocal.value.eval point * capSample.inverse.value.eval point *
              (-2 * point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent *
                capSample.inverse.value.eval point) := by ring1
        _ = _ := by rw [correction]; ring1

/-- Construct the original polynomial pullback sample on the retained reciprocal model with its exact coordinate and
derivative identities. -/
def build (preparation : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Preparation cap initial)
    (capSample : Primitives.Sample cap differential index box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample preparation capSample :=
  ofModel preparation capSample (initial.refine
    index) rfl

variable {preparation : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Preparation cap initial}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The retained reciprocal model differential residual satisfies its original geometric bound on the reciprocal model
box. -/
theorem reciprocal_differential_bound (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample
  preparation capSample) {point : InverseRootPolynomial.Gaussian}
    (inside : localBox.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual
      (HyperellipticReciprocal.polynomial curve) sample.reciprocal.value point) ≤
      Geometric.Basic.quarterRadius preparation.reciprocal.bound index := by
  rw [sample.reciprocal_eq]
  have scalar := preparation.reciprocal.refine_bound index inside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- The retained regular cap model differential residual satisfies its original geometric bound on the cap box. -/
theorem regular_differential_bound (_sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback.Sample
  preparation capSample) {point : InverseRootPolynomial.Gaussian}
    (inside : collar.box.Contains point) :
    Data.Gaussian.Norm.Basic.normSq (InverseModelDifferentialResidual.differentialResidual cap.polynomial
      capSample.inverse.value point) ≤
      Geometric.Basic.quarterRadius preparation.regular.bound index := by
  rw [capSample.inverse_eq]
  have scalar := preparation.regular.refine_bound index inside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end Sample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
