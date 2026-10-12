module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Polynomial.Path.Clearance.WithBound

import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Dominance
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Perturbation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

/-!
# Power-family affine-path clearance transport

A parameter displacement below the retained clearance transports the same
finite affine path to the target polynomial. The original checked package
retains both the certificate and its exact margin-and-Horner bound.
-/

namespace Purelib.RootIsolation.Power.Clearance.Path.Transport

open Purelib.Data.Gaussian
open Purelib.RootIsolation

/-- Retain affine-path clearance and its exact displacement-and-Horner bound.

The original margin is the source certificate's bound minus the squared
parameter displacement. Its positivity and pointwise dominance certify the
retained target-path polynomial pair on the same interval. -/
private opaque certifiedPathCertificateAfterMove
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    {origin direction : Gaussian.Basic.Canonical} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction) interval)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    Purelib.Geometry.Polynomial.Path.Clearance.WithBound.PathCertificateWithBound
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction) interval
      ((clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)) ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction) interval +
            Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction) interval))) := by
  rw [Power.Gaussian.Perturbation.polynomial_target_eq_add_perturbation]
  let margin := clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)
  have marginPositive : 0 < margin :=
    Fraction.Order.Arithmetic.sub_pos_direct small
  have dominance : ∀ point : Fraction.Rational, interval.Contains point →
      margin ≤
        (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
            origin direction).eval point ^ 2 +
          (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
            origin direction).eval point ^ 2 -
          ((Dense.Gaussian.Path.Components.pathReal
              (Power.Gaussian.Perturbation.parameterPerturbation source target)
                origin direction).eval point ^ 2 +
            (Dense.Gaussian.Path.Components.pathImag
              (Power.Gaussian.Perturbation.parameterPerturbation source target)
                origin direction).eval point ^ 2) := by
    intro point inside
    have sourceLower := clearance.lower point inside
    calc
      margin = clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target) := rfl
      _ ≤
          (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction).eval point ^ 2 +
            (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction).eval point ^ 2 -
              Data.Gaussian.Norm.Basic.normSq (source - target) :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct sourceLower _
      _ = _ := by
        rewrite [Dense.Gaussian.Path.Components.eval_pathReal,
          Dense.Gaussian.Path.Components.eval_pathImag,
          Dense.Gaussian.Path.Components.eval_pathReal,
          Dense.Gaussian.Path.Components.eval_pathImag,
          Power.Gaussian.Perturbation.parameterPerturbation_eval, Data.Gaussian.Norm.Basic.normSq]
        rfl
  have sumReal : ∀ point : Fraction.Rational,
      (Dense.Gaussian.Path.Components.pathReal
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree +
            Power.Gaussian.Perturbation.parameterPerturbation
            source target)
            origin direction).eval point =
        (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
            origin direction).eval point +
          (Dense.Gaussian.Path.Components.pathReal
            (Power.Gaussian.Perturbation.parameterPerturbation source target)
              origin direction).eval point := by
    intro point
    rw [Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathReal, Dense.Basic.DensePolynomial.eval_add]
    rfl
  have sumImag : ∀ point : Fraction.Rational,
      (Dense.Gaussian.Path.Components.pathImag
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree +
            Power.Gaussian.Perturbation.parameterPerturbation
            source target)
            origin direction).eval point =
        (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
            origin direction).eval point +
          (Dense.Gaussian.Path.Components.pathImag
            (Power.Gaussian.Perturbation.parameterPerturbation source target)
              origin direction).eval point := by
    intro point
    rw [Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathImag,
      Dense.Gaussian.Path.Components.eval_pathImag, Dense.Basic.DensePolynomial.eval_add]
    rfl
  let value := Clearance.Pair.Dominance.sumCertificate_of_normDominance
    margin marginPositive dominance sumReal sumImag
  exact
    { value := value
      bound := by
        dsimp only [value]
        exact Clearance.Pair.Dominance.sumCertificate_of_normDominance_bound
          margin marginPositive dominance sumReal sumImag }

/-- Read the complete target-path certificate from the checked transport package.

The original source certificate, degree, affine path and displacement proof
are supplied once to the opaque builder. This operation retains its computed
certificate without exposing the builder's body to clients. -/
public def pathCertificateAfterMoveData
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    {origin direction : Gaussian.Basic.Canonical} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction) interval)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction) interval :=
  (certifiedPathCertificateAfterMove degree clearance small).value

/-- Transport the complete affine-path clearance to the new power-family parameter.

The parameter displacement is strictly below the original clearance; the returned certificate reuses the opaque checked
margin-and-Horner construction. -/
@[expose] public def pathCertificateAfterMove
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    {origin direction : Gaussian.Basic.Canonical} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction) interval)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial target degree)
        origin direction) interval :=
  pathCertificateAfterMoveData degree clearance small

/-- Read the exact rational bound of the transported affine-path certificate.

The cached margin square is divided by four times the source-path Horner
majorant, using the original path components and interval. -/
@[simp] public theorem pathCertificateAfterMove_bound
    {source target : Gaussian.Basic.Canonical} (degree : Data.Nat.Positive.RootDegree)
    {origin direction : Gaussian.Basic.Canonical} {interval : Data.Rat.Interval.Bounds}
    (clearance : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction)
      (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
        origin direction) interval)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < clearance.bound) :
    (pathCertificateAfterMove degree clearance small).bound =
      (clearance.bound - Data.Gaussian.Norm.Basic.normSq (source - target)) ^ 2 /
        (4 * max 1
          (Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathReal (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction) interval +
            Dense.Rational.Bounds.Horner.evalSqBound
              (Dense.Gaussian.Path.Components.pathImag (Purelib.Polynomial.Power.Gaussian.rootPolynomial source degree)
                origin direction) interval)) :=
  (certifiedPathCertificateAfterMove degree clearance small).bound

end Purelib.RootIsolation.Power.Clearance.Path.Transport
