module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
public import Purelib.Riemann.Normalization.InverseModelRootRequests
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootRequests

@[expose] public section

/-!
# Actual cap primitive derivatives on the model's owned root

The polynomial derivative and the root used by the reciprocal overlap now
come from the same cached inverse model. One computed request pays the
inverse-root discrepancy and the actual numerator, including zero numerators
at the cap origin. Both finite reading indices may increase independently.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ModelAgreement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Gaussian Coordinate Box)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners (Point)
open Purelib.Riemann.Normalization.InverseModelRootRequests (InverseRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (Sample point degree numerator_eval coefficient)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parameter :
    Gaussian}

set_option genInjectivity false in
/-- A paid derivative-to-root comparison request on the same original cap model channel.

The exact differential numerator, positive weight and inverse-root request retain the original parameter, target and
stage floor. -/
structure CoefficientRequest (owned : Owners.Point data (Primitives.point curve parameter))
    (differential : Differentials.Basic.Differential genus) (target : Coordinate) (floor : Nat) where
  /-- The original coefficient comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached exact pulled differential numerator at the original cap parameter. -/ numerator : Gaussian
  /-- The cached numerator is exactly the retained differential polynomial evaluated at the original parameter. -/
    numerator_eq : numerator = (Primitives.numerator curve differential).eval parameter
  /-- The cached positive scale used to pay the numerator multiplication. -/ weight : Coordinate
  /-- The retained weight is exactly one plus the cached numerator squared norm. -/ weight_eq : weight =
    Data.Gaussian.Norm.Basic.normSq numerator + 1
  /-- The inverse-root comparison on the same original channel with target divided by the retained weight and the
    original stage floor. -/ inverse : InverseModelRootRequests.InverseRequest owned.channel (target / weight) floor

constructive_injectivity CoefficientRequest

namespace CoefficientRequest

/-- Cache the exact numerator and positive weight, then request the required inverse-root accuracy from the same
retained cap channel. -/
def build (owned : Owners.Point data (Primitives.point curve parameter))
    (differential : Differentials.Basic.Differential genus) (target : Coordinate) (positive : 0 < target) (floor : Nat)
      :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.ModelAgreement.CoefficientRequest owned differential target floor :=
  let numerator := (Primitives.numerator curve differential).eval parameter
  let weight := Data.Gaussian.Norm.Basic.normSq numerator + 1
  have weightPositive : 0 < weight := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  ⟨positive, numerator, rfl, weight, rfl,
    InverseRequest.build owned.channel (target / weight)
      (Fraction.Order.Field.div_pos_direct positive weightPositive) floor⟩

variable {owned : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data
  (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point curve parameter)}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {target : Coordinate} {floor
    index rootIndex : Nat} {box : Box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives in
/-- The derivative belongs to the supplied cached primitive; the root reading belongs to the same model channel used by
the cap overlap. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.ModelAgreement.CoefficientRequest owned
  differential target floor)
    (sample : Primitives.Sample data differential index box) (later : request.inverse.index ≤ index)
    (rootLater : request.inverse.comparison.rightIndex ≤ rootIndex) :
    Data.Gaussian.Norm.Basic.normSq ((GCD.derivative sample.primitive.value).eval parameter -
      request.numerator * Data.Gaussian.Field.inv ((Sampling.approximation owned.certificate.value.name).sample
        rootIndex)) < target := by
  have inverseError := request.inverse.accurate later rootLater
  have inverse_eq : sample.pulledInverse.eval parameter =
      (data.model.refine index).value.eval (Primitives.point curve parameter) := by
    rw [sample.pulledInverse_eq, sample.inverse_eq]
  rw [← inverse_eq, ← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at inverseError
  change Data.Gaussian.Norm.Basic.normSq
    (sample.pulledInverse.eval parameter -
      ((Sampling.approximation owned.certificate.value.name).sample rootIndex)⁻¹) < target / request.weight
        at inverseError
  rw [Data.Gaussian.Field.inv_eq] at inverseError
  have numerator_eq : request.numerator = -(degree curve : Gaussian) *
      parameter ^ (degree curve * (HyperellipticReciprocal.reversedDifferential differential).exponent) :=
    request.numerator_eq.trans (Primitives.numerator_eval curve differential parameter)
  rw [sample.primitive.derivative_eq, sample.coefficient_eq]
  unfold Primitives.coefficient
  rw [← numerator_eq]
  have scalarProduct :
      request.numerator * sample.pulledInverse.eval parameter -
        request.numerator * Data.Gaussian.Field.inv
          ((Sampling.approximation owned.certificate.value.name).sample rootIndex) =
      request.numerator * (sample.pulledInverse.eval parameter -
        Data.Gaussian.Field.inv
          ((Sampling.approximation owned.certificate.value.name).sample rootIndex)) := by ring1
  rw [scalarProduct, Data.Gaussian.Norm.Basic.normSq_mul]
  have weightPositive : 0 < request.weight := by
    rw [request.weight_eq]
    exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by
      decide)
  calc
    _ ≤ request.weight * Data.Gaussian.Norm.Basic.normSq (sample.pulledInverse.eval parameter -
        Data.Gaussian.Field.inv ((Sampling.approximation owned.certificate.value.name).sample rootIndex)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by rw [request.weight_eq]; exact le_add_of_nonneg_right (by decide)) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < request.weight * (target / request.weight) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct weightPositive inverseError
    _ = target := by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ weightPositive.ne'

end CoefficientRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ModelAgreement
