module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Product
public import Purelib.Approximation.Gaussian.Request.Multiplication
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Bounds
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Residual requests paying the actual retained product radius

The original multiplication request uses both supplied root processes' global
centre bounds. Each original square-root residual request is made smaller
than both its residual ceiling and its sensitivity-scaled radius request.
The resulting observations retain their original states; their actual paired
product Reading meets the output radius without another refinement.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Rational.Request

/-- The original finite zero-centred oracle retaining the supplied root process's unchanged centre bound. -/
@[expose] def centerName {parameter : Canonical} (root : Certificate parameter) : Request.Basic.Name :=
  Request.Basic.Name.centerOnly 0 root.value.name.process.centerBound
    root.value.name.process.centerBound_nonneg (by
      rewrite [Norm.Basic.normSq_zero]
      exact root.value.name.process.centerBound_nonneg)

/-- The original common multiplication input request on the two retained complete root certificates. -/
@[expose] def productInputTarget {firstParameter lastParameter : Canonical}
    (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter)
    (output : AccuracyRequest) : Fraction.Rational :=
  Request.Basic.Name.multiplicativeInputTarget (centerName firstRoot) (centerName lastRoot) output.tolerance

/-- The actual common multiplication input request is positive. -/
theorem productInputTarget_positive {firstParameter lastParameter : Canonical}
    (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter) (output : AccuracyRequest) :
    0 < productInputTarget firstRoot lastRoot output :=
  Request.Basic.Name.multiplicativeInputTarget_pos _ _ output.positive

/-- The original residual request simultaneously pays its supplied residual ceiling and radius sensitivity. -/
def jointRequest {parameter : Canonical} (root : Certificate parameter)
    (residual radius : AccuracyRequest) : AccuracyRequest :=
  ⟨Common.commonTarget residual.tolerance (radiusDenominator root * radius.tolerance),
    Common.commonTarget_pos residual.positive
      (Fraction.Order.Arithmetic.mul_pos_direct (radiusDenominator_pos root) radius.positive)⟩

/-- The joint original residual tolerance is strictly below the supplied residual ceiling. -/
theorem jointRequest_residual_lt {parameter : Canonical} (root : Certificate parameter)
    (residual radius : AccuracyRequest) : (jointRequest root residual radius).tolerance < residual.tolerance :=
  Common.commonTarget_lt_left residual.positive
    (Fraction.Order.Arithmetic.mul_pos_direct (radiusDenominator_pos root) radius.positive)

/-- The joint residual tolerance makes its original radius request strictly smaller than the supplied radius. -/
theorem jointRequest_radius_lt {parameter : Canonical} (root : Certificate parameter)
    (residual radius : AccuracyRequest) :
    (radiusRequest root (jointRequest root residual radius)).tolerance < radius.tolerance := by
  apply (Fraction.Order.Field.div_lt_iff_pos (radiusDenominator_pos root)).mpr
  have paid := Common.commonTarget_lt_right residual.positive
    (Fraction.Order.Arithmetic.mul_pos_direct (radiusDenominator_pos root) radius.positive)
  exact paid.trans_eq (Fraction.Field.mul_comm _ _)

/-- The exact common multiplication input as an original positive AccuracyRequest. -/
def productInputRequest {firstParameter lastParameter : Canonical}
    (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter)
    (output : AccuracyRequest) : AccuracyRequest :=
  ⟨productInputTarget firstRoot lastRoot output, productInputTarget_positive firstRoot lastRoot output⟩

/-- The original product input request reads the same computed multiplication tolerance. -/
theorem productInputRequest_tolerance {firstParameter lastParameter : Canonical}
    (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter) (output : AccuracyRequest) :
    (productInputRequest firstRoot lastRoot output).tolerance = productInputTarget firstRoot lastRoot output := by
  unfold productInputRequest
  rfl

/-- Retained common input and both original joint residual requests with exact complete factory identities. -/
@[expose] def ProductRequests {firstParameter lastParameter : Canonical}
    (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter)
    (firstResidual lastResidual output : AccuracyRequest) :=
  Σ input : { retained : AccuracyRequest // retained = productInputRequest firstRoot lastRoot output },
    { retained : AccuracyRequest × AccuracyRequest //
        retained = (jointRequest firstRoot firstResidual input.val, jointRequest lastRoot lastResidual input.val) }

namespace ProductRequests

variable {firstParameter lastParameter : Canonical}
variable {firstRoot : Certificate firstParameter} {lastRoot : Certificate lastParameter}
variable {firstResidual lastResidual output : AccuracyRequest}

/-- Retain an already computed common input and both complete original joint requests without rebuilding them. -/
@[expose] def ofCompleted (input : AccuracyRequest)
    (input_eq : input = productInputRequest firstRoot lastRoot output)
    (first last : AccuracyRequest)
    (requests_eq : (first, last) =
      (jointRequest firstRoot firstResidual input, jointRequest lastRoot lastResidual input)) :
    ProductRequests firstRoot lastRoot firstResidual lastResidual output :=
  ⟨⟨input, input_eq⟩, ⟨(first, last), requests_eq⟩⟩

/-- Compute the common multiplication request once and retain both exact original residual/radius joint requests. -/
def build (firstRoot : Certificate firstParameter) (lastRoot : Certificate lastParameter)
    (firstResidual lastResidual output : AccuracyRequest) :
    ProductRequests firstRoot lastRoot firstResidual lastResidual output :=
  let input := productInputRequest firstRoot lastRoot output
  let first := jointRequest firstRoot firstResidual input
  let last := jointRequest lastRoot lastResidual input
  ofCompleted input rfl first last rfl

/-- Read the identical common positive multiplication input request. -/
@[expose] def input (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) := requests.1.val

/-- Read the original first factor's separately retained residual/radius joint request. -/
@[expose] def first (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :=
  requests.2.val.1

/-- Read the original second factor's separately retained residual/radius joint request. -/
@[expose] def last (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) := requests.2.val.2

/-- The common input cache is the complete original factory on the same two original root processes. -/
theorem input_eq (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :
    requests.input = productInputRequest firstRoot lastRoot output := requests.1.property

/-- The first factor request is the original complete joint constructor on the same retained input request. -/
theorem first_eq (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :
    requests.first = jointRequest firstRoot firstResidual requests.input := congrArg Prod.fst requests.2.property

/-- The second factor request is its separate original complete joint constructor on that identical common input. -/
theorem last_eq (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :
    requests.last = jointRequest lastRoot lastResidual requests.input := congrArg Prod.snd requests.2.property

/-- The first retained request pays the original first residual ceiling. -/
theorem first_residual_lt (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :
    requests.first.tolerance < firstResidual.tolerance := by
  rewrite [requests.first_eq]
  exact jointRequest_residual_lt _ _ _

/-- The second retained request pays the distinct original second residual ceiling. -/
theorem last_residual_lt (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output) :
    requests.last.tolerance < lastResidual.tolerance := by
  rewrite [requests.last_eq]
  exact jointRequest_residual_lt _ _ _

/-- Original observations on these exact requests meet the output radius on their unchanged paired-product Reading. -/
theorem product_radius_lt (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output)
    (first : ResidualObservation firstRoot requests.first) (last : ResidualObservation lastRoot requests.last)
    (value : Name.Coherent.CoherentNamed) (retained : value = firstRoot.value.mul lastRoot.value) :
    (first.productReading last value retained).radius < output.tolerance := by
  have firstRadius : (radiusRequest firstRoot requests.first).tolerance < requests.input.tolerance := by
    rewrite [requests.first_eq]
    exact jointRequest_radius_lt firstRoot firstResidual requests.input
  have lastRadius : (radiusRequest lastRoot requests.last).tolerance < requests.input.tolerance := by
    rewrite [requests.last_eq]
    exact jointRequest_radius_lt lastRoot lastResidual requests.input
  have firstBound := first.radius_lt.trans firstRadius
  have lastBound := last.radius_lt.trans lastRadius
  rewrite [requests.input_eq, productInputRequest_tolerance] at firstBound lastBound
  have radius : (first.productReading last value retained).radius =
      ((firstRoot.value.name.process.ball first.state).mul
        (lastRoot.value.name.process.ball last.state)).radiusSq := by
    cases retained
    rfl
  rewrite [radius]
  exact Request.Basic.Name.mul_radius_lt (centerName firstRoot) (centerName lastRoot) _ _ output.positive
    firstBound lastBound (firstRoot.value.name.process.center_bounded first.state)
    (lastRoot.value.name.process.center_bounded last.state)

/-- Actual later observations pay this product request using the SAME two retained earlier radius comparisons.

The later observations keep their independent original residual requests
and actual states. Their selected-index orders transport the earlier paid
radius bounds to those states; the product Reading itself is unchanged.
-/
theorem product_radius_lt_after (requests : ProductRequests firstRoot lastRoot firstResidual lastResidual output)
    (firstPaid : ResidualObservation firstRoot requests.first)
    (lastPaid : ResidualObservation lastRoot requests.last)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : ResidualObservation firstRoot firstAccuracy) (last : ResidualObservation lastRoot lastAccuracy)
    (firstAfter : firstPaid.comparison.leftIndex ≤ first.comparison.leftIndex)
    (lastAfter : lastPaid.comparison.leftIndex ≤ last.comparison.leftIndex)
    (value : Name.Coherent.CoherentNamed) (retained : value = firstRoot.value.mul lastRoot.value) :
    (first.productReading last value retained).radius < output.tolerance := by
  have firstRadius : (radiusRequest firstRoot requests.first).tolerance < requests.input.tolerance := by
    rewrite [requests.first_eq]
    exact jointRequest_radius_lt firstRoot firstResidual requests.input
  have lastRadius : (radiusRequest lastRoot requests.last).tolerance < requests.input.tolerance := by
    rewrite [requests.last_eq]
    exact jointRequest_radius_lt lastRoot lastResidual requests.input
  have firstBound := (firstPaid.radius_lt_after first firstAfter).trans firstRadius
  have lastBound := (lastPaid.radius_lt_after last lastAfter).trans lastRadius
  rewrite [requests.input_eq, productInputRequest_tolerance] at firstBound lastBound
  have radius : (first.productReading last value retained).radius =
      ((firstRoot.value.name.process.ball first.state).mul
        (lastRoot.value.name.process.ball last.state)).radiusSq := by
    cases retained
    rfl
  rewrite [radius]
  exact Request.Basic.Name.mul_radius_lt (centerName firstRoot) (centerName lastRoot) _ _ output.positive
    firstBound lastBound (firstRoot.value.name.process.center_bounded first.state)
    (lastRoot.value.name.process.center_bounded last.state)

end ProductRequests

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
