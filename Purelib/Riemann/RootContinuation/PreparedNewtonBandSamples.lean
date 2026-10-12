module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.ScaledRootBounds
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Sample.Dyadic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

public section

/-!
# Newton-band bounds for actual prepared integration samples

The canonical residual root and every persisted coefficient centre are
covered. The cell estimate retains its squared displacement, so a dyadic
side estimate pays the full growing cell count. Residual accuracy and actual
boundary membership are explicit internal obligations for the prepared
subdivision; this module does not assume that arbitrary coarse cells satisfy
them or claim to construct the final boundary program.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile Sample)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)

open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

/-- The exact scalar identity converting retained coefficient-density movement into linear rate and quadratic error
terms. -/
private theorem density_movement_identity {R : Type*} [CommRing R]
    (quotient radius scale numerator rate error : R)
    (quotientPaid : quotient * (scale * radius) = 4 * numerator)
    (ratePaid : rate * scale = 128 * numerator) :
    (2 * (quotient + 4 * error) * (32 * radius ^ 2)) * scale =
      (2 * rate * radius + 256 * error * radius ^ 2) * scale := by
  calc
    _ = 64 * radius * (quotient * (scale * radius)) + 256 * error * radius ^ 2 * scale := by ring1
    _ = 256 * numerator * radius + 256 * error * radius ^ 2 * scale := by rw [quotientPaid]; ring1
    _ = 2 * (rate * scale) * radius + 256 * error * radius ^ 2 * scale := by rw [ratePaid]; ring1
    _ = _ := by ring1

section
open Purelib.Data.Rat
/-- For a radius between zero and one and error at most one, the original quadratic error is at most the radius. -/
private theorem error_radius_bound {radius error : Fraction.Rational}
    (nonnegative : 0 ≤ radius) (radiusLe : radius ≤ 1) (errorLe : error ≤ 1) : error * radius ^ 2 ≤ radius := by
  calc
    _ ≤ 1 * radius ^ 2 := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      errorLe (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    _ = radius * radius := by rw [_root_.one_mul, pow_two]
    _ ≤ 1 * radius := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct radiusLe nonnegative
    _ = radius := _root_.one_mul _

/-- A nonnegative weighted quadratic error converts to the retained linear radius rate. -/
private theorem linear_rate_bound {radius error : Fraction.Rational} (rate weight : Fraction.Rational)
    (weightNonnegative : 0 ≤ weight) (nonnegative : 0 ≤ radius)
    (radiusLe : radius ≤ 1) (errorLe : error ≤ 1) :
    2 * rate * radius + weight * error * radius ^ 2 ≤ (2 * rate + weight) * radius := by
  calc
    _ = 2 * rate * radius + weight * (error * radius ^ 2) :=
      congrArg (2 * rate * radius + ·) (Fraction.Field.mul_assoc _ _ _)
    _ ≤ 2 * rate * radius + weight * radius := add_le_add le_rfl
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (error_radius_bound nonnegative radiusLe errorLe) weightNonnegative)
    _ = _ := (_root_.add_mul _ _ _).symm

end

namespace Sample

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {epsilon : Purelib.Data.Rat.Fraction.Rational}
  (sample : Sample profile epsilon)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- The original prepared residual-root center satisfies the scaled lower bound under its retained boundary and accuracy
certificates. -/
theorem prepared_root_lower (prepared : PreparedEdge curve differential)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box (prepared.point 0))
    (accurate : prepared.modelErrorAllowance ≤ (profile.scale * sample.output.radius) ^ 2 / 4) :
    profile.scale * sample.output.radius ≤ 4 * normSq prepared.residualRootCenter := by
  have residual := prepared.residualRootState_candidate_residual_lt 0
    prepared.baseInside prepared.residualRootCenter_possible
  rw [Norm.Basic.normSq_eq_canonical] at residual
  have divided : (profile.scale * sample.output.radius) ^ 2 / 4 ≤
      normSq (curve.polynomial.eval (prepared.point 0)) / 4 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (sample.radicand_lower boundary) (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)
  have residualBound : normSq (prepared.residualRootCenter * prepared.residualRootCenter -
      curve.polynomial.eval (prepared.point 0)) ≤ SquareRootSheets.residualTarget (curve.polynomial.eval (prepared.point
        0)) :=
    residual.le.trans (prepared.rootResidualTarget_le_modelErrorAllowance.trans
      (accurate.trans divided))
  exact ScaledRootBounds.scale_le_four_normSq (sample.radicand_lower boundary)
    (SquareRootSheets.normSq_lower_of_square_residual residualBound)

open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- The original prepared residual coefficient satisfies the retained Newton-band quotient bound. -/
theorem prepared_coefficient_bound (fixed : DifferentialProfile profile differential.exponent)
    (prepared : PreparedEdge curve differential)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box (prepared.point 0))
    (accurate : prepared.modelErrorAllowance ≤ (profile.scale * sample.output.radius) ^ 2 / 4) :
    normSq prepared.residualCoefficientCenter ≤ (4 * fixed.numerator) / (profile.scale * sample.output.radius) :=
  NewtonBandDifferentials.Sample.coefficient_bound sample fixed boundary
    (PreparedNewtonBandSamples.Sample.prepared_root_lower sample prepared boundary accurate)

open Purelib.Data.Rat in
/-- The original prepared coefficient-density bound, retaining the inverse-radius numerator term and separate error
allowance. -/
@[expose] def preparedDensity (fixed : DifferentialProfile profile differential.exponent) (error : Fraction.Rational) :
  Fraction.Rational :=
  2 * ((4 * fixed.numerator) / (profile.scale * sample.output.radius) + 4 * error)

section
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- The retained prepared density is nonnegative for a nonnegative original error allowance. -/
theorem preparedDensity_nonnegative (fixed : DifferentialProfile profile differential.exponent)
    {error : Fraction.Rational} (nonnegative : 0 ≤ error) : 0 ≤ PreparedNewtonBandSamples.Sample.preparedDensity sample
      fixed error :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.numerator_nonnegative)
      (Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive).le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative))

/-- The retained density times the original diameter bound equals the separate linear-rate and quadratic-error
expression. -/
theorem preparedDensity_movement (fixed : DifferentialProfile profile differential.exponent) (error : Fraction.Rational)
  :
    PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error * (32 * sample.output.radius ^ 2) =
      2 * fixed.rate * sample.output.radius + 256 * error * sample.output.radius ^ 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne profile.scalePositive.ne'
  exact density_movement_identity _ _ _ _ _ _
    (Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive).ne')
    fixed.rate_mul_scale

/-- For radius and error at most one, the original density-movement product is bounded by its retained linear rate. -/
theorem preparedDensity_movement_le (fixed : DifferentialProfile profile differential.exponent)
    {error : Fraction.Rational} (errorLe : error ≤ 1) (radiusLe : sample.output.radius ≤ 1) :
    PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error * (32 * sample.output.radius ^ 2) ≤
      (2 * fixed.rate + 256) * sample.output.radius := by
  rw [PreparedNewtonBandSamples.Sample.preparedDensity_movement sample fixed error]
  exact linear_rate_bound fixed.rate 256 (by decide +kernel)
    sample.output.radiusPositive.le radiusLe errorLe

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The exact original retained center reading satisfies the prepared density bound.

The original residual coefficient and its cached center discrepancy are bounded separately using the retained boundary
and accuracy certificates. -/
theorem prepared_center_bound (fixed : DifferentialProfile profile differential.exponent)
    (prepared : PreparedEdge curve differential) (center : PreparedEdge.CenterState prepared)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box (prepared.point 0)) {error : Fraction.Rational}
    (errorBound : prepared.modelErrorAllowance ≤ error)
    (accurate : error ≤ (profile.scale * sample.output.radius) ^ 2 / 4) :
    normSq center.value ≤ PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error := by
  have discrepancy := PreparedPrimitiveSamples.center_sub_canonical_le prepared center
  have canonical := PreparedNewtonBandSamples.Sample.prepared_coefficient_bound sample fixed prepared boundary
    (errorBound.trans accurate)
  have triangle := Norm.Bounds.normSq_add_le_two prepared.residualCoefficientCenter (center.value -
    prepared.residualCoefficientCenter)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  have identity : center.value = prepared.residualCoefficientCenter + (center.value -
    prepared.residualCoefficientCenter) := by ring1
  calc
    normSq center.value = normSq (prepared.residualCoefficientCenter + (center.value -
      prepared.residualCoefficientCenter)) :=
      congrArg normSq identity
    _ ≤ 2 * (normSq prepared.residualCoefficientCenter + normSq (center.value - prepared.residualCoefficientCenter)) :=
      triangle
    _ ≤ PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add canonical (discrepancy.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorBound (by decide)))) (by decide)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.RootContinuation in
/-- An original centered child integral has squared norm bounded by retained density times its exact point movement. -/
theorem prepared_integral_bound (fixed : DifferentialProfile profile differential.exponent)
    (child : CenteredEdge curve differential)
    (boundary : Box.Boundary.OnBoxBoundary sample.output.box (child.edge.point 0)) {error : Fraction.Rational}
    (errorBound : child.edge.modelErrorAllowance ≤ error)
    (accurate : error ≤ (profile.scale * sample.output.radius) ^ 2 / 4) :
    normSq child.model.integralSample ≤ PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error *
      child.edge.pointMovement := by
  rw [Cell.Basic.CellModel.integralSample_constant
    child.model child.center.value rfl, Basic.Canonical.normSq_mul]
  have coefficient := PreparedNewtonBandSamples.Sample.prepared_center_bound sample fixed child.edge child.center
    boundary errorBound accurate
  change normSq (child.edge.point 1 - child.edge.point 0) * normSq child.center.value ≤ _
  calc
    _ ≤ normSq (child.edge.point 1 - child.edge.point 0) * PreparedNewtonBandSamples.Sample.preparedDensity sample fixed
      error :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient (Basic.Canonical.normSq_nonneg _)
    _ = _ := by
      unfold PreparedEdge.pointMovement
      rw [Norm.Basic.normSq_eq_canonical]
      exact Fraction.Field.mul_comm _ _

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.RootContinuation in
/-- An original dyadic child-model integral sum is bounded by the common retained density and parent movement.

The exact child count, boundary locations, error allowances and geometric movement bounds are retained for every
original list member. -/
theorem dyadic_prepared_integral_bound (fixed : DifferentialProfile profile differential.exponent)
    (children : List (CenteredEdge curve differential)) (depth : Nat) (count : children.length = 2 ^ depth)
    (movement error : Fraction.Rational) (errorNonnegative : 0 ≤ error)
    (boundary : ∀ child ∈ children, Box.Boundary.OnBoxBoundary sample.output.box (child.edge.point 0))
    (errors : ∀ child ∈ children, child.edge.modelErrorAllowance ≤ error)
    (accurate : error ≤ (profile.scale * sample.output.radius) ^ 2 / 4)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ Geometric.Basic.quarterRadius movement depth) :
    normSq (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample ≤
      PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error * movement := by
  rw [← Norm.Basic.normSq_eq_canonical]
  apply Sample.Dyadic.dyadic_integral_norm_le _ depth
    (by rw [Map.length_map]; exact count) movement (PreparedNewtonBandSamples.Sample.preparedDensity sample fixed error)
  intro cell member
  change cell ∈ children.map CenteredEdge.model at member
  obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
  have bound := (PreparedNewtonBandSamples.Sample.prepared_integral_bound sample fixed child (boundary child inChildren)
    (errors child inChildren) accurate).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (movements child inChildren)
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative sample fixed errorNonnegative))
  simpa only [Norm.Basic.normSq_eq_canonical] using bound

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.RootContinuation in
/-- The original dyadic child-model integral obeys the retained linear band-radius rate. -/
theorem dyadic_prepared_integral_rate (fixed : DifferentialProfile profile differential.exponent)
    (children : List (CenteredEdge curve differential)) (depth : Nat) (count : children.length = 2 ^ depth)
    (movement error : Fraction.Rational) (errorNonnegative : 0 ≤ error) (errorLe : error ≤ 1)
    (radiusLe : sample.output.radius ≤ 1) (movementLe : movement ≤ 32 * sample.output.radius ^ 2)
    (boundary : ∀ child ∈ children, Box.Boundary.OnBoxBoundary sample.output.box (child.edge.point 0))
    (errors : ∀ child ∈ children, child.edge.modelErrorAllowance ≤ error)
    (accurate : error ≤ (profile.scale * sample.output.radius) ^ 2 / 4)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ Geometric.Basic.quarterRadius movement depth) :
    normSq (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample ≤
      (2 * fixed.rate + 256) * sample.output.radius :=
  (PreparedNewtonBandSamples.Sample.dyadic_prepared_integral_bound sample fixed children depth count movement error
    errorNonnegative
    boundary errors accurate movements).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movementLe
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative sample fixed errorNonnegative)).trans
      (PreparedNewtonBandSamples.Sample.preparedDensity_movement_le sample fixed errorLe radiusLe))

end Sample

set_option genInjectivity false in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- A retained differential-specific Newton band with positive error allowance and exact target payment.

The original sample, radius-at-most-one and accuracy certificates share the same profile and cached error; the payment
uses the original differential rate plus its fixed error coefficient. -/
structure PreparedBandRequest {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {exponent : Nat}
    (fixed : DifferentialProfile profile exponent) (target : Fraction.Rational) where
  /-- The retained positive request size passed to the original profile. -/ requestSize : Fraction.Rational
  /-- The original request size is strictly positive. -/ requestPositive : 0 < requestSize
  /-- The exact retained Newton-band extraction sample. -/ sample : Sample profile requestSize
  /-- The actual retained sample radius is at most one. -/ radius_le_one : sample.output.radius ≤ 1
  /-- The retained positive prepared-model error allowance. -/ error : Fraction.Rational
  /-- The original cached error allowance is strictly positive. -/ errorPositive : 0 < error
  /-- The retained error allowance is at most one. -/ error_le_one : error ≤ 1
  /-- The error is at most one quarter of the squared original scaled sample radius. -/ error_accurate : error ≤
    (profile.scale * sample.output.radius) ^ 2 / 4
  /-- The original retained rate and actual size or sample radius pay the exact target. -/ paid : (2 * fixed.rate + 256)
    * sample.output.radius ≤ target

constructive_injectivity PreparedBandRequest

set_option genInjectivity false in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- A retained Newton-band selection with separate rate, target and radius limits.

The stored sample and positive error allowance retain their exact scale/radius accuracy certificate, while the request
size and payment preserve the original external bounds. -/
structure PreparedBandSelection {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    (profile : Profile squarefree current.box) (rate target radius : Fraction.Rational) where
  /-- The retained positive request size passed to the original profile. -/ requestSize : Fraction.Rational
  /-- The original request size is strictly positive. -/ requestPositive : 0 < requestSize
  /-- The retained requested size is at most the original radius limit. -/ request_le_radius : requestSize ≤ radius
  /-- The exact retained Newton-band extraction sample. -/ sample : Sample profile requestSize
  /-- The actual retained sample radius is at most one. -/ radius_le_one : sample.output.radius ≤ 1
  /-- The retained positive prepared-model error allowance. -/ error : Fraction.Rational
  /-- The original cached error allowance is strictly positive. -/ errorPositive : 0 < error
  /-- The retained error allowance is at most one. -/ error_le_one : error ≤ 1
  /-- The error is at most one quarter of the squared original scaled sample radius. -/ error_accurate : error ≤
    (profile.scale * sample.output.radius) ^ 2 / 4
  /-- The original retained rate and actual size or sample radius pay the exact target. -/ paid : rate *
    sample.output.radius ≤ target

constructive_injectivity PreparedBandSelection

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- A positive retained band request size bounded by the original radius and one, with exact rate payment. -/
structure PreparedBandBudget (rate target radius : Fraction.Rational) where
  /-- The retained scalar request size. -/ size : Fraction.Rational
  /-- The retained request size is strictly positive. -/ positive : 0 < size
  /-- The retained size is at most the original radius bound. -/ le_radius : size ≤ radius
  /-- The retained size is at most one. -/ le_one : size ≤ 1
  /-- The original retained rate and actual size or sample radius pay the exact target. -/ paid : rate * size ≤ target

constructive_injectivity PreparedBandBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Choose the minimum of the original radius, one and the weighted target allowance.

The retained minimum preserves strict positivity, both size bounds and the original nonnegative-rate payment. -/
@[expose] def PreparedBandBudget.build (rate : Fraction.Rational) (rateNonnegative : 0 ≤ rate)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) : PreparedBandBudget rate
      target radius :=
  let size := min radius (min 1 (Budget.Weighted.allowance target rate))
  { size := size
    positive := Fraction.Order.Basic.lt_min radiusPositive (Fraction.Order.Basic.lt_min (by decide)
      (Budget.Weighted.allowance_positive positive rateNonnegative))
    le_radius := Fraction.Order.Basic.min_le_left _ _
    le_one := (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
    paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)) rateNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le rateNonnegative) }

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Extract a Newton band using the retained scalar budget and choose its exact positive root-error allowance.

The original sample radius determines the error minimum. The returned selection retains the same sample, request radius
limit and original target payment. -/
@[expose] def Profile.requestPreparation {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    (profile : Profile squarefree current.box) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) (rate :
      Fraction.Rational) (rateNonnegative : 0 ≤ rate)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    PreparedBandSelection profile rate target radius := by
  let budget := PreparedBandBudget.build rate rateNonnegative positive radiusPositive
  let requestSize := budget.size
  have requestPositive : 0 < requestSize := budget.positive
  let sample := profile.request degreeAtLeastTwo elimination requestPositive
  have radiusBound : sample.output.radius ≤ requestSize := sample.radius_le.trans (by
    calc
      (1 / 8 : Fraction.Rational) * requestSize ≤ 1 * requestSize :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) requestPositive.le
      _ = requestSize := _root_.one_mul _)
  let error := min 1 ((profile.scale * sample.output.radius) ^ 2 / 4)
  exact
    { requestSize := requestSize
      requestPositive := requestPositive
      request_le_radius := budget.le_radius
      sample := sample
      radius_le_one := radiusBound.trans budget.le_one
      error := error
      errorPositive := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Arithmetic.pow_pos_direct
          (Fraction.Order.Arithmetic.mul_pos_direct profile.scalePositive sample.output.radiusPositive) 2) (by decide))
      error_le_one := Fraction.Order.Basic.min_le_left _ _
      error_accurate := Fraction.Order.Basic.min_le_right _ _
      paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusBound rateNonnegative).trans budget.paid }

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Specialize the retained band selection to an original differential whose rate fits its paid rate.

The exact sample, request and error caches are reused; only the payment certificate is transported through the supplied
rate inequality. -/
@[expose] def PreparedBandSelection.forDifferential {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {rate target radius : Fraction.Rational}
    (selection : PreparedBandSelection profile rate target radius) {exponent : Nat}
    (fixed : DifferentialProfile profile exponent) (rateBound : 2 * fixed.rate + 256 ≤ rate) : PreparedBandRequest fixed
      target where
  requestSize := selection.requestSize
  requestPositive := selection.requestPositive
  sample := selection.sample
  radius_le_one := selection.radius_le_one
  error := selection.error
  errorPositive := selection.errorPositive
  error_le_one := selection.error_le_one
  error_accurate := selection.error_accurate
  paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rateBound
    selection.sample.output.radiusPositive.le).trans selection.paid

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- Request a prepared differential band using its original rate and fixed error coefficient.

The retained generic selection uses radius limit one and is specialized without rebuilding its sample or error caches.
-/
@[expose] def DifferentialProfile.requestPrepared {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {degreeBound : Nat}
    {squarefree : Squarefree.Basic.SquarefreeCertificate p} {current : State.Raw.RawWindingState p ambient}
    {profile : Profile squarefree current.box} {exponent : Nat}
    (fixed : DifferentialProfile profile exponent) (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) {target :
      Fraction.Rational}
    (positive : 0 < target) : PreparedBandRequest fixed target :=
  let rate := 2 * fixed.rate + 256
  have rateNonnegative : 0 ≤ rate := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.rate_nonnegative) (by decide +kernel)
  let selection := PreparedNewtonBandSamples.Profile.requestPreparation profile degreeAtLeastTwo elimination rate
    rateNonnegative positive
    (by decide : (0 : Fraction.Rational) < 1)
  selection.forDifferential fixed le_rfl

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- The original dyadic prepared integral sum satisfies the retained band's paid target.

Its exact child count, boundary locations, error bounds and geometric movement certificates supply the stored
radius-rate estimate. -/
theorem PreparedBandRequest.bound {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {ambient : Box} {current :
      State.Raw.RawWindingState curve.polynomial ambient}
    {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
    {target : Fraction.Rational} (request : PreparedBandRequest fixed target)
    (children : List (CenteredEdge curve differential)) (depth : Nat) (count : children.length = 2 ^ depth)
    (movement : Fraction.Rational) (movementLe : movement ≤ 32 * request.sample.output.radius ^ 2)
    (boundary : ∀ child ∈ children, Box.Boundary.OnBoxBoundary request.sample.output.box (child.edge.point 0))
    (errors : ∀ child ∈ children, child.edge.modelErrorAllowance ≤ request.error)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ Geometric.Basic.quarterRadius movement depth) :
    normSq (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample ≤ target :=
  (PreparedNewtonBandSamples.Sample.dyadic_prepared_integral_rate request.sample fixed children depth count movement
    request.error
    request.errorPositive.le request.error_le_one request.radius_le_one movementLe
      boundary errors request.error_accurate movements).trans request.paid

end Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
