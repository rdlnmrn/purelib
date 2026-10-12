module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
public import Purelib.Approximation.Request.PairedFloors
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PrimitiveSamples

public section

/-!
# Requested cap endpoint values on the actual inverse boundary

The local inverse is the one retained by the original reciprocal cell.
The cap inverse and factor come from one shared polynomial sample. Both
root requests are prepared before that sample's stage is selected, and the
existing quotient coordinate is retained throughout the comparison.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Apart

open Purelib.Approximation.Request

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell source edge}
  {model : RootModel cell} {parameter :
    Coordinate}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owned : Point cap model
    parameter}

set_option genInjectivity false in
/-- The original endpoint radicand and inverse-product and coefficient ceilings.

All cached bounds refer to the actual retained reciprocal root channel and shared regular cap model before choosing a
polynomial stage. -/
structure Data (regular : RegularBounds.Data cap) (owned : Point cap model parameter) where
  /-- The cached original reciprocal radicand at the actual inverse source point. -/ radicand :
    InverseRootPolynomial.Gaussian
  /-- The cached radicand equals the original reciprocal curve polynomial at this endpoint. -/ radicand_eq : radicand =
    (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹
  /-- The cached squared-norm ceiling for the original reciprocal root inverse. -/ inverseUpper :
    InverseRootPolynomial.Coordinate
  /-- The inverse ceiling is exactly the reciprocal of the original root apartness lower bound. -/ inverseUpper_eq :
    inverseUpper = owned.root.channel.certificate.apart.certificate.lowerSq⁻¹
  /-- The cached discrepancy scale for the original paired inverse product. -/ productScale :
    InverseRootPolynomial.Coordinate
  /-- The product scale is twice the original radicand squared norm times the sum of the retained inverse ceilings. -/
    productScale_eq : productScale = 2 * Data.Gaussian.Norm.Basic.normSq radicand * (regular.inverseUpper +
    inverseUpper)
  /-- The cached squared-norm ceiling for the original endpoint primitive coefficient. -/ coefficientUpper :
    InverseRootPolynomial.Coordinate
  /-- The coefficient ceiling uses the actual inverse coordinate power and the shared original cap factor bound. -/
    coefficientUpper_eq : coefficientUpper = Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^
    (1 - HyperellipticReciprocal.originOrder curve)) * regular.factorUpper

constructive_injectivity Data

namespace Data

/-- Cache the original endpoint radicand, inverse ceiling and coefficient-adjusted product scale. -/
@[expose] def build (regular : RegularBounds.Data cap) (owned : Point cap model parameter) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned :=
  let parameterValue := owned.root.channel.samples.parameter
  let inverseUpper := owned.root.channel.certificate.apart.certificate.lowerSq⁻¹
  ⟨parameterValue, owned.root.channel.samples.parameter_eq, inverseUpper, rfl,
    2 * Data.Gaussian.Norm.Basic.normSq parameterValue * (regular.inverseUpper + inverseUpper), rfl,
    Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^ (1 - HyperellipticReciprocal.originOrder
      curve)) * regular.factorUpper, rfl⟩

/-- The retained original root apartness gives a positive inverse ceiling. -/
theorem inverseUpper_positive (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned)
  : 0 < data.inverseUpper := by
  rw [data.inverseUpper_eq]
  exact Fraction.Order.Field.inv_pos_direct owned.root.channel.certificate.apart.certificate.positive

/-- The cached original radicand and inverse ceilings give a nonnegative product scale. -/
theorem productScale_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular
  owned) : 0 ≤ data.productScale := by
  rw [data.productScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
    (add_nonneg regular.inverseUpper_positive.le data.inverseUpper_positive.le)

/-- The cached original coordinate power and factor ceiling give a nonnegative endpoint coefficient bound. -/
theorem coefficientUpper_nonnegative (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular
  owned) : 0 ≤ data.coefficientUpper := by
  rw [data.coefficientUpper_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    regular.factorUpper_nonnegative

/-- Every inverse reading of the original retained reciprocal root satisfies its cached ceiling. -/
theorem inverse_le (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned) (index :
  Nat) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Field.inv ((Sampling.approximation
      owned.root.channel.certificate.value.name).sample index)) ≤ data.inverseUpper := by
  rw [data.inverseUpper_eq, Data.Gaussian.Field.normSq_inv _
    (Sampling.sampled_nonzero owned.root.channel.certificate.value owned.root.channel.certificate.apart index)]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct owned.root.channel.certificate.apart.certificate.positive
    (Sampling.sampled_lower owned.root.channel.certificate.value owned.root.channel.certificate.apart index)

/-- The retained endpoint coefficient satisfies the original shared regular-cap factor ceiling. -/
theorem coefficient_le (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned) {index
  : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (endpoint : Coordinates.Overlap.Endpoint owned.coordinates capSample) :
    Data.Gaussian.Norm.Basic.normSq endpoint.coefficient ≤ data.coefficientUpper := by
  rw [endpoint.coefficient_eq, endpoint.factor_eq, data.coefficientUpper_eq, Data.Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (regular.factor_bound capSample owned.coordinates.regular.inside) (Data.Gaussian.Norm.Basic.normSq_nonneg _)

end Data

/-- Paired inverse-root requests and an independent coordinate comparison for the original retained endpoint.

The reciprocal root keeps its two-stage offset and each reading retains its own floor, while one common polynomial stage
pays the coefficient-adjusted target. -/
abbrev Request (data : Data regular owned) (target :
  InverseRootPolynomial.Coordinate) (floor : Nat) :=
  PairedFloors.RequestData data.coefficientUpper data.productScale
    (fun rootTarget => InverseModelRootRequests.InverseRequest owned.root.channel rootTarget floor)
    (fun rootTarget => InverseModelRootRequests.InverseRequest owned.coordinates.regular.channel rootTarget floor)
    (fun _ request => 2 + request.index) (fun _ request => request.comparison.rightIndex)
    (fun _ request => request.index) (fun _ request => request.comparison.rightIndex)
    (CoordinateSamples.inverseProduct owned.root.channel.certificate
      owned.coordinates.regular.certificate).toApproximation
    (Sampling.approximation owned.coordinates.coordinate.prepared.denominator.name) target floor

namespace Request

/-- Request both retained inverse roots and their original quotient coordinate with independent reading floors and one
paid polynomial stage. -/
@[expose] def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request data target floor :=
  let budget := target / (4 * (data.coefficientUpper + 1))
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.coefficientUpper_nonnegative (by decide)))
  let rootTarget := budget / (data.productScale + 1)
  have rootPositive : 0 < rootTarget := Fraction.Order.Field.div_pos_direct budgetPositive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.productScale_nonnegative (by decide))
  let reciprocal := InverseRequest.build owned.root.channel rootTarget rootPositive floor
  let regular := InverseRequest.build owned.coordinates.regular.channel rootTarget rootPositive floor
  let coordinate := (CoordinateSamples.inverseProduct_equivalent owned.coordinates.coordinate
    owned.root.channel.certificate (by
    rw [owned.coordinates.reciprocal_eq]
    exact owned.root.channel.owner_equivalent.symm)).compare
      (max reciprocal.comparison.rightIndex regular.comparison.rightIndex) floor budget budgetPositive
  ⟨positive, budget, rfl, rootTarget, rfl, reciprocal, regular, coordinate, max (2 + reciprocal.index) regular.index,
    rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular owned} {target :
  Coordinate} {floor : Nat}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}

/-- The retained endpoint request stage respects the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request data target floor) :
  floor ≤ request.index := by
  rw [request.index_eq]
  exact (request.reciprocal.floor_le.trans (Nat.le_add_left _ _)).trans (Data.Nat.Order.le_max_left _ _)

/-- At every later common polynomial stage, the retained inverse-polynomial product approximates its original sampled
coordinate product within budget. -/
private theorem model_product_error (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request
  data target floor) {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : ArcSamples.Sample comparison capSample) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (data.radicand * sample.retained.inverse.value.eval (parent.edge.point
      parameter)⁻¹ *
      capSample.inverse.value.eval (parent.edge.point parameter)⁻¹ -
      (CoordinateSamples.inverseProduct owned.root.channel.certificate owned.coordinates.regular.certificate).sample
        request.coordinate.leftIndex) < request.budget := by
  let point := (parent.edge.point parameter)⁻¹
  let first := sample.retained.inverse.value.eval point
  let second := capSample.inverse.value.eval point
  let left := Data.Gaussian.Field.inv ((Sampling.approximation
    owned.root.channel.certificate.value.name).sample request.coordinate.leftIndex)
  let right := Data.Gaussian.Field.inv ((Sampling.approximation
    owned.coordinates.regular.certificate.value.name).sample request.coordinate.leftIndex)
  have indices := later
  rw [request.index_eq] at indices
  have firstClose : Data.Gaussian.Norm.Basic.normSq (first - left) < request.rootTarget :=
    owned.inverse_accurate sample request.reciprocal ((Data.Nat.Order.le_max_left _ _).trans indices)
      ((Data.Nat.Order.le_max_left _ _).trans request.coordinate.left_ge)
  have secondClose : Data.Gaussian.Norm.Basic.normSq (second - right) < request.rootTarget :=
    owned.coordinates.regular.inverse_accurate capSample request.regular ((Data.Nat.Order.le_max_right _ _).trans
      indices)
      ((Data.Nat.Order.le_max_right _ _).trans request.coordinate.left_ge)
  have secondBound : Data.Gaussian.Norm.Basic.normSq second ≤ regular.inverseUpper := by
    dsimp only [second]
    rw [capSample.inverse_eq]
    exact regular.inverse_bound index owned.coordinates.regular.inside
  have leftBound := data.inverse_le request.coordinate.leftIndex
  have estimate : Data.Gaussian.Norm.Basic.normSq (first * second - left * right) ≤
      2 * (request.rootTarget * regular.inverseUpper + data.inverseUpper * request.rootTarget) := by
    rw [show first * second - left * right = (first - left) * second + left * (second - right) by ring1]
    apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
    exact add_le_add
      (Fraction.Order.Arithmetic.mul_le_mul_direct firstClose.le secondBound (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        request.reciprocal.positive.le)
      (Fraction.Order.Arithmetic.mul_le_mul_direct leftBound secondClose.le (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        data.inverseUpper_positive.le)
  have stream_eq : (CoordinateSamples.inverseProduct owned.root.channel.certificate
    owned.coordinates.regular.certificate).sample
      request.coordinate.leftIndex = data.radicand * left * right :=
    (CoordinateSamples.inverseProduct_sample _ _ _).trans
      (congrArg (fun parameter => parameter * left * right) data.radicand_eq.symm)
  rw [stream_eq,
    show data.radicand * first * second - data.radicand * left * right = data.radicand * (first * second - left * right)
      by ring1,
    Data.Gaussian.Norm.Basic.normSq_mul]
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct estimate (Data.Gaussian.Norm.Basic.normSq_nonneg
    _)).trans_lt
  have algebra : Data.Gaussian.Norm.Basic.normSq data.radicand * (2 * (request.rootTarget *
    regular.inverseUpper +
      data.inverseUpper * request.rootTarget)) = data.productScale * request.rootTarget := by
    calc
      _ = (2 * Data.Gaussian.Norm.Basic.normSq data.radicand * (regular.inverseUpper + data.inverseUpper)) *
        request.rootTarget := by
        ring1
      _ = _ := congrArg (fun scale => scale * request.rootTarget) data.productScale_eq.symm
  rw [algebra]
  have positive := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.productScale_nonnegative (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 1)
  calc
    _ < (data.productScale + 1) * request.rootTarget :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by
          simpa only [_root_.add_zero] using
            Fraction.Order.Arithmetic.add_lt_add_left_direct
              (by decide : (0 : InverseRootPolynomial.Coordinate) < 1) data.productScale)
        request.reciprocal.positive
    _ = request.budget := by
      rw [request.rootTarget_eq, Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

/-- The retained inverse polynomials approximate the actual root coordinate before multiplication by any differential
coefficient. -/
theorem coordinate_close (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request data target
  floor) {index coordinateIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : ArcSamples.Sample comparison capSample)
    (later : request.index ≤ index) (coordinateLater : request.coordinate.rightIndex ≤ coordinateIndex) :
    Data.Gaussian.Norm.Basic.normSq (data.radicand * sample.retained.inverse.value.eval (parent.edge.point
      parameter)⁻¹ *
      capSample.inverse.value.eval (parent.edge.point parameter)⁻¹ -
      (Sampling.approximation owned.coordinates.coordinate.prepared.denominator.name).sample coordinateIndex) < 4 *
        request.budget := by
  let point := (parent.edge.point parameter)⁻¹
  let product := data.radicand * sample.retained.inverse.value.eval point * capSample.inverse.value.eval point
  let middle := (CoordinateSamples.inverseProduct owned.root.channel.certificate
    owned.coordinates.regular.certificate).sample request.coordinate.leftIndex
  let coordinateReading := (Sampling.approximation owned.coordinates.coordinate.prepared.denominator.name).sample
    coordinateIndex
  have first := request.model_product_error sample later
  have second := request.coordinate.close (Nat.le_refl request.coordinate.leftIndex) coordinateLater
  have close : Data.Gaussian.Norm.Basic.normSq (product - coordinateReading) < 4 * request.budget := by
    rw [show product - coordinateReading = (product - middle) + (middle - coordinateReading) by ring1]
    apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first second)).trans_eq
    ring1
  exact close

/-- The same endpoint request controls the unweighted coordinate even when the differential vanishes. No additional
model or root reading is needed. -/
theorem coordinate_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request data
  target floor) {index coordinateIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : ArcSamples.Sample comparison capSample)
    (later : request.index ≤ index) (coordinateLater : request.coordinate.rightIndex ≤ coordinateIndex) :
    Data.Gaussian.Norm.Basic.normSq (data.radicand * sample.retained.inverse.value.eval (parent.edge.point
      parameter)⁻¹ *
      capSample.inverse.value.eval (parent.edge.point parameter)⁻¹ -
      (Sampling.approximation owned.coordinates.coordinate.prepared.denominator.name).sample coordinateIndex) < target
        := by
  have denominatorPositive : 0 < 4 * (data.coefficientUpper + 1) := Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct data.coefficientUpper_nonnegative (by decide))
  have budgetNonnegative : 0 ≤ request.budget := by
    rw [request.budget_eq]
    exact Fraction.Order.Field.div_nonneg_direct request.positive.le denominatorPositive.le
  have denominatorBound : 4 ≤ 4 * (data.coefficientUpper + 1) := by
    have extra : 0 ≤ 4 * data.coefficientUpper :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.coefficientUpper_nonnegative
    have additive : (4 : InverseRootPolynomial.Coordinate) ≤ 4 + 4 * data.coefficientUpper := by
      simpa only [_root_.add_zero] using Fraction.Order.Arithmetic.add_le_add_direct (le_refl (4 :
        InverseRootPolynomial.Coordinate)) extra
    exact additive.trans_eq (by ring1)
  have paid : 4 * request.budget ≤ target := by
    calc
      _ ≤ (4 * (data.coefficientUpper + 1)) * request.budget :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct denominatorBound budgetNonnegative
      _ = target := by
        rw [request.budget_eq, Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  exact (request.coordinate_close sample later coordinateLater).trans_le paid

/-- All later shared polynomial stages and independent coordinate readings approximate the actual cached comparison
endpoint within the request. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request data target floor)
  {index coordinateIndex : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : ArcSamples.Sample comparison capSample)
    (endpoint : Coordinates.Overlap.Endpoint owned.coordinates capSample)
    (later : request.index ≤ index) (coordinateLater : request.coordinate.rightIndex ≤ coordinateIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.pullback.value.eval (parent.edge.point parameter)⁻¹ -
      endpoint.approximation.sample coordinateIndex) < target := by
  let point := (parent.edge.point parameter)⁻¹
  let product := data.radicand * sample.retained.inverse.value.eval point * capSample.inverse.value.eval point
  let coordinateReading := (Sampling.approximation owned.coordinates.coordinate.prepared.denominator.name).sample
    coordinateIndex
  have close : Data.Gaussian.Norm.Basic.normSq (product - coordinateReading) < 4 * request.budget :=
    request.coordinate_close sample later coordinateLater
  have value_eq : sample.pullback.value.eval point = product * endpoint.coefficient := by
    rw [sample.pullback.value_eq, sample.inverse_eq, endpoint.coefficient_eq, endpoint.factor_eq]
    dsimp only [product]
    rw [data.radicand_eq]
    ring1
  rw [value_eq, endpoint.sample_eq,
    show product * endpoint.coefficient - coordinateReading * endpoint.coefficient = (product - coordinateReading) *
      endpoint.coefficient by ring1,
    Data.Gaussian.Norm.Basic.normSq_mul]
  have weightBound : data.coefficientUpper ≤ data.coefficientUpper + 1 := by
    simpa only [_root_.add_zero] using Fraction.Order.Arithmetic.add_le_add_direct
      (le_refl data.coefficientUpper) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
  have weightPositive : 0 < data.coefficientUpper + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    data.coefficientUpper_nonnegative (by decide)
  calc
    _ ≤ Data.Gaussian.Norm.Basic.normSq (product - coordinateReading) * (data.coefficientUpper + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        ((data.coefficient_le endpoint).trans weightBound) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ < (4 * request.budget) * (data.coefficientUpper + 1) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct close weightPositive
    _ = target := by
      rw [show (4 * request.budget) * (data.coefficientUpper + 1) = request.budget * (4 * (data.coefficientUpper + 1))
        by ring1,
        request.budget_eq]
      exact Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) weightPositive).ne'

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
