module
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointRestoration
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan

open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointBudget

open
  PreparedEndpointRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample

open
  PreparedIntegralReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling

open Purelib.Data.Rat

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Uniform source-restoration budgets from pre-acquisition parent data. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Coordinate}
  {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {anchorBank : PrimitiveCells data index
    cover.mesh.edges}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {basis : BasisBounds bounds}
  {joinTarget : Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation (BasisFanGeometry)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
  covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)
open Purelib.Riemann.RootContinuation

/-- Every finite dyadic subdivision has a positive number of edges. -/
private theorem dyadic_nonempty (depth : Nat)
    (first last : ClearSheetContinuation.Subdivision.Endpoint) :
    0 < (ClearSheetContinuation.Subdivision.dyadicEdges depth first last).length := by
  induction depth generalizing first last with
  | zero => exact Nat.zero_lt_succ _
  | succ depth ih =>
    rw [ClearSheetContinuation.Subdivision.dyadicEdges, List.Append.length_append]
    exact Nat.lt_of_lt_of_le (ih _ _) (Nat.le_add_right _ _)

/-- The retained common cover has at least one actual interval. -/
private theorem common_nonempty {coverFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor) : common.intervals ≠ [] := by
  intro empty
  have edges := common.edges_eq
  rw [empty, List.map_nil] at edges
  have positive := dyadic_nonempty
    common.depth
    UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint
  rw [← edges] at positive
  exact Nat.not_lt_zero _ positive

open Purelib.Integration.Path.IncrementAreaReplacement (bracket)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest (firstView
  lastView)
open
  Basis.CommonParentBoundary.BasisCommonParentRequest.Plan.Acquisition
  (firstReading lastReading first_inside last_inside)

namespace BasisCommonParentRequest

variable {coverFloor : Nat} {common :
  BasisCommonCover cover covers coverFloor}
  {allowance coefficientTarget : Coordinate}

namespace Plan.Acquisition

variable {request :
  BasisCommonParentRequest common basis
  allowance coefficientTarget floor}
  {plan : Plan
    request capSample polynomials minimum}
  {acquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    plan anchorBank bank stage}
  {energyFloor radialDepth : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy (Energies)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples (EnergySamples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank (Connectors)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces (Traces)
open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
open
  Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan.Acquisition.Sample
  (PreparedComparison)

namespace Sample

variable {preparation :
  EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

namespace PreparedComparison

open
  Basis.PreparedEndpointRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (endpointError endpointError_paid restoredSourceAreaError restoredSourceTotalError restored_source_area_error
  restored_source_total_error)

open PreparedEndpointRestoration.BasisCommonParentRequest

variable {sample :
  CommonParentSample.BasisCommonParentRequest.Plan.Acquisition.Sample
  acquired preparation originals coefficients radialDepth}

/-- The retained prepared-source target is at most the square of the original allowance. -/
private theorem source_target_paid : request.prepared.sourceTarget ≤ allowance ^ 2 := by
  have nonnegative := request.prepared.request.source_positive.le
  have extra := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct
    (common.intervals.length : InverseRootPolynomial.Coordinate))
    request.prepared.request.comparison.positive.le
  have left := le_add_of_nonneg_right extra (a := request.prepared.sourceTarget)
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : InverseRootPolynomial.Coordinate) ≤ 2) (add_nonneg nonnegative extra)
  rw [Fraction.Field.one_mul] at doubled
  exact (left.trans doubled).trans (BasisPreparedAreaRequest.endpoint_paid request.prepared)

/-- The retained weighted source-area error is paid by the square of the original allowance. -/
private theorem source_area_paid :
    32 * request.prepared.sourceTarget * (BasisSourceCovers.primitiveSlope covers + request.prepared.sourceTarget) ≤
      allowance ^ 2 := by
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32)
      request.prepared.request.source_positive.le)
    (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers) request.prepared.request.source_positive.le)
  have left := le_add_of_nonneg_right (Fraction.Order.Arithmetic.sq_nonneg_direct request.prepared.half)
    (a := 32 * request.prepared.sourceTarget * (BasisSourceCovers.primitiveSlope covers +
      request.prepared.sourceTarget))
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (1 : InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg nonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct request.prepared.half))
  rw [Fraction.Field.one_mul] at doubled
  exact (left.trans doubled).trans request.prepared.paid

/-- The endpoint detour ceiling is paid uniformly by the original parent allowance, before any source polynomials or
children are acquired. -/
theorem endpointError_uniform : PreparedComparison.endpointError (request := request) ≤ 64 * allowance ^ 2 := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 436) request.restoration.positive.le
  rw [Fraction.Field.one_mul] at scaled
  have paid : request.restoration.target ≤ (4 * allowance) ^ 2 :=
    (scaled.trans_eq (show 436 * request.restoration.target =
      416 * request.restoration.target + 20 * request.restoration.target by ring1)).trans request.restoration.paid
  exact ((PreparedComparison.endpointError_paid (request := request)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4))).trans_eq (by ring1)

/-- Uniform per-parent constants keep the original allowance and a common source slope, with no refinement-count
dependence. -/
@[expose] def uniformSourceAreaError (allowance slope : InverseRootPolynomial.Coordinate) : Coordinate :=
  2 * (240 * (64 * allowance ^ 2) * (2 * (slope + 1)) + 352 * (64 * allowance ^ 2) ^ 2 + allowance ^ 2)

/-- The coefficient-independent uniform displacement allowance for restoring the original source polygon. -/
@[expose] def uniformSourceTotalError (allowance : InverseRootPolynomial.Coordinate) : Coordinate := 2050 * allowance ^
  2

/-- The remaining scalar weight is fixed by the retained source covers. -/
@[expose] def uniformSourceAreaWeight (slope : InverseRootPolynomial.Coordinate) : Coordinate :=
  2 * (240 * 64 * (2 * (slope + 1)) + 352 * 64 ^ 2 + 1)

/-- An allowance of squared size at most one reduces the uniform area error to its retained slope weight times that
squared allowance. -/
theorem uniformSourceAreaError_le {allowance : InverseRootPolynomial.Coordinate} (slope :
  InverseRootPolynomial.Coordinate) (small : allowance ^ 2 ≤ 1) :

      uniformSourceAreaError
      allowance slope ≤
      uniformSourceAreaWeight
      slope * allowance ^ 2 := by
  have squared := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
    (Fraction.Order.Arithmetic.sq_nonneg_direct allowance)
  have quartic : (allowance ^ 2) ^ 2 ≤ allowance ^ 2 :=
    (show (allowance ^ 2) ^ 2 = allowance ^ 2 * allowance ^ 2 by ring1).trans_le
      (squared.trans_eq (Fraction.Field.mul_one_direct _))
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct quartic
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 352)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (64 : InverseRootPolynomial.Coordinate)))
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (le_refl (240 * 64 * (2 * (slope + 1)) * allowance ^ 2)) weighted) (le_refl (allowance ^ 2)))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  exact (show
    uniformSourceAreaError
    allowance slope =
    2 * (240 * 64 * (2 * (slope + 1)) * allowance ^ 2 + (352 * 64 ^ 2) * (allowance ^ 2) ^ 2 + allowance ^ 2) by
      unfold
        uniformSourceAreaError;
        ring1).trans_le (combined.trans_eq (by
          unfold uniformSourceAreaWeight
          ring1))

/-- A shared upper bound on the original source slope bounds the retained restoration area allowance uniformly. -/
theorem restoredSourceAreaError_uniform {slope : InverseRootPolynomial.Coordinate}
    (slopeLe : BasisSourceCovers.primitiveSlope covers ≤ slope) :

      Plan.Acquisition.Sample.PreparedComparison.restoredSourceAreaError
      (request := request) ≤
      uniformSourceAreaError
      allowance slope := by
  have sourceSmall : request.prepared.sourceTarget ≤ 1 := by
    rw [request.prepared.sourceTarget_eq]
    exact Fraction.Order.Basic.min_le_left _ _
  have boundLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct slopeLe sourceSmall) (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  have endpointNonnegative : 0 ≤ PreparedComparison.endpointError (request := request) :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤
          4) (Fraction.Order.Arithmetic.sq_nonneg_direct _)) request.restoration.positive.le))
  have boundNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers) request.prepared.request.source_positive.le)
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct
    (endpointError_uniform
    (request := request)) boundLe boundNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
      (Fraction.Order.Arithmetic.sq_nonneg_direct allowance))
  have linear := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 240)
  have squared := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct endpointNonnegative
    (endpointError_uniform
    (request := request)) 2)
    (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 352)
  have total := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct linear squared)
      (source_area_paid
      (request := request))) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  exact (show PreparedComparison.restoredSourceAreaError (request := request) =
    2 * (240 * (PreparedComparison.endpointError (request := request) * (2 * (BasisSourceCovers.primitiveSlope covers +
      request.prepared.sourceTarget))) +
      352 * (PreparedComparison.endpointError (request := request)) ^ 2 + 32 * request.prepared.sourceTarget *
        (BasisSourceCovers.primitiveSlope covers + request.prepared.sourceTarget)) by
      unfold PreparedComparison.restoredSourceAreaError; ring1).trans_le (total.trans_eq (by
        unfold uniformSourceAreaError
        ring1))

/-- The retained restoration displacement allowance is bounded by its uniform original-parent allowance. -/
theorem restoredSourceTotalError_uniform :
    PreparedComparison.restoredSourceTotalError (request := request) ≤
      uniformSourceTotalError
      allowance :=
  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (endpointError_uniform
      (request := request)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16))

      (source_target_paid
      (request := request))) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by
        unfold uniformSourceTotalError
        ring1)

/-- Every parent can use the same source slope ceiling in the concatenation estimate, while retaining its own literal
restored and source polygons. -/
theorem restored_source_area_uniform (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    {slope : InverseRootPolynomial.Coordinate} (slopeLe : BasisSourceCovers.primitiveSlope covers ≤ slope) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).area -
      comparison.weighted.source.area) ≤

        uniformSourceAreaError
        allowance slope * (PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2 :=
  (PreparedComparison.restored_source_area_error comparison previous gap).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (restoredSourceAreaError_uniform
      slopeLe) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The actual restored displacement approximates its retained source displacement with a uniform homogeneous bound.

The original incoming root gap must be paid; the estimate retains the exact restored and cached source totals. -/
theorem restored_source_total_uniform (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).total -
      comparison.weighted.source.total) ≤

        uniformSourceTotalError
        allowance * PreparedObservationCoercivity.coefficientNormSq coefficients :=
  (PreparedComparison.restored_source_total_error comparison previous gap).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (restoredSourceTotalError_uniform
      (request := request))
      (FiniteSum.Fin.sumFin_zero.symm.trans_le
        (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
          Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))))

/-- The cached source total is bounded by its original cover slope. -/
theorem source_total_bound (comparison : Acquisition.Sample.PreparedComparison sample) :
    Data.Gaussian.Norm.Basic.normSq comparison.weighted.source.total ≤ BasisSourceCovers.primitiveSlope covers
      * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bounded := ReciprocalDiskArcOwners.increment_bound originals coefficients (first := 0) (last := 1) ⟨le_rfl, by
    decide⟩ ⟨by decide, le_rfl⟩
  rw [show ((1 : InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 by decide, Fraction.Field.mul_one_direct, ←
    Weighted.source_total comparison.weighted] at bounded
  exact bounded

end PreparedComparison
end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget
