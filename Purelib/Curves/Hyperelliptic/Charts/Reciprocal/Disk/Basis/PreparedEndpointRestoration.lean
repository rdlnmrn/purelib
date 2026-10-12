module
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedIntegralReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Integration.Path.IncrementAreaDoubleRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

open
  PreparedIntegralReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Compare the actual restored integral path with its unbracketed interior. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointRestoration

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Basis.CommonParentRequest (BasisCommonParentRequest)
open Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Cover data} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Coordinate}
  {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {anchorBank : PrimitiveCells data index
    cover.mesh.edges}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
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

open Basis.CommonParentBoundary.BasisCommonParentRequest (firstView
  lastView)
open
  Basis.CommonParentBoundary.BasisCommonParentRequest.Plan.Acquisition
  (firstReading lastReading first_inside last_inside)

namespace BasisCommonParentRequest

variable {coverFloor : Nat} {common :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers coverFloor}
  {allowance coefficientTarget : Coordinate}

namespace Plan.Acquisition

variable {request :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest common basis
  allowance coefficientTarget floor}
  {plan : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan
    request capSample polynomials minimum}
  {acquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    plan anchorBank bank stage}
  {energyFloor radialDepth : Nat}

open Basis.CommonChartSchedule (BasisCommonChartRequests)
open Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Basis.CommonEnergyPreparation (EnergyPreparation)
open Basis.CommonChartEnergy (Energies)
open Basis.CommonEnergySamples (EnergySamples)
open Basis.CommonConnectorBank (Connectors)
open Basis.CommonChartTraces (Traces)
open
  Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
open
  Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan.Acquisition.Sample
  (PreparedComparison)

namespace Sample

variable {preparation :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

namespace PreparedComparison

variable {sample :
  CommonParentSample.BasisCommonParentRequest.Plan.Acquisition.Sample
  acquired preparation originals coefficients radialDepth}

/-- A coefficient-independent ceiling for each of the four retained endpoint corrections, once the scheduled incoming
root gap has been paid. -/
@[expose] def endpointError : Coordinate :=
  10 * request.charts.localAllowance^2 + 2 * (4 * request.charts.localAllowance^2 + request.restoration.target)

/-- The retained endpoint-error ceiling is at most four times the original restoration target. -/
theorem endpointError_paid :
  endpointError
  (request := request) ≤ 4 * request.restoration.target := by
  have small := request.restoration.incoming_paid request.charts.local_positive.le request.source_le
  have first := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 18))
    (le_refl (2 * request.restoration.target))
  have enlarged := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (18 : InverseRootPolynomial.Coordinate) ≤ 32)
      (Fraction.Order.Field.div_nonneg_direct request.restoration.positive.le (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)))
    (le_refl (2 * request.restoration.target))
  exact (show
    endpointError
    (request := request) = 18 * request.charts.localAllowance^2 + 2 * request.restoration.target by
    unfold
      endpointError;
      ring1).trans_le (first.trans (enlarged.trans_eq (calc
      32 * (request.restoration.target / 16) + 2 * request.restoration.target =
        2 * ((request.restoration.target / 16) * 16) + 2 * request.restoration.target := by ring1
      _ = 4 * request.restoration.target := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by
          decide : (16 : InverseRootPolynomial.Coordinate) ≠ 0)]; ring1)))

/-- All four actual endpoint corrections satisfy the common homogeneous allowance once the incoming root gap is paid. -/
private theorem endpoint_bounds (previous : InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq (Readings.firstChartValue coefficients request.charts.requests
      acquired.readings - sample.endpoints.first.1) ≤

        endpointError
        (request := request) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq (sample.endpoints.last.1 - Readings.lastChartValue coefficients
      request.charts.requests acquired.readings) ≤

        endpointError
        (request := request) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.1 - previous) ≤
      endpointError
      (request := request) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq (sample.endpoints.last.2 - sample.endpoints.last.1) ≤
      endpointError
      (request := request) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have chartLe : 10 * request.charts.localAllowance^2 ≤
    endpointError
    (request := request) :=
    le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)) request.restoration.positive.le))
  have sourceLe : 4 * request.charts.localAllowance^2 ≤
    endpointError
    (request := request) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (4 : InverseRootPolynomial.Coordinate) ≤
      10) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans chartLe
  have incomingLe : 2 * (4 * request.charts.localAllowance^2 + request.restoration.target) ≤
    endpointError
    (request := request) :=
    le_add_of_nonneg_left (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have first := sample.endpoints.first_bounded.chart_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartLe normNonnegative)
  have last := sample.endpoints.last_bounded.chart_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct chartLe normNonnegative)
  have outgoing := sample.endpoints.last_bounded.source_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct sourceLe normNonnegative)
  have incoming := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via sample.endpoints.first.1 sample.endpoints.first.2
    previous).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      sample.endpoints.first_bounded.source_close gap)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have incomingPaid := incoming.trans ((show 2 * (4 * request.charts.localAllowance^2 *
    PreparedObservationCoercivity.coefficientNormSq coefficients +
      request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients) =
      (2 * (4 * request.charts.localAllowance^2 + request.restoration.target)) *
        PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct incomingLe normNonnegative))
  rw [show Readings.firstChartValue coefficients request.charts.requests acquired.readings - sample.endpoints.first.1 =
    -(sample.endpoints.first.1 - Readings.firstChartValue coefficients request.charts.requests acquired.readings) by
      ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  rw [show sample.endpoints.last.2 - sample.endpoints.last.1 = -(sample.endpoints.last.1 - sample.endpoints.last.2) by
    ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  exact ⟨first, last, incomingPaid, outgoing⟩

/-- Endpoint restoration changes the total by exactly the retained endpoint corrections; the fine child count does not
enter this bound. -/
theorem restored_endpoint_total_error (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).total -
      comparison.weighted.integral.total) ≤
      (16 *
        endpointError
        (request := request)) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bounds :=
    endpoint_bounds
    previous gap
  exact (IncrementAreaDoubleRestoration.doubleBracket_total_error comparison.weighted.integral _ _ _ _ bounds.1
    bounds.2.1 bounds.2.2.1 bounds.2.2.2).trans_eq (by ring1)

/-- All endpoint polygon terms are retained, including the interaction with the integral total. No closed-path area is
assumed to vanish. -/
theorem restored_endpoint_area_error (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    {bound : InverseRootPolynomial.Coordinate} (bounded : Data.Gaussian.Norm.Basic.normSq
      comparison.weighted.integral.total ≤ bound * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).area -
      comparison.weighted.integral.area) ≤
      (240 *
        endpointError
        (request := request) * bound + 352 *
        (endpointError
        (request := request))^2) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bounds :=
    endpoint_bounds
    previous gap
  exact (IncrementAreaDoubleRestoration.doubleBracket_area_error comparison.weighted.integral _ _ _ _ bounds.1
    bounds.2.1 bounds.2.2.1 bounds.2.2.2 bounded).trans_eq (by ring1)

/-- Bound the actual prepared total using its retained source primitive and its certified endpoint error, before adding
the restoration increments. -/
theorem integral_total_bound (comparison : Acquisition.Sample.PreparedComparison sample) :
    Data.Gaussian.Norm.Basic.normSq comparison.weighted.integral.total ≤
      (2 * (BasisSourceCovers.primitiveSlope covers + request.prepared.sourceTarget)) *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have source := ReciprocalDiskArcOwners.increment_bound originals coefficients (first := 0) (last := 1) ⟨le_rfl, by
    decide⟩ ⟨by decide, le_rfl⟩
  rw [show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, Fraction.Field.mul_one_direct, ←
    Weighted.source_total comparison.weighted] at source
  have combined := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two comparison.weighted.source.total
    (comparison.weighted.source.total - comparison.weighted.integral.total)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
        (Weighted.total_error comparison.weighted)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [show comparison.weighted.source.total - (comparison.weighted.source.total - comparison.weighted.integral.total) =
    comparison.weighted.integral.total by ring1] at combined
  exact combined.trans_eq (by ring1)

/-- The coefficient-independent area allowance combining original source comparison with endpoint restoration. -/
@[expose] def restoredSourceAreaError : Coordinate :=
  2 * (240 *
    endpointError
    (request := request) * (2 * (BasisSourceCovers.primitiveSlope covers + request.prepared.sourceTarget)) +
    352 *
      (endpointError
      (request := request))^2 +
    32 * request.prepared.sourceTarget * (BasisSourceCovers.primitiveSlope covers + request.prepared.sourceTarget))

/-- The coefficient-independent displacement allowance combining original source comparison with endpoint restoration.
-/
@[expose] def restoredSourceTotalError : Coordinate := 2 * (16 *
  endpointError
  (request := request) + request.prepared.sourceTarget)

/-- Connect the complete restored integral polygon to the cached source polygon used by the original-schedule
comparison. -/
theorem restored_source_area_error (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).area -
      comparison.weighted.source.area) ≤

        restoredSourceAreaError
        (request := request) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have source := comparison.weighted.area_error
  rw [comparison.weighted.difference_eq] at source
  have reversed : Data.Gaussian.Norm.Basic.normSq (comparison.weighted.integral.area -
    comparison.weighted.source.area) =
      Data.Gaussian.Norm.Basic.normSq (comparison.weighted.source.area - comparison.weighted.integral.area) :=
        by
    rw [show comparison.weighted.integral.area - comparison.weighted.source.area =
      -(comparison.weighted.source.area - comparison.weighted.integral.area) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
  have combined := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (PreparedComparison.restoredIntegral comparison
    previous).area comparison.weighted.integral.area
    comparison.weighted.source.area).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct

          (restored_endpoint_area_error
          comparison previous gap
          (integral_total_bound
          comparison))
        (reversed.trans_le source)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  exact combined.trans_eq (by
    unfold restoredSourceAreaError
    ring1)

/-- The complete restored integral displacement approximates the original cached source displacement.

The bound uses the retained source and endpoint allowances and scales by the squared coefficient norm. -/
theorem restored_source_total_error (comparison : Acquisition.Sample.PreparedComparison sample) (previous :
  InverseRootPolynomial.Gaussian)
    (gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - previous) ≤ request.restoration.target *
      PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq ((PreparedComparison.restoredIntegral comparison previous).total -
      comparison.weighted.source.total) ≤

        restoredSourceTotalError
        (request := request) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have reversed : Data.Gaussian.Norm.Basic.normSq (comparison.weighted.integral.total -
    comparison.weighted.source.total) =
      Data.Gaussian.Norm.Basic.normSq (comparison.weighted.source.total - comparison.weighted.integral.total)
        := by
    rw [show comparison.weighted.integral.total - comparison.weighted.source.total =
      -(comparison.weighted.source.total - comparison.weighted.integral.total) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
  exact ((Data.Gaussian.Norm.Bounds.normSq_sub_le_via (PreparedComparison.restoredIntegral comparison previous).total
    comparison.weighted.integral.total
    comparison.weighted.source.total).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct

          (restored_endpoint_total_error
          comparison previous gap) (reversed.trans_le (Weighted.total_error comparison.weighted)))
        (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))).trans_eq (by
          unfold restoredSourceTotalError
          ring1)

end PreparedComparison
end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedEndpointRestoration
