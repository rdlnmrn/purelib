module
import Purelib.Data.List.Append
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Bound the actual returned endpoint potentials without discarding the closing ribbon. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation
  (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation
  (BasisFanGeometry)

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

/-- The retained common cover contains at least one actual interval. -/
private theorem common_nonempty {coverFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor) : common.intervals ≠ [] := by
  intro empty
  have edges := common.edges_eq
  rw [empty, List.map_nil] at edges
  have positive := dyadic_nonempty common.depth
    UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint
  rw [← edges] at positive
  exact Nat.not_lt_zero _ positive

open Purelib.Integration.Path.IncrementAreaReplacement (bracket)

open Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest (firstView
  lastView)
open
  Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.Plan.Acquisition
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

open Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Reciprocal.Disk.Basis.CommonChartEnergy (Energies)
open Reciprocal.Disk.Basis.CommonEnergySamples (EnergySamples)
open Reciprocal.Disk.Basis.CommonConnectorBank (Connectors)
open Reciprocal.Disk.Basis.CommonChartTraces (Traces)
open
  Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan.Acquisition
  (Sample)
open
  Reciprocal.Disk.Basis.CommonPreparedComparison.BasisCommonParentRequest.Plan.Acquisition.Sample
  (PreparedComparison)

namespace Sample

variable {preparation :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

/-- Uniform coefficient-independent cost of returning the retained endpoint potential, including the nonzero endpoint
ribbon. -/
@[expose] def returnScale : Coordinate := (180 + 64 * basis.coefficient) * (4 * allowance)^2

variable {previousCount previousCoverFloor previousFloor previousMinimum previousStage previousEnergyFloor : Nat}
  {previousParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {previousPatch : PreparedPatch previousParent}
  {previousData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data previousPatch
    previousCount}
  {previousCover : Cover previousData}
  {previousCovers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers
    previousParent}
  {previousCommon : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover previousCover
    previousCovers previousCoverFloor}
  {previousCoefficientTarget : Coordinate}
  {previousRequest :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
    previousCommon basis allowance previousCoefficientTarget previousFloor}
  {previousPlan :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest.Plan
    previousRequest capSample polynomials previousMinimum}
  {previousAnchorBank : PrimitiveCells
    previousData index previousCover.mesh.edges}
  {previousBank :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    previousCovers index}
  {previousAcquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    previousPlan previousAnchorBank previousBank previousStage}
  {previousPreparation :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation.EnergyPreparation
    previousRequest.charts.requests previousPlan.charts previousAcquired.readings allowance previousEnergyFloor}
  {previousOriginals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    previousCovers index}

/-- The two readings belong to the actual closing root join. The shifted potential estimate and direct endpoint gap
retain, then pay, its ribbon. -/
theorem returned_potential_bound
    (previous : Acquisition.Sample previousAcquired previousPreparation previousOriginals coefficients radialDepth)
    (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    {joined : ArcOwners.Join (BasisCommonParentRequest.lastView previousRequest).point
      (BasisCommonParentRequest.firstView request).point}
    (joining : RestorationJoins.BasisRestorationRequest basis joined request.restoration.target joinFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (previousLater : joining.index ≤ previousStage) (later : joining.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Acquisition.Sample.outgoingPotential previous -
      Acquisition.Sample.incomingPotential sample) ≤

        returnScale
        (basis := basis) (allowance := allowance) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
        by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have targetEq : previousRequest.restoration.target = request.restoration.target := by
    rw [previousRequest.restoration.target_eq, request.restoration.target_eq,
      previousRequest.restoration.source_eq, request.restoration.source_eq]
  have previousPaid := previousRequest.restoration.incoming_paid
    previousRequest.charts.local_positive.le previousRequest.source_le
  rw [targetEq] at previousPaid
  have currentPaid := request.restoration.incoming_paid request.charts.local_positive.le request.source_le
  have previousClose := previous.endpoints.last_bounded.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (previousPaid.trans_eq joining.endpoint_eq.symm)
      normNonnegative)
  have currentClose := sample.endpoints.first_bounded.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (currentPaid.trans_eq joining.endpoint_eq.symm)
      normNonnegative)
  rw [Plans.lastReading_chart previousRequest.charts.requests previousAcquired.readings
    (BasisCommonChartRequests.common_from previousCommon)
      (common_nonempty previousCommon)] at previousClose
  rw [Plans.firstReading_chart request.charts.requests acquired.readings
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.common_nonempty common)] at currentClose
  have chartGap := joining.chart_gap polynomials coefficients (Acquisition.lastReading previousAcquired).reading
    (Acquisition.firstReading acquired).reading
    branch (Acquisition.last_inside previousAcquired) (Acquisition.first_inside acquired) previousLater later
  have gap := joining.direct_gap coefficients previousClose currentClose chartGap
  have potentialBound := joining.potential_accurate polynomials coefficients
    (Acquisition.lastReading previousAcquired).reading (Acquisition.firstReading acquired).reading branch
      (Acquisition.last_inside previousAcquired) (Acquisition.first_inside acquired)
    previousLater later radialDepth previous.endpoints.last.2 sample.endpoints.first.2 previousClose currentClose
      request.restoration.small
  have previousChart := Plans.lastReading_chart (coefficients := coefficients)
    previousRequest.charts.requests previousAcquired.readings (BasisCommonChartRequests.common_from previousCommon)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.common_nonempty previousCommon)
  have previousRadial := Plans.lastReading_radial previousRequest.charts.requests previousAcquired.readings
    previous.energies previous.samples
    (BasisCommonChartRequests.common_from previousCommon)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.common_nonempty previousCommon)
  have currentChart := Plans.firstReading_chart (coefficients := coefficients)
    request.charts.requests acquired.readings (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.common_nonempty common)
  have currentRadial := Plans.firstReading_radial request.charts.requests acquired.readings sample.energies
    sample.samples
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn.common_nonempty common)
  have defect : Data.Gaussian.Norm.Basic.normSq (Acquisition.Sample.incomingPotential sample -
    Acquisition.Sample.outgoingPotential previous -
      BoundaryRibbon.area previous.endpoints.last.2 sample.endpoints.first.2) ≤
      (80 * request.restoration.target + 2 * request.restoration.target) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
    rw [Acquisition.Sample.incomingPotential, Acquisition.Sample.outgoingPotential, currentChart, previousChart,
      currentRadial, previousRadial]
    exact potentialBound
  have firstBound := PreparedComparison.first_direct_bound sample branch
  have gapReversed : Data.Gaussian.Norm.Basic.normSq (previous.endpoints.last.2 - sample.endpoints.first.2) ≤
      request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show previous.endpoints.last.2 - sample.endpoints.first.2 =
      -(sample.endpoints.first.2 - previous.endpoints.last.2) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact gap
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct gapReversed firstBound
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans gapReversed)
  have ribbon : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area previous.endpoints.last.2
    sample.endpoints.first.2) ≤
      4 * request.restoration.target * (2 + 8 * basis.coefficient) * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
    have identity : BoundaryRibbon.area previous.endpoints.last.2 sample.endpoints.first.2 =
        BoundaryRibbon.area (previous.endpoints.last.2 - sample.endpoints.first.2) sample.endpoints.first.2 := by
      apply Data.Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, BoundaryRibbon.area,
        Data.Gaussian.Basic.conj, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity]
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq (previous.endpoints.last.2 - sample.endpoints.first.2) *
        Data.Gaussian.Norm.Basic.normSq sample.endpoints.first.2 :=
        BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq (previous.endpoints.last.2 - sample.endpoints.first.2) *
        Data.Gaussian.Norm.Basic.normSq sample.endpoints.first.2) := by
        ring1
      _ ≤ 4 * (request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients *
          ((2 + 8 * basis.coefficient) * PreparedObservationCoercivity.coefficientNormSq coefficients)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
      _ = _ := by ring1
  have combined := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (Acquisition.Sample.incomingPotential sample - Acquisition.Sample.outgoingPotential previous - BoundaryRibbon.area
      previous.endpoints.last.2 sample.endpoints.first.2)
    (BoundaryRibbon.area previous.endpoints.last.2 sample.endpoints.first.2)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct defect
      ribbon) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [show Acquisition.Sample.incomingPotential sample - Acquisition.Sample.outgoingPotential previous -
    BoundaryRibbon.area previous.endpoints.last.2 sample.endpoints.first.2 +
    BoundaryRibbon.area previous.endpoints.last.2 sample.endpoints.first.2 = -(Acquisition.Sample.outgoingPotential
      previous - Acquisition.Sample.incomingPotential sample) by ring1,
    Data.Gaussian.Norm.Basic.normSq_neg] at combined
  have targetPaid : request.restoration.target ≤ (4 * allowance)^2 :=
    (show request.restoration.target = 1 * request.restoration.target by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide +kernel : (1 : InverseRootPolynomial.Coordinate) ≤ 436) request.restoration.positive.le).trans
        ((show 436 * request.restoration.target = 416 * request.restoration.target + 20 * request.restoration.target by
          ring1).trans_le
          request.restoration.paid))
  have factorNonnegative : 0 ≤ 180 + 64 * basis.coefficient :=
    add_nonneg (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 180)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
        basis.coefficient_nonnegative)
  exact (combined.trans_eq (show _ = (180 + 64 * basis.coefficient) * request.restoration.target *
    (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by ring1)).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct targetPaid factorNonnegative)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by
        unfold CommonParentReturn.BasisCommonParentRequest.Plan.Acquisition.Sample.returnScale
        ring1))

end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReturn
