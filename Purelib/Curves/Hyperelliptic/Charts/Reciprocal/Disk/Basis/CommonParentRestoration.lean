module
import Purelib.Data.List.Append
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonIncoming
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
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
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Integration.Path.HomogeneousTraceRestoration
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues.Paths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonIncoming.Paths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample.BasisCommonParentRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration.Paths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

public section

/-! Restore a common-parent sample against the preceding retained parent.
All endpoint estimates and radial readbacks come from those two samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration

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

namespace Sample

variable {preparation :
  EnergyPreparation
  request.charts.requests plan.charts acquired.readings allowance energyFloor}

/-- The literal connected chart path with its retained source endpoint detours. -/
@[expose] def restoredPath (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
  (previous : InverseRootPolynomial.Gaussian) : List Gaussian :=
  HomogeneousTraceRestoration.sourceRestoredPath
    (((Paths.joinedBlocks 0 sample.paths sample.connectors).map (fun block => block.1 :: block.2)).flatten)
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings)
    (Readings.lastChartValue coefficients request.charts.requests acquired.readings)
    sample.endpoints.first.1 sample.endpoints.last.1 sample.endpoints.last.2 previous

/-- The retained outgoing potential, including its source/chart origin correction. -/
@[expose] def outgoingPotential (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth) :
  Gaussian :=
  IncrementRestoration.potential (EnergySamples.lastPotential request.charts.requests sample.samples)
    (Readings.lastChartValue coefficients request.charts.requests acquired.readings) sample.endpoints.last.2

/-- Initial source potential, retained separately from the outgoing one. -/
@[expose] def incomingPotential (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth) :
  Gaussian :=
  IncrementRestoration.potential (EnergySamples.firstPotential request.charts.requests sample.samples)
    (Readings.firstChartValue coefficients request.charts.requests acquired.readings) sample.endpoints.first.2

/-- Start the family at its own retained direct endpoint. The initial gap and incoming ribbon vanish by scalar
equalities, without a root-closure premise. -/
@[expose] def restoreFirst (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients
      (restoredPath
      sample sample.endpoints.first.2)
      sample.endpoints.first.2 sample.endpoints.last.2
        (incomingPotential
        sample)
        (outgoingPotential
        sample)
      (allowance + allowance + allowance + allowance) := by
  have sourcePaid : request.charts.localAllowance^2 ≤ request.restoration.sourceAllowance^2 := by
    apply (request.restoration.incoming_paid request.charts.local_positive.le request.source_le).trans
    rw [request.restoration.target_eq]
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 16)).mpr
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide : (4 : InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1)
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have gap : Data.Gaussian.Norm.Basic.normSq (sample.endpoints.first.2 - sample.endpoints.first.2) ≤
      request.restoration.target * PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct request.restoration.positive.le normNonnegative
  have incoming : Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential (EnergySamples.firstPotential
    request.charts.requests sample.samples)
      (Readings.firstChartValue coefficients request.charts.requests acquired.readings) sample.endpoints.first.2 -

        incomingPotential
        sample - BoundaryRibbon.area sample.endpoints.first.2 sample.endpoints.first.2) ≤
      (80 * request.restoration.target + 2 * request.restoration.target) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
    rw
      [incomingPotential,
      Data.Gaussian.Basic.sub_self, IncrementArea.area_self, Data.Gaussian.Basic.sub_self,
      Data.Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 80)
        request.restoration.positive.le)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        request.restoration.positive.le)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  exact Extremes.restore sample.endpoints sample.connection request.restoration request.positive.le sourcePaid
    sample.endpoints.first.2
      (incomingPotential
      sample) gap incoming

variable {previousCount previousCoverFloor previousFloor previousMinimum previousStage previousEnergyFloor : Nat}
  {previousParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {previousPatch : PreparedPatch previousParent}
  {previousData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data previousPatch
    previousCount}
  {previousCover : Cover previousData}
  {previousCovers : BasisSourceCovers
    previousParent}
  {previousCommon : BasisCommonCover previousCover
    previousCovers previousCoverFloor}
  {previousCoefficientTarget : Coordinate}
  {previousRequest :
    BasisCommonParentRequest
    previousCommon basis allowance previousCoefficientTarget previousFloor}
  {previousPlan :
    Plan
    previousRequest capSample polynomials previousMinimum}
  {previousAnchorBank : PrimitiveCells
    previousData index previousCover.mesh.edges}
  {previousBank :
    BasisSourceLocations.SampleBank
    previousCovers index}
  {previousAcquired :
    CommonParentReadings.BasisCommonParentRequest.Plan.Acquisition
    previousPlan previousAnchorBank previousBank previousStage}
  {previousPreparation :
    EnergyPreparation
    previousRequest.charts.requests previousPlan.charts previousAcquired.readings allowance previousEnergyFloor}
  {previousOriginals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    previousCovers index}

/-- Restore a common-parent trace after its actual preceding retained sample.

The original physical root join and paid reading stages supply the incoming estimates; both endpoint and radial
readbacks come from the two retained samples. -/
@[expose] def restoreAfter
    (previous : Acquisition.Sample previousAcquired previousPreparation previousOriginals coefficients radialDepth)
    (sample : Acquisition.Sample acquired preparation originals coefficients radialDepth)
    {joined : ArcOwners.Join (BasisCommonParentRequest.lastView previousRequest).point
      (BasisCommonParentRequest.firstView request).point}
    (joining : RestorationJoins.BasisRestorationRequest basis joined request.restoration.target joinFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (previousLater : joining.index ≤ previousStage) (later : joining.index ≤ stage) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients
      (restoredPath
      sample previous.endpoints.last.2)
      previous.endpoints.last.2 sample.endpoints.last.2
        (outgoingPotential
        previous)
        (outgoingPotential
        sample)
      (allowance + allowance + allowance + allowance) := by
  have targetEq : previousRequest.restoration.target = request.restoration.target := by
    rw [previousRequest.restoration.target_eq, request.restoration.target_eq,
      previousRequest.restoration.source_eq, request.restoration.source_eq]
  have previousPaid := previousRequest.restoration.incoming_paid
    previousRequest.charts.local_positive.le previousRequest.source_le
  rw [targetEq] at previousPaid
  have previousChart := Plans.lastReading_chart (coefficients := coefficients)
    previousRequest.charts.requests previousAcquired.readings
    (BasisCommonChartRequests.common_from previousCommon)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty previousCommon)
  have previousRadial := Plans.lastReading_radial previousRequest.charts.requests previousAcquired.readings
    previous.energies previous.samples (BasisCommonChartRequests.common_from previousCommon)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty previousCommon)
  have previousEstimate := Extremes.last_bounded previous.endpoints
  rw [previousChart] at previousEstimate
  have previousReadback :
    outgoingPotential
    previous = IncrementRestoration.potential
      (RootRadialGeometry.radialArea (polynomials.value coefficients) radialDepth (Acquisition.lastReading
        previousAcquired).reading.coordinate)
      (polynomials.value coefficients (Acquisition.lastReading previousAcquired).reading.coordinate)
        previous.endpoints.last.2 := by
    rw
      [outgoingPotential,
      previousChart, previousRadial]
    rfl
  exact Extremes.restoreFromReadings sample.endpoints sample.connection request.restoration request.positive.le joining
    request.charts.local_positive.le request.source_le (Acquisition.lastReading previousAcquired).reading
      (Acquisition.firstReading acquired).reading
    branch (Acquisition.last_inside previousAcquired) (Acquisition.first_inside acquired) previousLater later
    (Plans.firstReading_chart request.charts.requests acquired.readings
      (BasisCommonChartRequests.common_from common)
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common))
    (Plans.firstReading_radial request.charts.requests acquired.readings sample.energies sample.samples
      (BasisCommonChartRequests.common_from common)
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common))
    previous.endpoints.last.1 previous.endpoints.last.2
      (outgoingPotential
      previous) previousReadback previousPaid previousEstimate

end Sample
end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRestoration
