module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Trace.Restoration
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Integration.Path.HomogeneousTraceRestoration
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonSourceRestoration.Paths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

open Purelib.Data.Rat

open Purelib.Integration.Budget.Trace

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

public section

/-! Incoming restoration estimates from the retained physical root join.
The tighter join endpoint tolerance is preserved explicitly. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonIncoming

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    BasisSourceCovers parent}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Coordinate}
  {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {anchorBank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index
    cover.mesh.edges}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Coordinate} {joinFloor : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest (BasisCommonCoordinateRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest (BasisCommonArcRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget (BasisCommonConnectorBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans
  (Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans (Paths)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy (Energies)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples (EnergySamples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank (Connectors)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces (Traces)
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
open Purelib.Integration.Path.HomogeneousTraceRestoration (sourceRestoredPath)
open Purelib.Integration.Path.HomogeneousTraceRestoration.HomogeneousTrace
open Purelib.Integration.Path.IncrementRestoration (potential)
open Purelib.Integration.Budget.Trace.Restoration (BasisCommonRestorationAllowance)

namespace Paths.Extremes

variable {intervals : List (BasisCommonInterval
  cover covers)}
  {requests : BasisCommonChartRequests
    regular depth target sourceTarget floor sourceFloor intervals}
  {plans : Plans
    capSample polynomials minimum requests} {readings :
    CommonChartReadings.BasisCommonChartRequests.Plans.Readings
    anchorBank bank stage requests plans}
  {paths :
    Paths
    originals coefficients requests plans readings}
  {connectors : Connectors coefficients
    energyDepth joinTarget requests plans readings}
  {firstPotential lastPotential : Gaussian} {loss allowance :
    Coordinate}

open Purelib.Integration.Path.HomogeneousTraceRestoration (sourceRestoredPath)
open Purelib.Integration.Path.IncrementRestoration (potential)

open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins (BasisRestorationRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues (EndpointEstimate)

variable {leftCount rightCount leftIndex rightIndex joinFloor : Nat}
  {leftParent rightParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {leftPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch leftParent}
  {rightPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch rightParent}
  {leftData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data leftPatch leftCount}
  {rightData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data rightPatch rightCount}
  {leftEdge rightEdge : ParameterEdge}
  {leftCell : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell leftData leftEdge}
  {rightCell : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell rightData rightEdge}
  {leftModel : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel leftCell}
  {rightModel : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel rightCell}
  {leftParameter rightParameter : Coordinate}
  {leftPoint : Point cap leftModel leftParameter}
    {rightPoint : Point cap rightModel rightParameter}
  {leftEndpoint : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint leftPoint.coordinates
    capSample}
  {rightEndpoint : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint
    rightPoint.coordinates capSample}
  {joined : Join leftPoint rightPoint}

/-- Restore the actual common-parent trace using its retained physical root join.

The acquired endpoint readings pay the incoming gap and shifted-potential error, preserving the tighter join tolerance
and all source/chart endpoint readbacks. -/
@[expose] def restoreFromReadings (ends : Paths.Extremes paths)
    (connection : HomogeneousTraceConnection.HomogeneousTrace coefficients
      (((Paths.joinedBlocks 0 paths connectors).map (fun block => block.1 :: block.2)).flatten)
      (Readings.firstChartValue coefficients requests readings) (Readings.lastChartValue coefficients requests readings)
      firstPotential lastPotential loss)
    (allocation : Restoration.BasisCommonRestorationAllowance allowance) (positive : 0 ≤ allowance)
    (request : RestorationJoins.BasisRestorationRequest basis joined allocation.target joinFloor)
    (sourceNonnegative : 0 ≤ sourceTarget) (sourceLe : sourceTarget ≤ allocation.incomingAllowance)
    (leftReading : ChartReadings.Endpoint.Reading leftEndpoint leftIndex)
    (rightReading : ChartReadings.Endpoint.Reading rightEndpoint rightIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex)
    (rightChart : Readings.firstChartValue coefficients requests readings = polynomials.value coefficients
      rightReading.coordinate)
    (rightPotential : firstPotential = RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
      rightReading.coordinate)
    (previousSource previous previousPotential : InverseRootPolynomial.Gaussian)
    (previousReadback : previousPotential = IncrementRestoration.potential
      (RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth leftReading.coordinate)
      (polynomials.value coefficients leftReading.coordinate) previous)
    {previousTarget : InverseRootPolynomial.Coordinate} (previousLe : previousTarget ≤ allocation.target / 16)
    (previousEstimate : ParentBasisEndpointValues.EndpointEstimate coefficients previousTarget
      (polynomials.value coefficients leftReading.coordinate) (previousSource, previous)) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients
      (HomogeneousTraceRestoration.sourceRestoredPath (((Paths.joinedBlocks 0 paths connectors).map (fun block =>
        block.1 :: block.2)).flatten)
        (Readings.firstChartValue coefficients requests readings) (Readings.lastChartValue coefficients requests
          readings)
        ends.first.1 ends.last.1 ends.last.2 previous)
      previous ends.last.2 previousPotential
      (IncrementRestoration.potential lastPotential (Readings.lastChartValue coefficients requests readings)
        ends.last.2) (loss + allowance) := by
  have sourcePaidForJoin := allocation.incoming_paid sourceNonnegative sourceLe
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have firstClose := previousEstimate.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (previousLe.trans_eq request.endpoint_eq.symm)
      normNonnegative)
  have lastClose := ends.first_bounded.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (sourcePaidForJoin.trans_eq request.endpoint_eq.symm)
      normNonnegative)
  rw [rightChart] at lastClose
  have gap := request.direct_gap coefficients firstClose lastClose
    (request.chart_gap polynomials coefficients leftReading rightReading branch leftInside rightInside leftLater
      rightLater)
  have potentialBound := request.potential_accurate polynomials coefficients leftReading rightReading branch
    leftInside rightInside leftLater rightLater energyDepth previous ends.first.2 firstClose lastClose allocation.small
  have sourcePaid : sourceTarget^2 ≤ allocation.sourceAllowance^2 := by
    apply sourcePaidForJoin.trans
    rw [allocation.target_eq]
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 16)).mpr
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (4 :
      InverseRootPolynomial.Coordinate) ≤ 16) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1)
  have incoming : Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential firstPotential
    (Readings.firstChartValue coefficients requests readings) ends.first.2 -
      previousPotential - BoundaryRibbon.area previous ends.first.2) ≤
      (80 * allocation.target + 2 * allocation.target) * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
    rw [rightPotential, rightChart, previousReadback]
    exact potentialBound
  exact Extremes.restore
    ends connection allocation positive sourcePaid previous previousPotential gap incoming

end Paths.Extremes
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonIncoming
