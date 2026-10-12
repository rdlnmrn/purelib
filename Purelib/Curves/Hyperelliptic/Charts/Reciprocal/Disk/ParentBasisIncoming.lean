module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
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
import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisConnection
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisConnection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration.BasisBoundarySample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

@[expose] public section

/-! Discharge a restored parent's incoming gap and potential error from the
actual joined root readings and certified endpoint values. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisIncoming

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRequests (BasisEnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundarySample (BasisBoundarySample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisBoundaryBound (ParentBasisBoundaryBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisRestoration (ParentBasisRestorationAllowance)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpointValues (EndpointEstimate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisSourceRestoration.BasisBoundarySample
  (SourceRestoration)
open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)
open Purelib.Integration.Path.IncrementRestoration (potential)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (radialArea)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Coordinate}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace ParentBasisRestorationAllowance

variable {edges : List ParameterEdge} {bank :
  Bank regular data edges} {owners :
  Owners bank}
  {allowance energyTarget : Coordinate} {energyFloor energyDepth :
    Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins (BasisRestorationRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisEndpoints (BasisEndpointPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint (Reading)

variable {leftCount rightCount leftIndex rightIndex joinFloor : Nat}
  {leftParent rightParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {leftPatch : PreparedPatch leftParent}
  {rightPatch : PreparedPatch rightParent}
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
  {bounds : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joined : Join leftPoint rightPoint}

open Purelib.Integration.Path.IncrementRestoration in
/-- The incoming gap and shifted-potential error are consequences of the retained root join. Only endpoint readbacks and
their acquired estimates enter. -/
def connectionFromReadings (allocation : ParentBasisRestoration.ParentBasisRestorationAllowance edges.length allowance)
    {requests : ParentChartRequests.ChartRequests allocation.target floor owners} {plans :
      ParentChartRequests.ChartPlans capSample minimum requests}
    {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated : ChartPlans.EvaluationData readingIndex
      plans cells}
    {energies : ParentBasisRequests.BasisEnergyData (polynomials := polynomials) energyTarget energyFloor energyDepth
      plans cells evaluated}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {sample : ParentBasisBoundarySample.BasisBoundarySample energies coefficients allocation.target}
    {sourceTarget previousTarget : InverseRootPolynomial.Coordinate}
    (restoration : BasisBoundarySample.SourceRestoration sample allocation.target sourceTarget)
    (sourceLe : sourceTarget ≤ ParentBasisRestorationAllowance.sourceTarget allocation)
    (budget : ParentBasisBoundaryBound.ParentBasisBoundaryBudget plans cells evaluated)
    (request : RestorationJoins.BasisRestorationRequest basis joined allocation.target joinFloor)
    (leftReading : ChartReadings.Endpoint.Reading leftEndpoint leftIndex)
    (rightReading : ChartReadings.Endpoint.Reading rightEndpoint rightIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex)
    (rightRoot : sample.firstRoot = rightReading.coordinate)
    (previousSource previous previousPotential : InverseRootPolynomial.Gaussian)
    (previousReadback : previousPotential = potential
      (RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth leftReading.coordinate)
      (polynomials.value coefficients leftReading.coordinate) previous)
    (previousLe : previousTarget ≤ ParentBasisRestorationAllowance.sourceTarget allocation)
    (previousEstimate : ParentBasisEndpointValues.EndpointEstimate coefficients previousTarget
      (polynomials.value coefficients leftReading.coordinate) (previousSource, previous)) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients (restoration.restored.path previous)
      previous restoration.restored.lastValue previousPotential restoration.restored.lastPotential
      ((edges.length : InverseRootPolynomial.Coordinate) * energyTarget + allowance) := by
  let restored := restoration.restored
  have sourceEq : ParentBasisRestorationAllowance.sourceTarget allocation = request.endpointTarget :=
    request.endpoint_eq.symm
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
        Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have firstClose := previousEstimate.direct_close.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (previousLe.trans_eq sourceEq) normNonnegative)
  have lastClose : Data.Gaussian.Norm.Basic.normSq (restored.firstValue - sample.firstValue) ≤
      request.endpointTarget * PreparedObservationCoercivity.coefficientNormSq coefficients :=
    restoration.first_estimate.direct_close.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (sourceLe.trans_eq sourceEq) normNonnegative)
  rw [sample.first_value, rightRoot] at lastClose
  have gap := request.direct_gap coefficients firstClose lastClose
    (request.chart_gap polynomials coefficients leftReading rightReading branch leftInside rightInside leftLater
      rightLater)
  have potential := request.potential_accurate polynomials coefficients leftReading rightReading branch
    leftInside rightInside leftLater rightLater energyDepth previous restored.firstValue firstClose lastClose
      allocation.small
  have error : Data.Gaussian.Norm.Basic.normSq (restored.joinError previous previousPotential) ≤
      (80 * allocation.target + 2 * allocation.target) * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
    rw [EndpointRestoration.joinError, restored.first_potential,
      sample.first_radial, sample.first_value, rightRoot, previousReadback]
    exact potential
  exact ParentBasisRestorationAllowance.connection
    allocation restored budget branch previous previousPotential gap error

end ParentBasisRestorationAllowance
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBasisIncoming
