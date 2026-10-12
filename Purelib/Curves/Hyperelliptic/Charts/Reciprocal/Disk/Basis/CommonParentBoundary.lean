module
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

public section

/-! Expose the retained first and last root owners of a complete common parent
before sampling, and acquire their boundary views from the existing root bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary

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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest (BasisCommonParentRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings.BasisCommonParentRequest (Plan)
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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)

/-- The retained common cover contains at least one actual interval.

Its edge identity retains the nonempty dyadic subdivision at the selected
cover depth. Mapping an empty interval list would contradict that exact count. -/
theorem common_nonempty {coverFloor : Nat}
    (common : CommonCover.BasisCommonCover cover covers coverFloor) : common.intervals ≠ [] := by
  intro empty
  have eq := common.edges_eq
  rw [empty, List.map_nil] at eq
  have positive := Nat.two_pow_pos common.depth
  rw [← ClearSheetContinuation.Subdivision.dyadicEdges_length common.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint] at positive
  rw [← eq] at positive
  exact Nat.not_lt_zero _ positive

namespace BasisCommonParentRequest

variable {coverFloor : Nat} {common :
  BasisCommonCover cover covers coverFloor}
  {allowance coefficientTarget : Coordinate}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners (EndpointView)

variable {request :
  BasisCommonParentRequest common basis
  allowance coefficientTarget floor}

/-- The original common-parent request's first retained physical root owner. -/
@[expose] def firstView (request : CommonParentRequest.BasisCommonParentRequest common basis allowance coefficientTarget
  floor) : Owners.EndpointView regular data 0 :=
  BasisCommonChartRequests.firstView request.charts.requests (BasisCommonChartRequests.common_from common)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

/-- The original common-parent request's last retained physical root owner. -/
@[expose] def lastView (request : CommonParentRequest.BasisCommonParentRequest common basis allowance coefficientTarget
  floor) : Owners.EndpointView regular data 1 :=
  BasisCommonChartRequests.lastView request.charts.requests (BasisCommonChartRequests.common_from common)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

/-- Join the actual common-parent boundary owners using the retained source root agreement, before selecting any
polynomial or root-reading stage. -/
@[expose] def join {otherCount otherMinimum otherFloor : Nat}
    {otherParent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {otherPatch : UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
    {otherData : UniformReciprocalModels.Data otherPatch otherCount}
    {otherCover : UniformReciprocalCover.Cover otherData}
    {otherCovers : SourceLocations.BasisSourceCovers otherParent}
    {otherCommon : CommonCover.BasisCommonCover otherCover otherCovers otherMinimum}
    {otherAllowance otherCoefficientTarget : InverseRootPolynomial.Coordinate}
    (first : CommonParentRequest.BasisCommonParentRequest common basis allowance coefficientTarget floor)
    (last : CommonParentRequest.BasisCommonParentRequest otherCommon basis otherAllowance otherCoefficientTarget
      otherFloor)
    (same : parent.edge.point 1 = otherParent.edge.point 0)
    (roots : Gaussian.Equivalence.NamedEquivalent
      (parent.edge.rootName 1 (by decide)) (otherParent.edge.rootName 0 otherParent.edge.baseInside)) :
    ArcOwners.Join
      (lastView
      first).point
      (firstView
      last).point :=
  let source := SourceJoin.build
    (lastView
      first).point.root
      (firstView
      last).point.root (parent.edge.point 1) rfl same.symm roots
  Join.ofRoots (lastView
    first).point
    (firstView
    last).point same
    (SourceJoin.rootEquivalent
      (first :=
        (lastView
        first).point.root) (last :=
        (firstView
        last).point.root) source)

namespace Plan.Acquisition

variable {plan :
  Plan request
  capSample polynomials minimum}

/-- Read the first retained boundary root from the already acquired common-parent bank. -/
@[expose] def firstReading (acquired : Plan.Acquisition plan anchorBank bank stage) :
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.firstView
  request).RootReading capSample stage :=
  Plans.firstReading request.charts.requests acquired.readings
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

/-- Read the last retained boundary root from the already acquired common-parent bank. -/
@[expose] def lastReading (acquired : Plan.Acquisition plan anchorBank bank stage) :
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.BasisCommonParentRequest.lastView
  request).RootReading capSample stage :=
  Plans.lastReading request.charts.requests acquired.readings
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

/-- The acquired first boundary root has its square inside the original padded domain. -/
theorem first_inside (acquired : Plan.Acquisition plan anchorBank bank stage) :
    regular.padded.Contains
      ((firstReading
      acquired).reading.coordinate *
      (firstReading
      acquired).reading.coordinate) :=
  Plans.firstReading_inside request.charts.requests acquired.readings
    (acquired.geometry.inside request.charts.requests plan.charts acquired.readings)
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

/-- The acquired last boundary root has its square inside the original padded domain. -/
theorem last_inside (acquired : Plan.Acquisition plan anchorBank bank stage) :
    regular.padded.Contains
      ((lastReading
      acquired).reading.coordinate *
      (lastReading
      acquired).reading.coordinate) :=
  Plans.lastReading_inside request.charts.requests acquired.readings
    (acquired.geometry.inside request.charts.requests plan.charts acquired.readings)
    (BasisCommonChartRequests.common_from common)
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary.common_nonempty common)

end Plan.Acquisition
end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBoundary
