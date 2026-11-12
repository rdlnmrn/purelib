module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Connector values and radial certificates use the endpoint readings already
acquired on the two retained common intervals. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector

open Purelib.Riemann.RootContinuation
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : UniformReciprocalCover.Cover data} {covers :
    SourceLocations.BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget rightSourceTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {first next : CommonCover.BasisCommonInterval cover covers}
  {leftRequest : IntervalChartRequest.BasisIntervalChartRequest first regular
    depth target sourceTarget floor sourceFloor}
  {rightRequest : IntervalChartRequest.BasisIntervalChartRequest next regular
    depth target rightSourceTarget floor sourceFloor}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {leftPlan : IntervalChartAcquisition.BasisIntervalChartRequest.Plan
    leftRequest capSample polynomials minimum}
  {rightPlan : IntervalChartAcquisition.BasisIntervalChartRequest.Plan
    rightRequest capSample polynomials minimum}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joined : ArcOwners.Join leftRequest.last.point rightRequest.first.point}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

set_option genInjectivity false in
/-- The retained primitive values determine the actual connector increment;
its radial estimate includes the signed joining ribbon. -/
structure BasisCommonConnector (left :
  CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition leftPlan
  anchorBank bank stage)
    (right : CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      rightPlan anchorBank bank stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat) (joinTarget :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The cached polynomial basis value at the original left interval's last root reading. -/ firstValue :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The first value uses exactly the retained left endpoint coordinate. -/ first_eq : firstValue = polynomials.value
    coefficients left.evaluated.last.root.coordinate
  /-- The cached polynomial basis value at the original right interval's first root reading. -/ lastValue :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The last value uses exactly the retained right endpoint coordinate. -/ last_eq : lastValue = polynomials.value
    coefficients right.evaluated.first.root.coordinate
  /-- The cached actual connector increment. -/ increment : Normalization.InverseRootPolynomial.Gaussian
  /-- The connector is the last retained endpoint value minus the first. -/ increment_eq : increment = lastValue -
    firstValue
  /-- The connector increment meets the original joining target homogeneously in the coefficient norm. -/
    increment_bound : Gaussian.Norm.Basic.normSq increment ≤ joinTarget *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The actual radial-potential difference, including the signed joining ribbon, meets the original homogeneous
    joining target. -/ radial_bound : Gaussian.Norm.Basic.normSq (
    RootRadialGeometry.radialArea (polynomials.value coefficients) radialDepth
      right.evaluated.first.root.coordinate -
    RootRadialGeometry.radialArea (polynomials.value coefficients) radialDepth
      left.evaluated.last.root.coordinate -
    Path.BoundaryRibbon.area firstValue lastValue) ≤ joinTarget *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity BasisCommonConnector

namespace BasisCommonConnector

/-- Reuse the two actual interval endpoint readings to cache the connector and certify its increment and radial bounds
from their original root join. -/
@[expose] def build (request : JunctionRequests.BasisRequest basis joined
  joinTarget joinFloor)
    (left : CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      leftPlan anchorBank bank stage) (right :
      CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      rightPlan anchorBank bank stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (left.evaluated.last.root.coordinate * left.evaluated.last.root.coordinate))
    (rightInside : regular.padded.Contains (right.evaluated.first.root.coordinate *
      right.evaluated.first.root.coordinate))
    (later : request.index ≤ stage) : BasisCommonConnector
      left right coefficients radialDepth joinTarget := by
  let firstView := ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
    VertexRequests.Prepared.point left.evaluated.last_owner)
    left.evaluated.last.root
  let lastView := ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
    VertexRequests.Prepared.point right.evaluated.first_owner)
    right.evaluated.first.root
  have firstEq : firstView.reading.coordinate = left.evaluated.last.root.coordinate :=
    ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
  have lastEq : lastView.reading.coordinate = right.evaluated.first.root.coordinate :=
    ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
  have beforeInside : regular.padded.Contains (firstView.reading.coordinate * firstView.reading.coordinate) := by
    rw [firstEq]; exact leftInside
  have afterInside : regular.padded.Contains (lastView.reading.coordinate * lastView.reading.coordinate) := by
    rw [lastEq]; exact rightInside
  have estimate := request.radial_accurate polynomials coefficients firstView.reading lastView.reading
    branch beforeInside afterInside later later radialDepth
  have incrementEstimate := request.increment_accurate polynomials coefficients firstView.reading lastView.reading
    branch beforeInside afterInside later later
  rw [firstEq, lastEq] at estimate incrementEstimate
  let firstValue := polynomials.value coefficients left.evaluated.last.root.coordinate
  let lastValue := polynomials.value coefficients right.evaluated.first.root.coordinate
  exact ⟨firstValue, rfl, lastValue, rfl, lastValue - firstValue, rfl, incrementEstimate, estimate⟩

end BasisCommonConnector
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector
