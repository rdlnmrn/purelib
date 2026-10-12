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

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget rightSourceTarget :
    Normalization.InverseRootPolynomial.Coordinate}
  {first next : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers}
  {leftRequest : Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest first regular
    depth target sourceTarget floor sourceFloor}
  {rightRequest : Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest next regular
    depth target rightSourceTarget floor sourceFloor}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {leftPlan : Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan
    leftRequest capSample polynomials minimum}
  {rightPlan : Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan
    rightRequest capSample polynomials minimum}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join leftRequest.last.point rightRequest.first.point}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

set_option genInjectivity false in
/-- The retained primitive values determine the actual connector increment;
its radial estimate includes the signed joining ribbon. -/
structure BasisCommonConnector (left :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition leftPlan
  anchorBank bank stage)
    (right : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
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
    increment_bound : Data.Gaussian.Norm.Basic.normSq increment ≤ joinTarget *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The actual radial-potential difference, including the signed joining ribbon, meets the original homogeneous
    joining target. -/ radial_bound : Data.Gaussian.Norm.Basic.normSq (
    RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) radialDepth
      right.evaluated.first.root.coordinate -
    RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) radialDepth
      left.evaluated.last.root.coordinate -
    Path.BoundaryRibbon.area firstValue lastValue) ≤ joinTarget *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2

constructive_injectivity BasisCommonConnector

namespace BasisCommonConnector

/-- Reuse the two actual interval endpoint readings to cache the connector and certify its increment and radial bounds
from their original root join. -/
@[expose] def build (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis joined
  joinTarget joinFloor)
    (left : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      leftPlan anchorBank bank stage) (right :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      rightPlan anchorBank bank stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (left.evaluated.last.root.coordinate * left.evaluated.last.root.coordinate))
    (rightInside : regular.padded.Contains (right.evaluated.first.root.coordinate *
      right.evaluated.first.root.coordinate))
    (later : request.index ≤ stage) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector.BasisCommonConnector
      left right coefficients radialDepth joinTarget := by
  let firstView := Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
    Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared.point left.evaluated.last_owner)
    left.evaluated.last.root
  let lastView := Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
    Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared.point right.evaluated.first_owner)
    right.evaluated.first.root
  have firstEq : firstView.reading.coordinate = left.evaluated.last.root.coordinate :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
  have lastEq : lastView.reading.coordinate = right.evaluated.first.root.coordinate :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
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
