module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
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
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAngularRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartOrientation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
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

open Purelib.Riemann

public section

/-! Every common-interval fan has certified root bounds and signed orientation
on the same reading bank used by its primitive paths and physical connectors. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation

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
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

/-- Every retained common-interval segment has bounded endpoint roots and positive signed root orientation.

The predicate follows the actual acquired interval paths in their original order. -/
@[expose] def Orientation : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Prop
  | _, .nil, _, _ => True
  | _, .cons _ tail, plans, readings =>
      (∀ segment ∈
        (IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments,
        Gaussian.Norm.Basic.normSq segment.last.root.coordinate ≤ 2 ∧ Gaussian.Norm.Basic.normSq
          segment.first.root.coordinate ≤ 2 ∧
        0 < Energy.AffineTriangle.crossEnergy segment.last.root.coordinate segment.first.root.coordinate) ∧
      CommonChartOrientation.Orientation tail plans.2
        readings.2

/-- The original common reading geometry and paid angular requests certify all interval root bounds and signed
orientations.

The same acquired roots are used, with the odd-degree branch condition, positive parent orientation and common tolerance
at most one. -/
theorem orientation (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (small : target ≤ 1) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
    (readings : CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage requests plans) → CommonChartGeometry.Geometry
      requests plans readings →
    (angular : CommonAngularRequests.BasisCommonAngularRequests regular depth
      intervals) → angular.Fits target →
    Orientation requests plans readings
  | _, .nil, _, _, _, .nil, _ => True.intro
  | _, .cons _ tail, plans, readings, certified, .cons head remaining, paid => by
      refine ⟨?_, CommonChartOrientation.orientation branch
        oriented small tail plans.2 readings.2 certified.2.2.2 remaining paid.2⟩
      intro segment member
      exact
        ⟨IntervalChartOrientation.BasisIntervalChartRequest.Plan.Evaluation.root_norm_upper
        branch small segment.last,

          IntervalChartOrientation.BasisIntervalChartRequest.Plan.Evaluation.root_norm_upper
          branch small segment.first,

          IntervalChartOrientation.BasisIntervalChartRequest.Plan.Evaluation.coordinate_area_positive
          readings.1.evaluated head branch oriented small paid.1 segment member
          ((certified.2.2.1 segment member).2.1)⟩

/-- Selecting the minimum of the two positive request tolerances supplies
both conclusions. Angular requests are made at the eventual spatial depth. -/
theorem geometry_and_orientation {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} {spatialFloor : Nat}
    (coordinate : CommonCoordinateRequest.BasisCommonCoordinateRequest
      regular intervals spatialFloor)
    (angular : CommonAngularRequests.BasisCommonAngularRequests regular depth
      intervals)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (later : coordinate.depth ≤ depth) (smaller : target ≤ min coordinate.tolerance angular.tolerance)
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals)
    (plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) (readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) :
    CommonChartGeometry.Geometry requests plans readings ∧
      Orientation requests plans readings := by
  have coordinateLe := smaller.trans (Data.Rat.Fraction.Order.Basic.min_le_left _ _)
  have angularLe := smaller.trans (Data.Rat.Fraction.Order.Basic.min_le_right _ _)
  have geometric := CommonChartGeometry.geometry_of_request coordinate branch
    later coordinateLe requests plans readings
  exact ⟨geometric, orientation branch oriented
    (coordinateLe.trans coordinate.small) requests plans readings
    geometric angular (angular.fits_of_le angularLe)⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartOrientation
