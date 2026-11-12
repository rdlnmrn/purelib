module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

open Purelib.Integration.Energy

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

@[expose] public section

/-! Signed fan orientation is proved on the actual acquired subinterval path.
Its angular request uses the subinterval width, not the anchor cell width. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartOrientation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest (Model)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace BasisIntervalChartRequest

variable {interval : BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Geometry.Rational.Box}
  {request : BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace Plan.Evaluation

variable {plan :
  Plan
  request capSample polynomials minimum}
  {comparison : ArcSamples.Data regular interval.anchor.cell}
  {sample : ArcSamples.Sample comparison capSample}
  {bank : BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- A unit-bounded reading at a simple reciprocal origin has squared coordinate norm at most two. -/
theorem root_norm_upper (branch : HyperellipticReciprocal.originOrder curve = 1)
    (small : target ≤ 1) {parameter : Coordinate}
    (reading : Reading regular (Model interval) sample parameter target floor
      stage) :
    Basic.normSq reading.root.coordinate ≤ 2 := by
  have square := reading.square
  rw [branch, pow_one, Basic.normSq_eq_canonical] at square
  have unit := Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve
    (data.boundary.point ⟨interval.anchor.owner.left.inside.1.trans reading.prepared.inside.1,
      reading.prepared.inside.2.trans interval.anchor.owner.right.inside.2⟩))
  rw [Basic.normSq_eq_canonical] at unit ⊢
  exact ReciprocalDiskCoordinateOrientation.coordinate_norm_upper
    (root := reading.root.coordinate) (point := (parent.edge.point parameter)⁻¹)
    (tolerance := target) unit small square

/-- The acquired segment has positive reversed coordinate cross energy when the original edge is positively oriented and
the retained angular margin and dot-product conditions are paid.

The angular bound uses the actual common-subinterval width. -/
theorem coordinate_area_positive (evaluated : Plan.Evaluation plan sample bank stage)
    (angular : AngularRequest comparison depth interval.edge.left.parameter
      interval.edge.right.parameter)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (small : target ≤ 1) (paid : 16 * target ≤ angular.margin ^ 2)
    (segment : Segment regular (Model interval) sample target floor stage)
    (member : segment ∈ (Evaluation.path evaluated).segments)
    (dot : 0 < segment.first.root.coordinate.re * segment.last.root.coordinate.re +
      segment.first.root.coordinate.im * segment.last.root.coordinate.im) :
    0 < crossEnergy segment.last.root.coordinate segment.first.root.coordinate := by
  have unit (parameter : Coordinate)
      (inside : interval.anchor.owner.left.parameter ≤ parameter ∧ parameter ≤ interval.anchor.owner.right.parameter) :
      Basic.normSq (parent.edge.point parameter)⁻¹ ≤ 1 :=
    Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve
      (data.boundary.point ⟨interval.anchor.owner.left.inside.1.trans inside.1,
        inside.2.trans interval.anchor.owner.right.inside.2⟩))
  have firstSquare := segment.first.square
  have lastSquare := segment.last.square
  rw [branch, pow_one, Basic.normSq_eq_canonical] at firstSquare lastSquare
  have firstUnit := unit segment.firstParameter segment.first.prepared.inside
  have lastUnit := unit segment.lastParameter segment.last.prepared.inside
  rw [Basic.normSq_eq_canonical] at firstUnit lastUnit
  exact ReciprocalDiskCoordinateOrientation.coordinate_area_positive
    (first := segment.first.root.coordinate) (last := segment.last.root.coordinate)
    (firstPoint := (parent.edge.point segment.firstParameter)⁻¹)
    (lastPoint := (parent.edge.point segment.lastParameter)⁻¹)
    (tolerance := target) (margin := angular.margin) firstUnit lastUnit
    segment.first.prepared.request.positive small firstSquare lastSquare dot angular.positive
    (angular.lower oriented segment.first.prepared.inside segment.last.prepared.inside
      ((Evaluation.path evaluated).width_eq segment member)) paid

end Plan.Evaluation
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartOrientation
