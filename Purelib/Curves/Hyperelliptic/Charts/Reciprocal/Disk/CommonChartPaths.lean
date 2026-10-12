module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib.Data.Vector

open Purelib.Integration.Path.Dyadic

public section

/-! Actual common-cover intervals supply all dyadic vertex owners and root
joins for paired chart acquisition, including the ramified reciprocal cap. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Periods.CenteredBilinearPath hiding Coordinate
variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  (interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval cover
    otherCover)

set_option genInjectivity false in
/-- The two actual retained differential-recast cap points at one common parameter, with their operational root join. -/
structure ChartVertex (firstModel : UniformReciprocalRootChannels.RootModel interval.first.cell)
    (secondModel : UniformReciprocalRootChannels.RootModel interval.second.cell) (parameter : Coordinate) where
  /-- The actual first differential's retained cap point at this parameter. -/ first : ArcOwners.Point cap firstModel
    parameter
  /-- The actual second differential's retained cap point at this parameter. -/ second : ArcOwners.Point cap secondModel
    parameter
  /-- The operational join between these exact two retained cap points. -/ joined : ArcOwners.Join first second

constructive_injectivity ChartVertex

/-- The dependent vector of actual paired cap vertices on the retained indexed dyadic parameter list. -/
@[expose] def ChartVertices (firstModel : UniformReciprocalRootChannels.RootModel interval.first.cell)
    (secondModel : UniformReciprocalRootChannels.RootModel interval.second.cell) (tail : List Coordinate) :=
  Data.Vector.DependentVector (fun i : Fin (tail.length + 1) =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartVertex (cap := cap) interval firstModel
      secondModel
      (DyadicTrace.indexed interval.edge.left.parameter tail i))

set_option genInjectivity false in
/-- The exact common-cover dyadic parameter tail, both retained root models and all actual paired vertex owners. -/
structure ChartGeometry (depth : Nat) where
  /-- The cached ordered dyadic parameter tail on the original common interval. -/ tail : List Coordinate
  /-- The parameter tail is exactly the original interval's dyadic trace at the retained depth. -/ tail_eq : tail =
    DyadicTrace.tail depth interval.edge.left.parameter interval.edge.right.parameter
  /-- The retained root model on the actual first differential's cover cell. -/ firstModel :
    UniformReciprocalRootChannels.RootModel interval.first.cell
  /-- The retained root model on the actual second differential's cover cell. -/ secondModel :
    UniformReciprocalRootChannels.RootModel interval.second.cell
  /-- The cached paired cap points and joins at every exact indexed parameter. -/ vertices :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartVertices (cap := cap) interval firstModel
    secondModel tail

constructive_injectivity ChartGeometry

namespace ChartGeometry

/-- Cache both original root models and construct every actual dyadic vertex with its automatic differential-recast root
join. -/
@[expose] def build (depth : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap :=
  cap) interval depth := by
  let firstModel := RootModel.build interval.first.cell
  let secondModel := RootModel.build interval.second.cell
  let tail := DyadicTrace.tail depth interval.edge.left.parameter interval.edge.right.parameter
  let vertices : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartVertices (cap := cap) interval
    firstModel secondModel tail :=
    DependentVector.ofFn (fun i => by
      let parameter := DyadicTrace.indexed interval.edge.left.parameter tail i
      have inside := DyadicTrace.indexed_inside depth interval.ordered i
      let first := ArcOwners.Point.build cap firstModel parameter
        ⟨interval.first.lower.trans inside.1, inside.2.trans interval.first.upper⟩
      let second := ArcOwners.Point.build cap secondModel parameter
        ⟨interval.second.lower.trans inside.1, inside.2.trans interval.second.upper⟩
      exact ⟨first, second, Join.ofRecast first second⟩)
  exact ⟨tail, rfl, firstModel, secondModel, vertices⟩

variable {interval} {depth : Nat}

/-- Read the retained operational join at the supplied actual dyadic vertex. -/
@[expose] def joins (geometry : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap)
  interval depth)
    (i : Fin (geometry.tail.length + 1)) :
    ArcOwners.Join (geometry.vertices.get i).first (geometry.vertices.get i).second :=
  (geometry.vertices.get i).joined

/-- The final retained dyadic vertex has exactly the original common interval's right parameter. -/
theorem last_parameter (geometry : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap :=
  cap) interval depth) :
    DyadicTrace.indexed interval.edge.left.parameter geometry.tail (Fin.last geometry.tail.length) =
      interval.edge.right.parameter := by
  rw [DyadicTrace.indexed_last, geometry.tail_eq, DyadicTrace.tail_terminal]

set_option genInjectivity false in
/-- Adjacent intervals inherit both sheets from their original parent models; no equality of independently sampled roots
is asserted. -/
structure Junction {nextInterval : UniformReciprocalCommonCover.CommonInterval cover otherCover} {nextDepth : Nat}
    (geometry : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth)
    (next : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) nextInterval
      nextDepth) where
  /-- The retained first-differential root join across these two actual adjacent intervals. -/ first : ArcOwners.Join
    (geometry.vertices.get (Fin.last geometry.tail.length)).first (next.vertices.get 0).first
  /-- The retained second-differential root join across these two actual adjacent intervals. -/ second : ArcOwners.Join
    (geometry.vertices.get (Fin.last geometry.tail.length)).second (next.vertices.get 0).second

constructive_injectivity Junction

/-- Join consecutive actual chart endpoints using their retained parent models and certified parameter adjacency. -/
@[expose] def junction {nextInterval : UniformReciprocalCommonCover.CommonInterval cover otherCover} {nextDepth : Nat}
    (geometry : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth)
    (next : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) nextInterval
      nextDepth)
    (adjacent : interval.edge.right.parameter = nextInterval.edge.left.parameter) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry.Junction geometry next :=
  let same := geometry.last_parameter.trans adjacent
  ⟨Join.ofSameParent _ _ same, Join.ofSameParent _ _ same⟩

end ChartGeometry

variable {index : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  (sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
  (otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox)

/-- The paired chart-reading request on the supplied original dyadic vertex owners and joins. -/
@[expose] def ChartRequest {depth : Nat} (geometry :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth)
    (target : Coordinate) (floor : Nat) :=
  PairedChartReadings.ChartPathRequest (sample := sample) (otherSample := otherSample)
    geometry.joins (target := target) (floor := floor)

set_option genInjectivity false in
/-- The retained common-interval geometry and a paid complete paired chart-area request. -/
structure ChartAcquisition (depth : Nat) (target : Coordinate) (floor : Nat) where
  /-- The cached actual dyadic geometry with both original differential root owners. -/ geometry :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth
  /-- The retained reading request on these exact paired chart vertices. -/ request :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartRequest interval sample otherSample geometry
    target floor
  /-- The cached paid complete paired area evaluation for the original target. -/ area : ChartPathRequest.RequestedArea
    request target

constructive_injectivity ChartAcquisition

/-- Build the actual dyadic owners, acquire their recast joins, and pay the full paired area discrepancy at an
internally selected common reading stage. -/
@[expose] def acquireChart (depth : Nat) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartAcquisition interval sample otherSample depth
      target floor :=
  let geometry := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry.build (cap := cap) interval
    depth
  let request := ChartPathRequest.build geometry.joins sample otherSample target positive floor
  ⟨geometry, request, request.acquireRequestedArea target positive⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
