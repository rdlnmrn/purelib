module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedEndpointPolygon
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointPolygonPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.TraceHandoffs
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs

open Purelib.Geometry

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

open Purelib.Riemann.Topology

@[expose] public section

/-! Piece contacts reuse a retained endpoint preparation's common owner.
Both original face sheets are preserved by the cached contained paths. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (EndpointPolygonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation (MatchedSidePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation (MatchedVerticalSidePreparation)
open Purelib.Integration.Path.PairedEndpointPolygon (pairedEndpointPolygon)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner
    (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularPairedEndpointReadings (PairedEndpointReadingsGeometry)

variable {count : Nat}
  {first : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (OwnedVertex leftDomain.geometry)}
  {last : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace
    (OwnedVertex rightDomain.geometry)}

namespace EndpointPolygonPreparation

variable {geometry : PairedEndpointReadingsGeometry first
  last}
  (preparation : EndpointPolygonPreparation
    (leftEntry := leftEntry) (rightEntry := rightEntry) geometry)
  (vertex : Fin ((Purelib.Integration.Path.PairedEndpointPolygon.pairedEndpointPolygon first last).rest.length + 1))

/-- Read the exact terminal root owner cached by the original endpoint-path preparation. -/
def ownerAt : SquareRootContinuationChain.Owner (curve.polynomial.eval (geometry.points vertex)) :=
  (preparation.prepared.get vertex).traced.finishOwner

/-- Transport the original first-face entry along its retained endpoint path to that exact cached owner. -/
def leftEntryAt : FaceModels.Entry firstModels (geometry.points vertex)
  (ownerAt preparation
  vertex) :=
  Entry.follow leftEntry (preparation.prepared.get vertex).traced (preparation.leftInside vertex)

/-- Transport the original second-face entry along the same retained path to that exact cached owner. -/
def rightEntryAt : FaceModels.Entry lastModels (geometry.points vertex)
  (ownerAt preparation
  vertex) :=
  Entry.follow rightEntry (preparation.prepared.get vertex).traced (preparation.rightInside vertex)

/-- Prepare the actual horizontal matched trace from the retained endpoint owner, preserving both original face domains
and sheets. -/
def horizontalAt {leftBox rightBox : Rational.Box}
    {leftMesh : RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
    {rightMesh : RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
    {leftRow : Fin leftMesh.partition.y.intervals.length} {rightRow : Fin rightMesh.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {depth : Nat}
    {side : ObservationMesh.MatchedHorizontalSide leftMesh rightMesh leftRow rightRow height}
    (trace : side.Trace depth) (origin : trace.point (trace.vertices.indexed 0) = geometry.points vertex) :
    SidePreparation.MatchedSidePreparation (leftEntry :=
      leftEntryAt preparation
      vertex) (rightEntry :=
      rightEntryAt
      preparation vertex)
      (leftDomain := leftDomain) (rightDomain := rightDomain) trace :=
  MatchedSidePreparation.build (leftEntry :=
    leftEntryAt preparation
    vertex) (rightEntry :=
    rightEntryAt preparation
    vertex)
    (leftDomain := leftDomain) (rightDomain := rightDomain) trace origin

/-- Prepare the actual vertical matched trace from the retained endpoint owner, preserving both original face domains
and sheets. -/
def verticalAt {leftBox rightBox : Rational.Box}
    {leftMesh : RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
    {rightMesh : RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
    {leftColumn : Fin leftMesh.partition.x.intervals.length} {rightColumn : Fin rightMesh.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {depth : Nat}
    {side : ObservationMesh.MatchedVerticalSide leftMesh rightMesh leftColumn rightColumn horizontal}
    (trace : side.Trace depth) (origin : trace.point (trace.vertices.indexed 0) = geometry.points vertex) :
    VerticalSidePreparation.MatchedVerticalSidePreparation (leftEntry :=
      leftEntryAt preparation
      vertex) (rightEntry :=
      rightEntryAt
      preparation vertex)
      (leftDomain := leftDomain) (rightDomain := rightDomain) trace :=
  MatchedVerticalSidePreparation.build (leftEntry :=
    leftEntryAt preparation
    vertex) (rightEntry :=
    rightEntryAt preparation
    vertex)
    (leftDomain := leftDomain) (rightDomain := rightDomain) trace origin

end EndpointPolygonPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.EndpointTraceHandoffs
