module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceHandoffs
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
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

/-! Continue across surface-piece boundaries from actual retained prefix
owners. Both fixed face sheets survive each handoff unchanged. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.TraceHandoffs

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation (MatchedSidePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation (MatchedVerticalSidePreparation)
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

section
variable {leftBox rightBox : Purelib.Geometry.Rational.Box}
  {leftMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftRow : Fin leftMesh.partition.y.intervals.length} {rightRow : Fin rightMesh.partition.y.intervals.length}
  {height : Purelib.Data.Rat.Fraction.Rational} {depth : Nat}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh
    rightMesh leftRow rightRow height}

namespace MatchedSidePreparation

variable {trace : side.Trace depth}

/-- Read the actual terminal root owner already retained by the selected trace-prefix preparation. -/
def ownerAt (preparation : SidePreparation.MatchedSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    SquareRootContinuationChain.Owner (curve.polynomial.eval (trace.point (trace.vertices.indexed vertex))) :=
  (preparation.prepared.get vertex).traced.finishOwner

/-- Transport the original first face entry along the actual retained trace prefix to its cached terminal owner. -/
def leftEntryAt (preparation : SidePreparation.MatchedSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    FaceModels.Entry firstModels (trace.point (trace.vertices.indexed vertex))
      (ownerAt preparation
      vertex) :=
  Entry.follow leftEntry (preparation.prepared.get vertex).traced (preparation.leftInside vertex)

/-- Transport the original second face entry along the same retained trace prefix to that exact terminal owner. -/
def rightEntryAt (preparation : SidePreparation.MatchedSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    FaceModels.Entry lastModels (trace.point (trace.vertices.indexed vertex))
      (ownerAt preparation
      vertex) :=
  Entry.follow rightEntry (preparation.prepared.get vertex).traced (preparation.rightInside vertex)

/-- Prepare the next actual matched trace from the retained prefix owner while preserving both original fixed face
domains and sheet entries. -/
def continueAt (preparation : SidePreparation.MatchedSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1))
    {nextLeftBox nextRightBox : Rational.Box}
    {nextLeft : RectangularObservationMesh.ObservationMesh leftDomain.cuts nextLeftBox}
    {nextRight : RectangularObservationMesh.ObservationMesh rightDomain.cuts nextRightBox}
    {nextLeftRow : Fin nextLeft.partition.y.intervals.length}
    {nextRightRow : Fin nextRight.partition.y.intervals.length}
    {nextCoordinate : InverseRootPolynomial.Coordinate} {nextDepth : Nat}
    {nextSide : ObservationMesh.MatchedHorizontalSide nextLeft nextRight
      nextLeftRow nextRightRow nextCoordinate}
    (next : nextSide.Trace nextDepth)
    (joined : next.point (next.vertices.indexed 0) = trace.point (trace.vertices.indexed vertex)) :
    SidePreparation.MatchedSidePreparation (leftEntry :=
      leftEntryAt preparation
      vertex) (rightEntry :=
      rightEntryAt preparation
      vertex)
      (leftDomain := leftDomain) (rightDomain := rightDomain) next :=
  MatchedSidePreparation.build (leftEntry :=
    leftEntryAt preparation
    vertex) (rightEntry :=
    rightEntryAt preparation
    vertex)
    (leftDomain := leftDomain) (rightDomain := rightDomain) next joined

end MatchedSidePreparation
end

section
variable {leftBox rightBox : Purelib.Geometry.Rational.Box}
  {leftMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftColumn : Fin leftMesh.partition.x.intervals.length} {rightColumn : Fin rightMesh.partition.x.intervals.length}
  {horizontal : Purelib.Data.Rat.Fraction.Rational} {depth : Nat}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide leftMesh
    rightMesh leftColumn rightColumn horizontal}

namespace MatchedVerticalSidePreparation

variable {trace : side.Trace depth}

/-- Read the actual terminal root owner already retained by the selected trace-prefix preparation. -/
def ownerAt (preparation : VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    SquareRootContinuationChain.Owner (curve.polynomial.eval (trace.point (trace.vertices.indexed vertex))) :=
  (preparation.prepared.get vertex).traced.finishOwner

/-- Transport the original first face entry along the actual retained trace prefix to its cached terminal owner. -/
def leftEntryAt (preparation : VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    FaceModels.Entry firstModels (trace.point (trace.vertices.indexed vertex))
      (ownerAt
      preparation vertex) :=
  Entry.follow leftEntry (preparation.prepared.get vertex).traced (preparation.leftInside vertex)

/-- Transport the original second face entry along the same retained trace prefix to that exact terminal owner. -/
def rightEntryAt (preparation : VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    FaceModels.Entry lastModels (trace.point (trace.vertices.indexed vertex))
      (ownerAt
      preparation vertex) :=
  Entry.follow rightEntry (preparation.prepared.get vertex).traced (preparation.rightInside vertex)

/-- Prepare the next actual matched trace from the retained prefix owner while preserving both original fixed face
domains and sheet entries. -/
def continueAt (preparation : VerticalSidePreparation.MatchedVerticalSidePreparation trace)
    (vertex : Fin (trace.vertices.rest.length + 1))
    {nextLeftBox nextRightBox : Rational.Box}
    {nextLeft : RectangularObservationMesh.ObservationMesh leftDomain.cuts nextLeftBox}
    {nextRight : RectangularObservationMesh.ObservationMesh rightDomain.cuts nextRightBox}
    {nextLeftColumn : Fin nextLeft.partition.x.intervals.length}
    {nextRightColumn : Fin nextRight.partition.x.intervals.length}
    {nextCoordinate : InverseRootPolynomial.Coordinate} {nextDepth : Nat}
    {nextSide : ObservationMesh.MatchedVerticalSide nextLeft nextRight
      nextLeftColumn nextRightColumn nextCoordinate}
    (next : nextSide.Trace nextDepth)
    (joined : next.point (next.vertices.indexed 0) = trace.point (trace.vertices.indexed vertex)) :
    VerticalSidePreparation.MatchedVerticalSidePreparation (leftEntry :=
      leftEntryAt
      preparation vertex) (rightEntry :=
      rightEntryAt
      preparation vertex)
      (leftDomain := leftDomain) (rightDomain := rightDomain) next :=
  MatchedVerticalSidePreparation.build (leftEntry :=
    leftEntryAt
    preparation vertex) (rightEntry :=
    rightEntryAt
    preparation vertex)
    (leftDomain := leftDomain) (rightDomain := rightDomain) next joined

end MatchedVerticalSidePreparation
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.TraceHandoffs
