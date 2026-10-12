module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation

@[expose] public section

/-! Shared corner owners prepare both selected face sheets directly. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation (MatchedSidePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation (MatchedVerticalSidePreparation)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

namespace HorizontalCrossing

variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The original source-sheet primitive entry at its retained upper-left lifted corner. -/
def leftEntry (_joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get firstPosition).models (vertices.coordinate first.lifted.quad.fourth)
      (vertices.owner frames first.lifted.quad.fourth) :=
  ⟨firstSheet, (first.lifted.edge_endpoints_reached (domains.get firstPosition).models .top).2⟩

/-- The destination-sheet primitive entry at the same original upper-left corner, transported through the retained
reversed crossing edge. -/
def rightEntry (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get nextPosition).models (vertices.coordinate first.lifted.quad.fourth)
      (vertices.owner frames first.lifted.quad.fourth) := by
  refine ⟨joined.crossing.next.sheet, ?_⟩
  have reached := (joined.crossing.next.located.lifted.edge_endpoints_reached
    (domains.get nextPosition).models .bottom).1
  have reversed := joined.reversed
  change joined.crossing.next.located.lifted.quad.edge .bottom =
    (first.lifted.quad.edge .top).reverse at reversed
  rw [reversed] at reached
  exact reached

/-- The matched horizontal trace begins at the actual retained source upper-left coordinate. -/
theorem origin_eq (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    trace.point (trace.vertices.indexed 0) = vertices.coordinate first.lifted.quad.fourth := by
  rw [trace.first_point, joined.side.first_eq, first.lifted.coordinates.2.2.2]
  apply Data.Gaussian.Basic.ext
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_first
  · rfl

/-- Prepare both actual sheet owners on the same retained horizontal side trace and original shared corner. -/
def preparation (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    SidePreparation.MatchedSidePreparation
      (leftEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.HorizontalCrossing.leftEntry
        joined)
      (rightEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.HorizontalCrossing.rightEntry
        joined) trace :=
  MatchedSidePreparation.build
    (leftEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.HorizontalCrossing.leftEntry
      joined)
    (rightEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.HorizontalCrossing.rightEntry
      joined)
    (leftDomain := (domains.get firstPosition).domain firstSheet)
    (rightDomain := (domains.get nextPosition).domain joined.crossing.next.sheet) trace
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.HorizontalCrossing.origin_eq joined trace)

end HorizontalCrossing

namespace VerticalCrossing

variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The original source-sheet primitive entry at its retained lower-right lifted corner. -/
def leftEntry (_joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get firstPosition).models (vertices.coordinate first.lifted.quad.second)
      (vertices.owner frames first.lifted.quad.second) :=
  ⟨firstSheet, (first.lifted.edge_endpoints_reached (domains.get firstPosition).models .right).1⟩

/-- The destination-sheet primitive entry at the same original lower-right corner, transported through the retained
reversed crossing edge. -/
def rightEntry (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get nextPosition).models (vertices.coordinate first.lifted.quad.second)
      (vertices.owner frames first.lifted.quad.second) := by
  refine ⟨joined.crossing.next.sheet, ?_⟩
  have reached := (joined.crossing.next.located.lifted.edge_endpoints_reached
    (domains.get nextPosition).models .left).2
  have reversed := joined.reversed
  change joined.crossing.next.located.lifted.quad.edge .left =
    (first.lifted.quad.edge .right).reverse at reversed
  rw [reversed] at reached
  exact reached

/-- The matched vertical trace begins at the actual retained source lower-right coordinate. -/
theorem origin_eq (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    trace.point (trace.vertices.indexed 0) = vertices.coordinate first.lifted.quad.second := by
  rw [trace.first_point, joined.side.first_eq, first.lifted.coordinates.2.1]
  apply Data.Gaussian.Basic.ext
  · rfl
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_first

/-- Prepare both actual sheet owners on the same retained vertical side trace and original shared corner. -/
def preparation (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    VerticalSidePreparation.MatchedVerticalSidePreparation
      (leftEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.VerticalCrossing.leftEntry
        joined)
      (rightEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.VerticalCrossing.rightEntry
        joined) trace :=
  MatchedVerticalSidePreparation.build
    (leftEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.VerticalCrossing.leftEntry
      joined)
    (rightEntry := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.VerticalCrossing.rightEntry
      joined)
    (leftDomain := (domains.get firstPosition).domain firstSheet)
    (rightDomain := (domains.get nextPosition).domain joined.crossing.next.sheet) trace
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations.VerticalCrossing.origin_eq joined trace)

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
