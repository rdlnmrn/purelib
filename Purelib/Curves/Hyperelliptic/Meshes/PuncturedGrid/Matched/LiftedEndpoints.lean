module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
public import Purelib.Riemann.Paths.RectangularMatchedChords
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
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
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh

open Purelib.Topology.Polygon

@[expose] public section

/-! Both ends of the actual matched traces use the retained lifted corner owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
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
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

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

/-- The original source-sheet primitive entry at the actual retained upper-right terminal corner. -/
def leftTerminalEntry (_joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get firstPosition).models (vertices.coordinate first.lifted.quad.third)
      (vertices.owner frames first.lifted.quad.third) :=
  ⟨firstSheet, (first.lifted.edge_endpoints_reached (domains.get firstPosition).models .top).1⟩

/-- The original destination-sheet primitive entry at that same retained terminal corner, transported through the exact
reversed crossing edge. -/
def rightTerminalEntry (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get nextPosition).models (vertices.coordinate first.lifted.quad.third)
      (vertices.owner frames first.lifted.quad.third) := by
  refine ⟨joined.crossing.next.sheet, ?_⟩
  have reached := (joined.crossing.next.located.lifted.edge_endpoints_reached
    (domains.get nextPosition).models .bottom).2
  have reversed := joined.reversed
  change joined.crossing.next.located.lifted.quad.edge .bottom =
    (first.lifted.quad.edge .top).reverse at reversed
  rw [reversed] at reached
  exact reached

/-- The actual horizontal trace terminates at the original source's retained upper-right corner. -/
theorem terminal_eq (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    trace.point (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      vertices.coordinate first.lifted.quad.third := by
  rw [trace.last_point, joined.side.last_eq, first.lifted.coordinates.2.2.1]
  apply Data.Gaussian.Basic.ext
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_last
  · rfl

/-- The first actual matched horizontal piece starts at the original lifted upper-left corner. -/
theorem first_piece_eq (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns_eq
      0)).first =
      vertices.coordinate first.lifted.quad.fourth := by
  rw [joined.side.first_eq, first.lifted.coordinates.2.2.2]
  apply Data.Gaussian.Basic.ext
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_first
  · rfl

/-- The last actual matched horizontal piece ends at the original lifted upper-right corner. -/
theorem last_piece_eq (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns_eq
      (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns))).last =
      vertices.coordinate first.lifted.quad.third := by
  rw [joined.side.last_eq, first.lifted.coordinates.2.2.1]
  apply Data.Gaussian.Basic.ext
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_last
  · rfl

/-- The actual left-owner horizontal chord reads the original lifted initial and terminal corners. -/
theorem leftChord_eq_corners (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    (values : _) :
    joined.side.leftChord values =
      Stokes.edgeArea
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryColumns_eq 0)).leftColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryColumns_eq 0)).leftRow
          (vertices.coordinate first.lifted.quad.fourth))
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryColumns_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns))).leftColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryColumns_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns))).leftRow
          (vertices.coordinate first.lifted.quad.third)) := by
  rw [MatchedHorizontalSide.leftChord,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.HorizontalCrossing.first_piece_eq joined,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.HorizontalCrossing.last_piece_eq joined]

/-- The actual right-owner horizontal chord reads the same original lifted initial and terminal corners. -/
theorem rightChord_eq_corners (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    (values : _) :
    joined.side.rightChord values =
      Stokes.edgeArea
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryColumns_eq 0)).rightColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryColumns_eq 0)).rightRow
          (vertices.coordinate first.lifted.quad.fourth))
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryColumns_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns))).rightColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryColumns_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryColumns))).rightRow
          (vertices.coordinate first.lifted.quad.third)) := by
  rw [MatchedHorizontalSide.rightChord,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.HorizontalCrossing.first_piece_eq joined,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.HorizontalCrossing.last_piece_eq joined]

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The original source-sheet primitive entry at the actual retained upper-right terminal corner. -/
def leftTerminalEntry (_joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get firstPosition).models (vertices.coordinate first.lifted.quad.third)
      (vertices.owner frames first.lifted.quad.third) :=
  ⟨firstSheet, (first.lifted.edge_endpoints_reached (domains.get firstPosition).models .right).2⟩

/-- The original destination-sheet primitive entry at that same retained terminal corner, transported through the exact
reversed crossing edge. -/
def rightTerminalEntry (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    FaceModels.Entry (domains.get nextPosition).models (vertices.coordinate first.lifted.quad.third)
      (vertices.owner frames first.lifted.quad.third) := by
  refine ⟨joined.crossing.next.sheet, ?_⟩
  have reached := (joined.crossing.next.located.lifted.edge_endpoints_reached
    (domains.get nextPosition).models .left).1
  have reversed := joined.reversed
  change joined.crossing.next.located.lifted.quad.edge .left =
    (first.lifted.quad.edge .right).reverse at reversed
  rw [reversed] at reached
  exact reached

/-- The actual vertical trace terminates at the original source's retained upper-right corner. -/
theorem terminal_eq (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    {depth : Nat} (trace : joined.side.Trace depth) :
    trace.point (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      vertices.coordinate first.lifted.quad.third := by
  rw [trace.last_point, joined.side.last_eq, first.lifted.coordinates.2.2.1]
  apply Data.Gaussian.Basic.ext
  · rfl
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_last

/-- The first actual matched vertical piece starts at the original lifted lower-right corner. -/
theorem first_piece_eq (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows_eq
      0)).first =
      vertices.coordinate first.lifted.quad.second := by
  rw [joined.side.first_eq, first.lifted.coordinates.2.1]
  apply Data.Gaussian.Basic.ext
  · rfl
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_first

/-- The last actual matched vertical piece ends at the original lifted upper-right corner. -/
theorem last_piece_eq (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows_eq
      (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows))).last =
      vertices.coordinate first.lifted.quad.third := by
  rw [joined.side.last_eq, first.lifted.coordinates.2.2.1]
  apply Data.Gaussian.Basic.ext
  · rfl
  · exact ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_last

/-- The actual left-owner vertical chord reads the original lifted initial and terminal corners. -/
theorem leftChord_eq_corners (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (values : _) :
    joined.side.leftChord values =
      Stokes.edgeArea
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryRows_eq 0)).leftColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryRows_eq 0)).leftRow
          (vertices.coordinate first.lifted.quad.second))
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryRows_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows))).leftColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryRows_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows))).leftRow
          (vertices.coordinate first.lifted.quad.third)) := by
  rw [MatchedVerticalSide.leftChord,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.VerticalCrossing.first_piece_eq joined,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.VerticalCrossing.last_piece_eq joined]

/-- The actual right-owner vertical chord reads the same original lifted initial and terminal corners. -/
theorem rightChord_eq_corners (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (values : _) :
    joined.side.rightChord values =
      Stokes.edgeArea
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryRows_eq 0)).rightColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryRows_eq 0)).rightRow
          (vertices.coordinate first.lifted.quad.second))
        (values (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
          firstPosition).boundaryRows_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows))).rightColumn
          (joined.side.pieces (Fin.cast ((request.entries.get firstSheet).meshes.entries.get
            firstPosition).boundaryRows_eq
            (Fin.last ((request.entries.get firstSheet).meshes.entries.get firstPosition).boundaryRows))).rightRow
          (vertices.coordinate first.lifted.quad.third)) := by
  rw [MatchedVerticalSide.rightChord,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.VerticalCrossing.first_piece_eq joined,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints.VerticalCrossing.last_piece_eq joined]

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedEndpoints
