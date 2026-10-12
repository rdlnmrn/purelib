module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FaceSides
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Matched observation boundaries follow the actual lifted dual crossing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)

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

variable (request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target)

set_option genInjectivity false in
/-- An actual lifted top-to-bottom crossing with the corresponding retained matched observation boundary.

The next sheet comes from the original crossing and both lifted side orientations are certified. -/
structure HorizontalCrossing (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) (firstUpper lastUpper : Bool) where
  /-- The actual retained lifted dual crossing and its dependent next-face sheet. -/ crossing : LiftedMesh.Crossing
    first .top nextPosition .bottom firstUpper lastUpper
  /-- The next retained lifted boundary edge is exactly the reverse of the original crossing edge. -/ reversed :
    crossing.next.located.lifted.quad.edge (GridSide.kind .bottom) =
    (first.lifted.quad.edge (GridSide.kind .top)).reverse
  /-- The matched observation side between the two actual sheet-specific retained face meshes. -/ side :
    let firstMesh := (request.entries.get firstSheet).meshes.entries.get firstPosition
    let lastMesh := (request.entries.get crossing.next.sheet).meshes.entries.get nextPosition
    ObservationMesh.MatchedHorizontalSide firstMesh lastMesh
      (Fin.cast firstMesh.boundaryRows_eq (Fin.last firstMesh.boundaryRows))
      (Fin.cast lastMesh.boundaryRows_eq 0) faces.regulars[firstPosition.val].cell.box.yUpper

set_option cleanup.letToHave false in
constructive_injectivity HorizontalCrossing

/-- Cross the actual lifted top side and retain the matched bottom observation boundary on the selected next sheet. -/
def HorizontalCrossing.build (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.xLower = faces.regulars[nextPosition.val].cell.box.xLower)
    (upperEq : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xUpper)
    (adjacent : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yLower)
    (firstUpper lastUpper : Bool) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.HorizontalCrossing
      request first nextPosition firstUpper lastUpper := by
  have startEq : GridSide.start .bottom faces.regulars[nextPosition.val].cell.box =
      GridSide.finish .top faces.regulars[firstPosition.val].cell.box := by
    exact Data.Gaussian.Basic.ext lowerEq.symm adjacent.symm
  have finishEq : GridSide.finish .bottom faces.regulars[nextPosition.val].cell.box =
      GridSide.start .top faces.regulars[firstPosition.val].cell.box := by
    exact Data.Gaussian.Basic.ext upperEq.symm adjacent.symm
  let crossing := LiftedMesh.crossSide first .top nextPosition .bottom startEq finishEq firstUpper lastUpper
  exact ⟨crossing, LiftedMesh.opposite_sides first .top .bottom crossing.next startEq finishEq,
    FaceSides.matchedTopBottom request firstSheet
      crossing.next.sheet firstPosition nextPosition lowerEq upperEq adjacent⟩

set_option genInjectivity false in
/-- An actual lifted right-to-left crossing with the corresponding retained matched observation boundary.

The next sheet comes from the original crossing and both lifted side orientations are certified. -/
structure VerticalCrossing (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length) (firstUpper lastUpper : Bool) where
  /-- The actual retained lifted dual crossing and its dependent next-face sheet. -/ crossing : LiftedMesh.Crossing
    first .right nextPosition .left firstUpper lastUpper
  /-- The next retained lifted boundary edge is exactly the reverse of the original crossing edge. -/ reversed :
    crossing.next.located.lifted.quad.edge (GridSide.kind .left) =
    (first.lifted.quad.edge (GridSide.kind .right)).reverse
  /-- The matched observation side between the two actual sheet-specific retained face meshes. -/ side :
    let firstMesh := (request.entries.get firstSheet).meshes.entries.get firstPosition
    let lastMesh := (request.entries.get crossing.next.sheet).meshes.entries.get nextPosition
    ObservationMesh.MatchedVerticalSide firstMesh lastMesh
      (Fin.cast firstMesh.boundaryColumns_eq (Fin.last firstMesh.boundaryColumns))
      (Fin.cast lastMesh.boundaryColumns_eq 0) faces.regulars[firstPosition.val].cell.box.xUpper

set_option cleanup.letToHave false in
constructive_injectivity VerticalCrossing

/-- Cross the actual lifted right side and retain the matched left observation boundary on the selected next sheet. -/
def VerticalCrossing.build (first : mesh.LocatedFace firstPosition firstSheet)
    (nextPosition : Fin faces.regulars.length)
    (lowerEq : faces.regulars[firstPosition.val].cell.box.yLower = faces.regulars[nextPosition.val].cell.box.yLower)
    (upperEq : faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yUpper)
    (adjacent : faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xLower)
    (firstUpper lastUpper : Bool) : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.VerticalCrossing
      request first nextPosition firstUpper lastUpper := by
  have startEq : GridSide.start .left faces.regulars[nextPosition.val].cell.box =
      GridSide.finish .right faces.regulars[firstPosition.val].cell.box := by
    exact Data.Gaussian.Basic.ext adjacent.symm upperEq.symm
  have finishEq : GridSide.finish .left faces.regulars[nextPosition.val].cell.box =
      GridSide.start .right faces.regulars[firstPosition.val].cell.box := by
    exact Data.Gaussian.Basic.ext adjacent.symm lowerEq.symm
  let crossing := LiftedMesh.crossSide first .right nextPosition .left startEq finishEq firstUpper lastUpper
  exact ⟨crossing, LiftedMesh.opposite_sides first .right .left crossing.next startEq finishEq,
    FaceSides.matchedRightLeft request firstSheet
      crossing.next.sheet firstPosition nextPosition lowerEq upperEq adjacent⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
