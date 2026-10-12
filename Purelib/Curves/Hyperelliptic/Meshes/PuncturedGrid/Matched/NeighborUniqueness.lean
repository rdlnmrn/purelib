module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness.BranchCellBank

open Purelib.Topology.Polygon

@[expose] public section

/-! Two actual crossings across a fixed source side have one destination face. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)

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

/-- The actual destination anchor is the original source face's upper-left physical corner. -/
theorem next_anchor (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    faces.regulars[nextPosition.val].cell.box.anchor = (⟨faces.regulars[firstPosition.val].cell.box.xLower,
      faces.regulars[firstPosition.val].cell.box.yUpper⟩ : Data.Gaussian.Basic.Canonical) := by
  have equal := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    vertices.coordinate edge.start) joined.reversed
  change vertices.coordinate joined.crossing.next.located.lifted.quad.first =
    vertices.coordinate first.lifted.quad.fourth at equal
  rw [joined.crossing.next.located.lifted.coordinates.1, first.lifted.coordinates.2.2.2] at equal
  exact equal

/-- Two actual horizontal crossings from the same original source face have the same destination position. -/
theorem next_position_unique {otherPosition : Fin faces.regulars.length}
    (left : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    (right : LiftedSides.HorizontalCrossing request first otherPosition firstUpper lastUpper) : nextPosition =
      otherPosition := by
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.HorizontalCrossing.next_anchor left
    |>.trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.HorizontalCrossing.next_anchor right).symm
  exact PuncturedFaces.position_eq_of_lower
    faces nextPosition otherPosition
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) equal)
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) equal)

/-- Two actual horizontal crossings into the same original destination face have the same source position. -/
theorem previous_position_unique {otherPosition : Fin faces.regulars.length} {otherSheet : Fin 2}
    {other : mesh.LocatedFace otherPosition otherSheet}
    (left : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper)
    (right : LiftedSides.HorizontalCrossing request other nextPosition firstUpper lastUpper) : firstPosition =
      otherPosition := by
  have equal := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.HorizontalCrossing.next_anchor
    left).symm.trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.HorizontalCrossing.next_anchor right)
  exact PuncturedFaces.position_eq_of_left_top
    faces firstPosition otherPosition
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) equal)
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) equal)

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual destination anchor is the original source face's lower-right physical corner. -/
theorem next_anchor (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    faces.regulars[nextPosition.val].cell.box.anchor = (⟨faces.regulars[firstPosition.val].cell.box.xUpper,
      faces.regulars[firstPosition.val].cell.box.yLower⟩ : Data.Gaussian.Basic.Canonical) := by
  have equal := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    vertices.coordinate edge.finish) joined.reversed
  change vertices.coordinate joined.crossing.next.located.lifted.quad.first =
    vertices.coordinate first.lifted.quad.second at equal
  rw [joined.crossing.next.located.lifted.coordinates.1, first.lifted.coordinates.2.1] at equal
  exact equal

/-- Two actual vertical crossings from the same original source face have the same destination position. -/
theorem next_position_unique {otherPosition : Fin faces.regulars.length}
    (left : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (right : LiftedSides.VerticalCrossing request first otherPosition firstUpper lastUpper) : nextPosition =
      otherPosition := by
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.VerticalCrossing.next_anchor left
    |>.trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.VerticalCrossing.next_anchor right).symm
  exact PuncturedFaces.position_eq_of_lower
    faces nextPosition otherPosition
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) equal)
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) equal)

/-- Two actual vertical crossings into the same original destination face have the same source position. -/
theorem previous_position_unique {otherPosition : Fin faces.regulars.length} {otherSheet : Fin 2}
    {other : mesh.LocatedFace otherPosition otherSheet}
    (left : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper)
    (right : LiftedSides.VerticalCrossing request other nextPosition firstUpper lastUpper) : firstPosition =
      otherPosition := by
  have equal := (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.VerticalCrossing.next_anchor
    left).symm.trans
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness.VerticalCrossing.next_anchor right)
  exact PuncturedFaces.position_eq_of_right_bottom
    faces firstPosition otherPosition
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) equal)
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) equal)

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness
