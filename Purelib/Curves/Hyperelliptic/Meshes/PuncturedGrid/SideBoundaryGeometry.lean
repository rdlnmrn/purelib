module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

@[expose] public section

/-! Transfer a retained source edge's boundary certificate to every point
of its rectangle side. Reversal is handled before the coordinate estimates. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence (OnBoundary)

/-- The two actual oriented endpoints lie on a common side of the band. -/
def SideBoundary (face band : Rational.Box) (side : GridLiftedDualSteps.GridSide) : Prop :=
  let endpoints := RectangleEdge.coordinates face side.kind
  band.Contains endpoints.1 ∧ band.Contains endpoints.2 ∧ PreparedBoundarySegments.SameSide band endpoints.1 endpoints.2

/-- A point belongs to the face box and lies on the specified horizontal or vertical side. -/
def OnSide (face : Rational.Box) (side : GridLiftedDualSteps.GridSide) (point :
  Data.Gaussian.Basic.Canonical) : Prop :=
  face.Contains point ∧ match side with
    | .bottom => point.im = face.yLower
    | .right => point.re = face.xUpper
    | .top => point.im = face.yUpper
    | .left => point.re = face.xLower

/-- A point between two horizontal endpoints contained in a box is also contained in that box. -/
private theorem horizontal_inside {band : Rational.Box} {lower upper height : Fraction.Rational} {point
  : Data.Gaussian.Basic.Canonical}
    (first : band.Contains ⟨lower, height⟩) (last : band.Contains ⟨upper, height⟩)
    (x : lower ≤ point.re ∧ point.re ≤ upper) (y : point.im = height) : band.Contains point :=
  ⟨first.1.trans x.1, x.2.trans last.2.1, y ▸ first.2.2⟩

/-- A point between two vertical endpoints contained in a box is also contained in that box. -/
private theorem vertical_inside {band : Rational.Box} {lower upper horizontal : Fraction.Rational}
  {point : Data.Gaussian.Basic.Canonical}
    (first : band.Contains ⟨horizontal, lower⟩) (last : band.Contains ⟨horizontal, upper⟩)
    (x : point.re = horizontal) (y : lower ≤ point.im ∧ point.im ≤ upper) : band.Contains point :=
  ⟨x ▸ first.1, x ▸ first.2.1, first.2.2.1.trans y.1, y.2.trans last.2.2.2⟩

/-- A proper horizontal side determines the same boundary side for any two points with that height. -/
private theorem horizontal_same {band : Rational.Box} {lower upper height : Fraction.Rational} {first
  last : Data.Gaussian.Basic.Canonical}
    (proper : lower < upper) (side : PreparedBoundarySegments.SameSide band ⟨lower, height⟩ ⟨upper, height⟩)
    (firstEq : first.im = height) (lastEq : last.im = height) : PreparedBoundarySegments.SameSide band first last := by
  rcases side with side | side | side | side
  · exact False.elim ((ne_of_lt proper) (side.1.trans side.2.symm))
  · exact False.elim ((ne_of_lt proper) (side.1.trans side.2.symm))
  · exact Or.inr (Or.inr (Or.inl ⟨firstEq.trans side.1, lastEq.trans side.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨firstEq.trans side.1, lastEq.trans side.2⟩))

/-- A proper vertical side determines the same boundary side for any two points with that horizontal coordinate. -/
private theorem vertical_same {band : Rational.Box} {lower upper horizontal : Fraction.Rational} {first
  last : Data.Gaussian.Basic.Canonical}
    (proper : lower < upper) (side : PreparedBoundarySegments.SameSide band ⟨horizontal, lower⟩ ⟨horizontal, upper⟩)
    (firstEq : first.re = horizontal) (lastEq : last.re = horizontal) : PreparedBoundarySegments.SameSide band first
      last := by
  rcases side with side | side | side | side
  · exact Or.inl ⟨firstEq.trans side.1, lastEq.trans side.2⟩
  · exact Or.inr (Or.inl ⟨firstEq.trans side.1, lastEq.trans side.2⟩)
  · exact False.elim ((ne_of_lt proper) (side.1.trans side.2.symm))
  · exact False.elim ((ne_of_lt proper) (side.1.trans side.2.symm))

namespace SideBoundary
variable {face band : Purelib.Geometry.Rational.Box} {side :
  Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide}

/-- Every point on the retained face side lies in its certified boundary band. -/
theorem contains (boundary : Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary face band side)
  {point : Data.Gaussian.Basic.Canonical} (inside :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.OnSide face side point) :
    band.Contains point := by
  cases side with
  | bottom =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.horizontal_inside boundary.1 boundary.2.1
      ⟨inside.1.1, inside.1.2.1⟩ inside.2
  | right =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.vertical_inside boundary.1 boundary.2.1
      inside.2 inside.1.2.2
  | top =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.horizontal_inside boundary.2.1 boundary.1
      ⟨inside.1.1, inside.1.2.1⟩ inside.2
  | left =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.vertical_inside boundary.2.1 boundary.1
      inside.2 inside.1.2.2

/-- Any two points of a proper certified face side lie on the same original band boundary side. -/
theorem sameSide (boundary : Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary face band side)
  (proper : face.Proper)
    {first last : Data.Gaussian.Basic.Canonical} (firstInside :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.OnSide face side first) (lastInside :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.OnSide face side last) :
    PreparedBoundarySegments.SameSide band first last := by
  cases side with
  | bottom =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.horizontal_same proper.1 boundary.2.2
      firstInside.2 lastInside.2
  | right =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.vertical_same proper.2 boundary.2.2
      firstInside.2 lastInside.2
  | top =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.horizontal_same proper.1 boundary.2.2.reverse
      firstInside.2 lastInside.2
  | left =>
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.vertical_same proper.2 boundary.2.2.reverse
      firstInside.2 lastInside.2

end SideBoundary

namespace BranchCellBank.LiftedMesh.SideOccurrence
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}

/-- The retained source occurrence's boundary certificate gives the actual face-side boundary geometry.

The proof transports the original projected endpoint coordinates and reverses the supplied boundary witness when the
occurrence is backward. -/
theorem boundary (occurrence : LiftedMesh.SideOccurrence mesh) {box : Rational.Box}
    (bounded : SideOccurrence.OnBoundary occurrence box) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry.SideBoundary
      (faces.regulars[occurrence.position.val]'occurrence.position.isLt).cell.box box occurrence.side := by
  rcases occurrence with ⟨position, sheet, side, backward⟩
  let located := mesh.locateFace position sheet
  have coordinates :
      (vertices.coordinate ((LocatedFace.sideSource located side).project mesh.triangulation.faces).start,
        vertices.coordinate ((LocatedFace.sideSource located side).project mesh.triangulation.faces).finish) =
      RectangleEdge.coordinates (faces.regulars[position.val]'position.isLt).cell.box side.kind := by
    rw [LocatedFace.sideSource_project located side]
    exact located.lifted.rectangleCoordinates.edge_coordinates side.kind
  have firstEq := congrArg Prod.fst coordinates
  have lastEq := congrArg Prod.snd coordinates
  cases backward with
  | false =>
      change box.Contains _ ∧ box.Contains _ ∧ PreparedBoundarySegments.SameSide box _ _ at bounded
      exact ⟨firstEq ▸ bounded.1, lastEq ▸ bounded.2.1,
        (congrArg₂ (PreparedBoundarySegments.SameSide box) firstEq lastEq).mp bounded.2.2⟩
  | true =>
      change box.Contains _ ∧ box.Contains _ ∧ PreparedBoundarySegments.SameSide box _ _ at bounded
      exact ⟨firstEq ▸ bounded.2.1, lastEq ▸ bounded.1,
        (congrArg₂ (PreparedBoundarySegments.SameSide box) firstEq lastEq).mp bounded.2.2.reverse⟩

end BranchCellBank.LiftedMesh.SideOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideBoundaryGeometry
