module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
public import Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Geometry.Grid.FromStates

@[expose] public section

/-!
# Genuine requested shrinking of the branch holes

The new grid keeps every old coordinate and the same enclosing frame, but
its removed branch cells lie strictly inside the old cells and satisfy the
requested squared-diagonal bound. Classification and mesh construction use
these actual new cells. This is geometric shrinking, not yet an estimate of
the differential integrals on their boundaries or of the exterior term.
-/

namespace Purelib.Riemann.Meshes.ShrinkingPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank FramedBranchCellBank)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (BranchCellRow)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Location (BranchBudget)
open Purelib.RootIsolation.SquareRoot.Grid.Branch.Neighborhoods (BranchNeighborhoods)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (FramedExtension)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding (state state_strict_cell)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace BranchCellBank

open Purelib in
open Purelib.Data.Rat in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A framed refinement of the original branch-cell bank with strictly interior holes and a retained radius bound.

The new grid includes the original coordinates, while every branch index keeps its original cell owner and exact
squared-diameter estimate. -/
structure Shrunk (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) (radius :
  Fraction.Rational) where
  /-- The retained framed branch-cell bank refining the original grid. -/ prepared :
    Curves.Hyperelliptic.Branches.FramedBranchCellBank curve branches higher
  /-- The original grid coordinates are included in the exact prepared grid. -/ included :
    Geometry.Grid.Extension.CoordinateInclusion original.grid prepared.grid
  /-- Every prepared branch cell lies strictly inside its original indexed cell. -/ cell_strict : ∀ index,
    (prepared.toBranchCellBank.cell index).box.StrictInterior (original.cell index).box
  /-- Each retained indexed branch cell satisfies the requested squared-radius bound. -/ diagonal : ∀ index,
    (prepared.toBranchCellBank.cell index).box.diagonalSq ≤ radius ^ 2

constructive_injectivity Shrunk

namespace Shrunk

variable {original : BranchCellBank curve branches higher} {radius :
  Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Retain the original branch row together with its located refined state, cell membership and composed refinements. -/
public def row (sample : SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods (BranchCellWinding.state original)
  radius)
    {extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension original.grid sample.listed}
    (locations : sample.Locations extension) (index : BranchIsolation.Data.Index branches) :
      BranchCellBank.BranchCellRow extension.grid :=
  let found := locations.entries.get index
  ⟨(original.rows index).original,
    ⟨found.state, (found.refines.trans (sample.refines index)).trans (original.rows index).location.refines,
      found.cell, found.member, found.strict, (locations.cell_refines index).trans (original.rows
        index).location.refines⟩⟩

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Construct the shrunk original bank from retained branch neighborhoods and their exact locations in a framed
extension.

The cached rows preserve original branch-state ownership. Exact coordinate inclusion, strict interior containment and
radius bounds come from the same retained locations. -/
def ofLocations (sample : SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods (BranchCellWinding.state original)
  radius)
    (extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension original.grid sample.listed) (locations :
      sample.Locations extension) :
    Shrunk original radius :=
  let rows := Vector.Basic.vectorOfFn (row sample locations)
  let prepared : Curves.Hyperelliptic.Branches.FramedBranchCellBank curve branches higher :=
    { grid := extension.grid
      baseIncluded := original.baseIncluded.trans extension.originalIncluded
      budget := locations.budget
      rows := rows
      original_eq := fun index => by rw [Vector.Basic.vectorOfFn_apply]; exact original.original_eq index
      frame := extension.frame
      holesInterior := fun index => by
        change ((rows index).location.cell).box.StrictInterior (Cuts.Ambient curve)
        rw [Vector.Basic.vectorOfFn_apply]
        exact Geometry.Rational.Box.Refinement.StrictInterior.of_refines
          (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines (BranchCellWinding.state_strict_cell
              original index)
            (original.cell index).box_refines)
          (locations.cell_refines index) }
  { prepared := prepared
    included := extension.originalIncluded
    cell_strict := fun index => by
      change ((rows index).location.cell).box.StrictInterior (original.cell index).box
      rw [Vector.Basic.vectorOfFn_apply]
      exact Geometry.Rational.Box.Refinement.StrictInterior.of_refines (BranchCellWinding.state_strict_cell original
          index)
        (locations.cell_refines index)
    diagonal := fun index => by
      change ((rows index).location.cell).box.diagonalSq ≤ radius ^ 2
      rw [Vector.Basic.vectorOfFn_apply]
      exact locations.cell_diagonal index }

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The constructed original branch cell is exactly the cell stored in its retained location entry. -/
theorem ofLocations_cell (sample : SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods (BranchCellWinding.state
  original) radius)
    (extension : Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension original.grid sample.listed) (locations :
      sample.Locations extension)
    (index : BranchIsolation.Data.Index branches) :
    ((ofLocations sample extension locations).prepared.toBranchCellBank.cell index) = (locations.entries.get index).cell
      := by
  change ((Vector.Basic.vectorOfFn (row sample locations) index).location).cell = _
  rw [Vector.Basic.vectorOfFn_apply]
  rfl

/-- Form the exact punctured-face partition of the retained shrunk framed bank. -/
def punctured (sample : Shrunk original radius) : FramedPuncturedGrid curve branches higher :=
  FramedPuncturedGrid.ofBank sample.prepared

/-- Every retained shrunk hole has squared diameter at most the original requested radius squared. -/
theorem hole_diagonal (sample : Shrunk original radius) (hole : BranchHole sample.punctured.bank.toBranchCellBank) :
    hole.cell.box.diagonalSq ≤ radius ^ 2 := by
  rw [hole.cell_eq]
  exact sample.diagonal hole.index

/-- Every retained shrunk hole lies strictly inside its corresponding original branch cell. -/
theorem hole_strict_original (sample : Shrunk original radius) (hole : BranchHole
  sample.punctured.bank.toBranchCellBank) :
    hole.cell.box.StrictInterior (original.cell hole.index).box := by
  rw [hole.cell_eq]
  exact sample.cell_strict hole.index

end Shrunk

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial.Clearance.Box in
set_option genInjectivity false in
/-- The original ambient polynomial boundary clearance retained before branch-cell shrinking requests. -/
structure ShrinkingPreparation (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) where
  /-- The retained original polynomial clearance on the ambient box boundary. -/ clearance :
    Boundary.Basic.BoundaryClearance curve.polynomial (Cuts.Ambient curve)

constructive_injectivity ShrinkingPreparation

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial.Clearance.Box in
/-- Cache the original curve's ambient boundary clearance for subsequent shrinking requests. -/
def prepareShrinking (original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher) :
  ShrinkingPreparation original :=
  ⟨Boundary.RootRadius.largeSquare_boundaryClearance (BranchIsolation.degreePositive curve)⟩

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Shrink the original branch cells to the positive requested radius using retained boundary clearance.

Original branch tracks produce finite neighborhoods; their listed coordinates extend the original grid, and exact
locations build the retained framed bank. -/
def ShrinkingPreparation.request {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
    (preparation : ShrinkingPreparation original) (radius : Fraction.Rational) (positive : 0 < radius) : Shrunk original
      radius :=
  let tracks := fun index => branches.track higher index
  let sample := SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods.build (BranchCellWinding.state original) tracks
    radius positive
  let extension := Polynomial.Geometry.Grid.FramedClearGrid.FramedExtension.build original.grid preparation.clearance
    sample.listed
  let locations := SquareRoot.Grid.Branch.Neighborhoods.BranchNeighborhoods.Locations.build sample extension
    (SquareRoot.Grid.Branch.Location.BranchBudget.ofGrid extension.grid)
    (BranchIsolation.degreePositive curve) tracks
  Shrunk.ofLocations sample extension locations

end BranchCellBank
end Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
