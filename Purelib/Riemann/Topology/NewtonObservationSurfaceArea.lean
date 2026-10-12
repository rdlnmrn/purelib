module
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Content

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleOverlap
public import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Observation area retained in the complete regular surface

Clipped area telescopes over the original full grid. Every removed branch
face lies above the protected observation region and contributes zero.
Within each regular face the complete rectangular subdivision preserves
clipped area, and its cached placements identify that area with exactly the
pieces inside the selected observation box.
-/

namespace Purelib.Riemann.Topology.NewtonObservationSurfaceArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleOverlap (content content_refines content_contains
  content_separated partition_sum grid_sum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (FaceSplit BranchHole)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- The retained regular and hole face sums account exactly for the original full cell list. -/
private theorem split_sum (value : Rational.Box → Rat.Fraction.Rational) {bank :
  Hyperelliptic.Branches.BranchCellBank curve branches higher} :
    {cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))} → (split
      : FaceSplit bank cells) →
      FiniteSum.Rational.Squares.coordinateSum (split.regulars.map fun face => value face.cell.box) +
        FiniteSum.Rational.Squares.coordinateSum (split.holes.map fun hole => value hole.cell.box) =
          FiniteSum.Rational.Squares.coordinateSum (cells.map fun cell => value cell.box)
  | _, .nil => by change (0 : Rat.Fraction.Rational) + 0 = 0; ring1
  | _, .regular face tail => by
      change (value face.cell.box + _) + _ = value face.cell.box + _
      rw [← split_sum value tail]
      dsimp only [FaceSplit.regulars, FaceSplit.holes]
      ring1
  | _, .hole hole tail => by
      change _ + (value hole.cell.box + _) = value hole.cell.box + _
      rw [← split_sum value tail]
      dsimp only [FaceSplit.regulars, FaceSplit.holes]
      ring1

section
open Purelib.Algebra
open Purelib.Data
/-- A finite list of pointwise zero rational values has zero coordinate sum. -/
private theorem sum_zero {Alpha : Type} (items : List Alpha) (value : Alpha → Rat.Fraction.Rational)
    (zero : ∀ item, value item = 0) : FiniteSum.Rational.Squares.coordinateSum (items.map value) = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    change value head + FiniteSum.Rational.Squares.coordinateSum (tail.map value) = 0; rw [zero head, ih, add_zero]

/-- The mapped coordinate sum equals the finite sum over the original retained list indices. -/
private theorem sum_map_index {Alpha : Type} (items : List Alpha) (value : Alpha → Rat.Fraction.Rational) :
    FiniteSum.Rational.Squares.coordinateSum (items.map value) = FiniteSum.Fin.sumFin (fun index : Fin items.length =>
      value (items[index.val]'index.isLt)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change value first + FiniteSum.Rational.Squares.coordinateSum (rest.map value) = value first +
        FiniteSum.Fin.sumFin (fun index : Fin rest.length => value (rest[index.val]'index.isLt))
      exact congrArg (fun total => value first + total) ih

end

open Purelib.Curves in
open Purelib.Geometry in
/-- Every removed branch face contributes zero clipped area to a protected observation box.

The original branch-state separation and retained Newton-band refinements place the hole above the observation region.
-/
theorem hole_content_zero (observations : ProtectedObservations original) (grid : NewtonGrid preparation target radius)
    (site : Fin genus) (hole : BranchHole grid.punctured.bank.toBranchCellBank) :
    Rectangle.Partition.PreparedRectangleOverlap.content (observations.energy.box site) hole.cell.box = 0 := by
  have band : (grid.bands.box hole.index).Refines (Hyperelliptic.Branches.BranchCellWinding.state original
    hole.index).box :=
    Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.bands.entries.get
      hole.index).selection.sample.output.strictCurrent
  have below := ((observations.energy.box_refines_region site).2.2.2.trans_lt
    (observations.region.below_state hole.index)).trans_le
      (band.2.2.1.trans (grid.hole_refines_band hole).2.2.1)
  exact Rectangle.Partition.PreparedRectangleOverlap.content_separated (Or.inr (Or.inr (Or.inr below.le)))

open Purelib.Algebra in
open Purelib.Geometry in
/-- The actual regular faces retain the entire protected observation area.

The original full-grid clipped-area sum telescopes, and every omitted branch face has zero contribution. -/
theorem regular_content_eq_area (observations : ProtectedObservations original) (grid : NewtonGrid preparation target
  radius)
    (site : Fin genus) :
    FiniteSum.Fin.sumFin (fun position : Fin grid.faces.regulars.length =>
      Rectangle.Partition.PreparedRectangleOverlap.content (observations.energy.box site)
        (grid.faces.regulars[position.val]'position.isLt).cell.box) = observations.energy.area := by
  have split := split_sum (Rectangle.Partition.PreparedRectangleOverlap.content (observations.energy.box site))
    grid.faces.split
  rw [← grid.faces.regulars_eq, ← grid.faces.holes_eq] at split
  rw [sum_zero grid.faces.holes _ ((hole_content_zero observations) grid site), add_zero] at split
  rw [sum_map_index grid.faces.regulars (fun face => Rectangle.Partition.PreparedRectangleOverlap.content
    (observations.energy.box site) face.cell.box)] at split
  exact split.trans ((Rectangle.Partition.PreparedRectangleOverlap.grid_sum (observations.energy.box site)
    grid.shrunk.prepared.frame).trans
    ((Rectangle.Partition.PreparedRectangleOverlap.content_contains
        (Geometry.Rational.Box.Refinement.StrictInterior.refines
      (observations.box_interior site))).trans (observations.energy.boxContent_eq_area site)))

namespace SurfacePartition

variable {position : Fin grid.faces.regulars.length}

open Purelib.Data in
open Purelib.Geometry in
/-- Read an actual piece's observation area from its cached inside-or-outside placement. -/
def observationArea (partition : SurfacePartition observations grid position) (site : Fin genus)
    (piece : Fin partition.cuts.boxes.length) : Rat.Fraction.Rational :=
  match (partition.placements.get piece).get site with
  | .inside _ => Rational.Box.Content.boxContent (partition.cuts.boxes[piece.val]'piece.isLt)
  | .outside _ => 0

open Purelib.Geometry in
/-- The retained placement reading equals the exact clipped area of the original piece box. -/
theorem observationArea_eq_content (partition : SurfacePartition observations grid position) (site : Fin genus)
    (piece : Fin partition.cuts.boxes.length) :
    (observationArea partition) site piece = Rectangle.Partition.PreparedRectangleOverlap.content
      (observations.energy.box site) (partition.cuts.boxes[piece.val]'piece.isLt) := by
  unfold observationArea
  cases (partition.placements.get piece).get site with
  | inside contained => exact (Rectangle.Partition.PreparedRectangleOverlap.content_refines contained).symm
  | outside separated => exact (Rectangle.Partition.PreparedRectangleOverlap.content_separated separated).symm

open Purelib.Algebra in
open Purelib.Geometry in
/-- Summing the actual piece observations preserves the original regular face's clipped area. -/
theorem observationArea_sum (partition : SurfacePartition observations grid position) (site : Fin genus) :
    FiniteSum.Fin.sumFin ((observationArea partition) site) =
      Rectangle.Partition.PreparedRectangleOverlap.content (observations.energy.box site)
        (grid.faces.regulars[position.val]'position.isLt).cell.box := by
  rw [FiniteSum.Fin.sumFin_congr ((observationArea_eq_content partition) site), ←
    Rectangle.Partition.PreparedBoxPartitions.sumCells_eq_sumFin]
  exact Rectangle.Partition.PreparedRectangleOverlap.partition_sum _ partition.cuts

end SurfacePartition

open Purelib.Algebra in
/-- The complete retained surface has exactly the original observation area at every site.

Any certified per-face rectangular partitions preserve the clipped-area sum through their cached placement readbacks. -/
theorem surface_observation_area (partitions : SurfacePartitions observations grid) (site : Fin genus) :
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (SurfacePartition.observationArea (partitions.get
      position) site)) = observations.energy.area := by
  rw [FiniteSum.Fin.sumFin_congr (fun position => SurfacePartition.observationArea_sum (partitions.get position) site)]
  exact (regular_content_eq_area observations) grid site

end Purelib.Riemann.Topology.NewtonObservationSurfaceArea
