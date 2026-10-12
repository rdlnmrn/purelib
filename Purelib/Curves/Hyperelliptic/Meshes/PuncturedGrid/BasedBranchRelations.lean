module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Topology.Surface.Sewing.AreaChainTests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-!
# Reference-pair relations with the actual physical branch boundary

The difference of the pairs `(first, reference)` and `(last, reference)`
represents `(first, last)` after adding the clockwise two-lap boundary at
`last`. Both sheets of every stem cancel, using the retained edge maps.
The boundary term is kept for every antisymmetric edge valuation; no
vanishing period, primitive area, or symplectic intersection is assumed.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues (walk_append walk_reverse)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {first last reference : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

namespace Pair

/-- The same branch on both legs reads both actual sheets, in the order determined by the starting sheet. -/
theorem repeated_area (pair : BasedBranchBank.Pair bank last last sheet)
    (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive pair.closed.indexed =
      lifted.edges.twoSheetArea lifted.vertices primitive (bank.rows.get last).reference.walk := by
  rw [pair.indexed, Stokes.edgeListArea_append]
  by_cases zero : sheet = 0
  · rw [zero, BranchCutLifts.otherSheet_zero]
    rfl
  · have different : sheet.val ≠ 0 := fun equal => zero (Fin.ext equal)
    have one : sheet = 1 := by
      have value : sheet.val = 1 := by
        have bound := sheet.isLt
        omega0
      exact Fin.ext value
    rw [one, BranchCutLifts.otherSheet_one]
    exact add_comm _ _

/-- Cancelling the two lifted occurrences of each stem leaves the physical hole with the opposite orientation. This
holds for arbitrary shared vertex primitives, not only for exact or analytically controlled assignments. -/
theorem repeated_hole_area (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (pair : BasedBranchBank.Pair bank hole.index hole.index sheet)
    (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive pair.closed.indexed =
      -Stokes.edgeListArea primitive (hole.liftedBoundary lifted.vertices lifted.edges) := by
  let loop := bank.rows.get hole.index
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk base.bank.grid start finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive
      (fun point member => (BranchCellBank.referenceAt
        base.bank.toBranchCellBank point member).toLoop) walk
  calc
    _ = values.walk loop.reference.walk :=
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations.Pair.repeated_area pair primitive).trans (walks
        _).symm
    _ = values.walk loop.boundary := by
      rw [loop.reference_eq, EdgeValues.walk_append,
        EdgeValues.walk_append,
        EdgeValues.walk_reverse]
      ring1
    _ = -values.walk hole.inwardBoundary := by
      rw [loop.boundary_eq, BranchHole.inwardBoundary,
        EdgeValues.walk_reverse,
        neg_neg, BranchHole.boundary]
      have move (cell : ClearGrid.Cell curve.polynomial
        (Cuts.Ambient curve))
          (member : cell ∈ base.bank.grid.cells) (equal : cell = base.bank.cell hole.index) :
          values.walk (CellBoundary.Cell.boundaryWalk cell member) =
            values.walk (CellBoundary.Cell.boundaryWalk
              (base.bank.cell hole.index) (base.bank.cell_mem hole.index)) := by
        cases equal
        rfl
      exact (move hole.cell hole.member hole.cell_eq).symm
    _ = _ := congrArg Neg.neg ((walks _).trans (hole.liftedBoundary_area _ _ primitive).symm)

/-- Finite primitive tests turn the shared-vertex area identity into the full oriented-chain identity. In particular the
physical term is retained for edge values that are not a globally exact primitive. -/
theorem repeated_hole_value (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (pair : BasedBranchBank.Pair bank hole.index hole.index sheet)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.closed.indexed =
      -SewingRetraction.wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  have zero := AreaChainTests.wordValue_eq
    (first := pair.closed.indexed ++ hole.liftedBoundary lifted.vertices lifted.edges) (last := [])
    (fun primitive => by
      rw [Stokes.edgeListArea_append,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations.Pair.repeated_hole_area hole pair primitive]
      exact neg_add_cancel _) value anti
  rw [SewingRetraction.wordValue_append] at zero
  change _ + _ = 0 at zero
  calc
    _ = (SewingRetraction.wordValue value pair.closed.indexed +
        SewingRetraction.wordValue value (hole.liftedBoundary lifted.vertices lifted.edges)) -
        SewingRetraction.wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by ring1
    _ = _ := by rw [zero, zero_sub]

/-- Read the three already materialized pair words. The shared reference leg cancels literally, and the remaining two
`last` legs form its double branch circuit. No sheet reclassification or new preparation is performed. -/
theorem reference_value (pair : BasedBranchBank.Pair bank first last sheet)
    (firstReference : BasedBranchBank.Pair bank first reference sheet) (lastReference : BasedBranchBank.Pair bank last
      reference sheet)
    (repeated : BasedBranchBank.Pair bank last last sheet) (value : Stokes.OrientedEdge lifted.vertices.count →
      Data.Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue value pair.closed.indexed = SewingRetraction.wordValue value
      firstReference.closed.indexed -
      SewingRetraction.wordValue value lastReference.closed.indexed + SewingRetraction.wordValue value
        repeated.closed.indexed := by
  rw [pair.indexed, firstReference.indexed, lastReference.indexed, repeated.indexed]
  simp only [SewingRetraction.wordValue_append]
  ring1

/-- The actual clockwise physical boundary is exactly the correction to the reference-pair difference, for every
retained branch label. -/
theorem reference_hole_value (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (pair : BasedBranchBank.Pair bank first hole.index sheet)
    (firstReference : BasedBranchBank.Pair bank first reference sheet) (lastReference : BasedBranchBank.Pair bank
      hole.index reference sheet)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.closed.indexed = SewingRetraction.wordValue value
      firstReference.closed.indexed -
      SewingRetraction.wordValue value lastReference.closed.indexed -
      SewingRetraction.wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations.Pair.reference_value pair firstReference
      lastReference (bank.pair hole.index hole.index sheet),
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations.Pair.repeated_hole_value hole _ value anti]
  rfl

end Pair
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations

end
