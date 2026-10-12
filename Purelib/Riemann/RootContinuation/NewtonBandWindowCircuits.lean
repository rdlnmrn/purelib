module
import Purelib.Data.List.Nodup
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells

public section

/-! The Newton-band window retains precisely its own shrunken
hole circuit. Its polygon remains explicit in the fine compiler identity. -/
namespace Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
  (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index
    branches}
  {current : LiftedPuncturedGrid grid.punctured}

open Purelib.Curves in
/-- Prepare the ordered branch circuits in the retained Newton annulus window on the chosen sheet.

The window, edge bank and vertex bank all belong to the same refined grid. -/
@[expose] def fineOrder (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin 2) :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window.prepareBranches
    grid.faces region.window current.edges current.vertices sheet

open Purelib.Curves in
open Purelib.Polynomial in
/-- Compile the retained Newton-window partition against the grid's identity inclusion.

The result retains its word, ordered hole circuit, connectors and regular area terms with the original sheet and anchor.
-/
@[expose] def fineCompiler (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin 2)
  :
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
      (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid region)
      (fineOrder (current := current) region sheet).partition sheet :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit _
    current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop) _
    (fineOrder (current := current) region sheet).partition sheet

/-- A duplicate-free list containing an item and no other item is its singleton. -/
private theorem singleton_of_unique {Item : Type} (entries : List Item) (index : Item)
    (unique : entries.Nodup) (present : index ∈ entries)
    (only : ∀ entry ∈ entries, entry = index) : entries = [index] := by
  cases entries with
  | nil => exact (List.not_mem_nil present).elim
  | cons head tail =>
      have headEq := only head List.mem_cons_self
      have empty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            have nextEq := only next (List.mem_cons_of_mem _ List.mem_cons_self)
            exact ((List.pairwise_cons.mp unique).1 next List.mem_cons_self (headEq.trans nextEq.symm)).elim
      rw [headEq, empty]

open Purelib.Curves in
open Purelib.Geometry in
/-- The Newton-window compiler partition retains exactly the specified branch label once.

The shrunken cell is present, and the original cell separation excludes every other branch label, preserving
multiplicity in the partition. -/
theorem fine_kept_labels (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin 2) :
    (fineOrder (current := current) region sheet).partition.labels = [index] := by
  let order := fineOrder (current := current) region sheet
  have present : index ∈ order.labels := order.selected index |>.mpr (grid.cell_refines_band index)
  have only : ∀ entry ∈ order.labels, entry = index := by
    intro entry member
    have inside := ((order.selected entry).mp member).trans (Geometry.Rational.Box.Refinement.StrictInterior.refines
      (grid.bands.strict_original index))
    have retained := (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.shrunk.cell_strict entry))
    by_cases same : entry = index
    · exact same
    · exact ((original.cells_separated entry index same).points_ne
        (retained.contains (grid.punctured.bank.cell entry).box.contains_anchor)
        (inside.contains (grid.punctured.bank.cell entry).box.contains_anchor) rfl).elim
  exact order.labels_eq.symm.trans (singleton_of_unique order.labels index order.unique present only)

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Polynomial in
/-- The literal annular boundary area equals the compiled word area plus all retained area terms.

The comparison uses an antisymmetric edge reading and the exact window order, identity resplitting, connectors and hole
polygon. -/
theorem fineCompiler_area (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin 2)
    (value : OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    current.edges.chainArea current.vertices value
      region.boundary sheet =
      Mesh.RetracingWords.wordArea value (fineCompiler (current := current) region sheet).word +
        Mesh.RetracingWords.AreaTerm.total value (fineCompiler (current := current) region sheet).areaTerms := by
  let order := fineOrder (current := current) region sheet
  let compiled := fineCompiler (current := current) region sheet
  let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
    grid.punctured.bank.toBranchCellBank point member).toLoop
  have ordered := order.ordered.comparison.areas value anti sheet
  rw [order.ordered.product_eq] at ordered
  have self := Polynomial.Geometry.Grid.ClearGrid.self_resplit_comparison
    current.edges current.vertices reference order.ordered.tree.product
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid region)
  exact ordered.symm.trans ((self.areas value anti sheet).symm.trans (compiled.areas value anti))

end Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
