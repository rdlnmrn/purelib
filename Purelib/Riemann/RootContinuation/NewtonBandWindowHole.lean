module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit

public section

/-! Read back the actual unique fine hole circuit inside an Newton-band
window, retaining its stem and the shrunken hole's exact identity. -/
namespace Purelib.Riemann.RootContinuation.NewtonBandWindowHole

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
  (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit (SingleHole singleHole)
open Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
  (fineOrder fineCompiler)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index
    branches}
  {current : LiftedPuncturedGrid grid.punctured}

open Purelib.Riemann in
open Purelib.Curves in
/-- Retain the Newton-window partition's unique fine hole and original connector.

The partition is independent of initial sheet; its singleton label proof fixes the exact shrunken hole identity. -/
@[expose] def fineHole (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.SingleHole (fineOrder (current := current) region 0).partition
      index :=
  Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.singleHole index (fineOrder (current := current) region
    0).partition
    (RootContinuation.NewtonBandWindowCircuits.fine_kept_labels region 0)

open Purelib.Curves in
/-- The retained unique fine hole is the requested grid bank's cell for the original branch label. -/
theorem fineHole_cell (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) :
    (fineHole (current := current) region).hole.cell = grid.punctured.bank.cell index :=
  (fineHole (current := current) region).hole.cell_eq.trans
    (congrArg grid.punctured.bank.cell (fineHole (current := current) region).hole_index)

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Polynomial in
/-- The compiler word reads as the based circuit around the exact retained shrunken hole.

The comparison retains the compiler's original stem and requested initial sheet, and applies to antisymmetric edge
readings. -/
theorem fineCompiler_hole_area (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (sheet : Fin
  2)
    (value : OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Mesh.RetracingWords.wordArea value (fineCompiler (current := current) region sheet).word =
      current.edges.chainArea current.vertices value
        ((fineHole (current := current) region).stem.based
          (Geometry.Grid.CellBoundary.Cell.boundaryWalk
            (fineHole (current := current) region).hole.cell
            (fineHole (current := current) region).hole.member)) sheet := by
  let order := fineOrder (current := current) region sheet
  let compiled := fineCompiler (current := current) region sheet
  let found := fineHole (current := current) region
  let member := (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid region)
  have words := congrArg (Mesh.RetracingWords.wordArea value) compiled.word_eq
  have self := Polynomial.Geometry.Grid.ClearGrid.self_resplit_comparison current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop) order.partition.kept.product member
  have kept : order.partition.kept.product = found.stem.based (Geometry.Grid.CellBoundary.Cell.boundaryWalk
    found.hole.cell found.hole.member) :=
    found.product_eq
  exact words.trans ((self.areas value anti sheet).trans
    (congrArg (fun walk => current.edges.chainArea current.vertices value walk sheet) kept))

end Purelib.Riemann.RootContinuation.NewtonBandWindowHole
