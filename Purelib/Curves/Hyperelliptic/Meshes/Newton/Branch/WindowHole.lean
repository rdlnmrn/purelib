module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Read back the actual unique fine hole circuit inside an original
branch window, retaining its stem and the shrunken hole's exact identity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowHole

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
  (NewtonPreparation NewtonGrid)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

/-- The partition is independent of the initial sheet. Read its unique
hole and original connector once, with their ownership certificates. -/
@[expose] def fineHole (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) :
    Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.SingleHole
      (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region 0).partition index :=
  Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.singleHole index
    (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region 0).partition
    (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fine_kept_labels region 0)

/-- The unique original fine-window hole retains exactly the indexed shrunken branch cell. -/
theorem fineHole_cell (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) :
    (Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region).hole.cell =
      grid.punctured.bank.cell index :=
  (Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region).hole.cell_eq.trans
    (congrArg grid.punctured.bank.cell (Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current)
      region).hole_index)

/-- The remaining polygon is the based circuit around the actual shrunken
hole, on the compiler's actual stem and the requested initial sheet. -/
theorem fineCompiler_hole_area (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index)
  (sheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Topology.Mesh.RetracingWords.wordArea value (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineCompiler (current
      := current) region sheet).word =
      current.edges.chainArea current.vertices value
        ((Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region).stem.based
          (Geometry.Grid.CellBoundary.Cell.boundaryWalk
            (Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region).hole.cell
            (Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region).hole.member)) sheet :=
              by
  let order := Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet
  let compiled := Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineCompiler (current := current) region sheet
  let found := Hyperelliptic.Meshes.Newton.Branch.WindowHole.fineHole (current := current) region
  let member := grid.shrunk.included.vertex (Geometry.Grid.ClearGrid.Cell.anchor_mem (original.cell index)
    (original.cell_mem index))
  have words := congrArg (Topology.Mesh.RetracingWords.wordArea value) compiled.word_eq
  have self := Polynomial.Geometry.Grid.ClearGrid.self_resplit_comparison current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop) order.partition.kept.product member
  have kept : order.partition.kept.product = found.stem.based (Geometry.Grid.CellBoundary.Cell.boundaryWalk
    found.hole.cell found.hole.member) :=
    found.product_eq
  exact words.trans ((self.areas value anti sheet).trans
    (congrArg (fun walk => current.edges.chainArea current.vertices value walk sheet) kept))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowHole
