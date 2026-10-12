module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitRegularIndices
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann.Paths
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

/-! Both starting sheets enumerate both actual local sheets of every retained regular face. -/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (regularIndices)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

-- Preserve the original nominal RootEdgeBank.RootEdgeBank theorem path.
-- The original module suppressed this same legacy duplicate name globally.
/-- Actual root transport is a finite permutation of the two sheet labels.

Injectivity of the retained transport exhausts the two original sheet labels,
so their arbitrary Gaussian readings have the same sum. -/
theorem target_sum_two (edges :
  RootEdgeBank frames)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) (value : Fin 2 →
      Data.Gaussian.Basic.Canonical) :
    value (RootEdgeBank.target edges walk 0) + value (RootEdgeBank.target edges walk 1) = value 0 + value 1 :=
  Data.Gaussian.Norm.Sum.Basic.sum_two_reindex _ (edges.target_injective reference walk) value

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {base : Purelib.Data.Gaussian.Basic.Canonical}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
  (edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitTwoSheetCoverage.BranchCellBank.CircuitPartition

/-- The arriving sheets retained by the compiler are still a complete pair. -/
theorem compile_finish_sum {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (value : Fin 2 → Data.Gaussian.Basic.Canonical) :
    value (partition.compile edges vertices 0).finish + value (partition.compile edges vertices 1).finish = value 0 +
      value 1 := by
  rw [← (partition.compile edges vertices 0).target_eq, ← (partition.compile edges vertices 1).target_eq]
  exact edges.target_sum_two (fun point member => (BranchCellBank.referenceAt bank point member).toLoop) tree.product
    value

/-- Regular-face positions and local sheets are both read from the actual compiled occurrences. -/
theorem compile_twoSheet_sum {tree : RowCircuitOrder.CellCircuits bank.grid base} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (value : Fin faces.regulars.length → Fin 2 → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet) (partition.compile edges
      vertices 0).regulars +
      CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet) (partition.compile
        edges vertices 1).regulars =
      CellBoundary.sumValues (fun index => value index 0 + value index 1) partition.regularIndices := by
  induction partition with
  | nil => exact add_zero _
  | @regular cell member stem location =>
      change (value location.index (RootEdgeBank.target edges stem 0) + 0) + (value location.index (RootEdgeBank.target
        edges stem 1) + 0) =
        (value location.index 0 + value location.index 1) + 0
      simp only [add_zero, -eq_self, -iff_self]
      exact edges.target_sum_two (fun point member => (BranchCellBank.referenceAt bank point member).toLoop) stem (value
        location.index)
  | hole => exact add_zero _
  | append first last ihFirst ihLast =>
      change CellBoundary.sumValues _ ((first.compile edges vertices 0).regulars ++
          (last.compile edges vertices (first.compile edges vertices 0).finish).regulars) +
        CellBoundary.sumValues _ ((first.compile edges vertices 1).regulars ++
          (last.compile edges vertices (first.compile edges vertices 1).finish).regulars) = _
      rw [CellBoundary.sumValues_append, CellBoundary.sumValues_append, CircuitPartition.regularIndices,
        CellBoundary.sumValues_append]
      have final :=
        compile_finish_sum
        edges vertices first (fun sheet =>
        CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet) (last.compile edges
          vertices sheet).regulars)
      calc
        _ = (CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet) (first.compile
          edges vertices 0).regulars +
            CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet) (first.compile
              edges vertices 1).regulars) +
          (CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
              (last.compile edges vertices (first.compile edges vertices 0).finish).regulars +
            CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
              (last.compile edges vertices (first.compile edges vertices 1).finish).regulars) := by ring1
        _ = _ := by rw [ihFirst, final, ihLast]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitTwoSheetCoverage.BranchCellBank.CircuitPartition

end
end
