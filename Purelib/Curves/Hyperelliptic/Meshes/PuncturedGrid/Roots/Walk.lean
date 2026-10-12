module
public import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
public import Purelib.Riemann.Meshes.PuncturedGridBoundary
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

section
@[expose] public section

/-!
# Actual lifted walks from the shared edge bank

Walk queries compose stored two-sheet maps.  Their proof traces use the same
edge preparations and proved same-root handoffs.  The trace winding is the
winding of the original grid walk, so regular face boundaries act as the
identity and branch-hole boundaries act as the swap on these shared maps.
-/

section Purelib.Riemann.RootContinuation.GridRootWalks.RootEdgeBank

open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Grid polynomial
  ambient}
  {frames : Purelib.RootIsolation.SquareRoot.Grid.RootFrames grid}
end Purelib.Riemann.RootContinuation.GridRootWalks.RootEdgeBank

namespace Purelib.Riemann.RootContinuation.GridRootWalks
namespace BranchCellBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace RegularFace

/-- Each regular face closes using the four identifications from the same shared edge bank, not four independently
supplied face-level comparisons. -/
theorem
  sharedTransport_identity
  (face : RegularFace bank) (edges : RootEdgeBank frames) (sheet : Fin 2) :
    RootEdgeBank.target edges face.boundary sheet = sheet :=
  RootEdgeBank.target_even edges (BranchCellBank.referenceAt bank _ (Cell.anchor_mem face.cell face.member)).toLoop
    face.boundary
    (Cell.anchor_mem face.cell face.member) 0 face.boundary_winding sheet

end RegularFace

namespace BranchHole

/-- The boundary of a removed branch cell is not a closed lifted face: its shared edge maps exchange the two retained
sheets. -/
theorem
  sharedTransport_swap
  (hole : BranchHole bank) (edges : RootEdgeBank frames) (sheet : Fin 2) :
    RootEdgeBank.target edges hole.inwardBoundary sheet = BranchCutLifts.otherSheet sheet :=
  RootEdgeBank.target_odd edges hole.inwardBoundary (Cell.anchor_mem hole.cell hole.member) (-1)
    (hole.inwardBoundary_winding.trans (by decide)) sheet

end BranchHole

end BranchCellBank
end Purelib.Riemann.RootContinuation.GridRootWalks

end
