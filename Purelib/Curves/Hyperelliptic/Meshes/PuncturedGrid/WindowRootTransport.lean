module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Gaussian

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Path.Box

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.Winding

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

@[expose] public section

/-!
# Exact root comparison between the two corner routes of a grid window

The horizontal-then-vertical route and the reversed opposite connector
differ by the window's proved branch parity. The comparison follows actual
shared edge maps; equal endpoint coordinates alone do not identify roots.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.Winding.Walk (append_winding reverse_winding)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-- Transport through the original retained grid walk is injective on the two starting root sheets. -/
theorem target_injective
    (edges : RootEdgeBank frames)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) : Function.Injective
      (RootEdgeBank.target edges walk) := by
  intro first last equal
  exact (edges.target_reverse reference walk first).symm.trans
    ((congrArg (RootEdgeBank.target edges walk.reverse) equal).trans (edges.target_reverse reference walk last))

/-- The winding of the actual reverse-joined loop determines the endpoint root equality. Both paths may use different
subdivisions or grid routes. -/
theorem target_eq_of_winding
    (edges : RootEdgeBank frames)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {start finish : Data.Gaussian.Basic.Canonical} (first last : Walks.Walk grid start finish) (member :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid start)
    (winding : ClearPath.rawWinding first.path = ClearPath.rawWinding last.path) (sheet : Fin 2) :
    RootEdgeBank.target edges first sheet = RootEdgeBank.target edges last sheet := by
  have raw : ClearPath.rawWinding (first.append last.reverse).path = 8 * (0 : Int) := by
    rw [Walk.append_winding,
      Walk.reverse_winding, winding]
    omega
  have returned := RootEdgeBank.target_even edges (reference start member) (first.append last.reverse) member 0 raw
    sheet
  rw [RootEdgeBank.target_append edges] at returned
  apply edges.target_injective reference last.reverse
  rw [returned, edges.target_reverse reference last]

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {box : Purelib.Geometry.Rational.Box}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

/-- The two literal L-shaped connectors traverse this window's boundary with its positive orientation, including every
retained intermediate cut. -/
theorem corner_winding (window :
  Polynomial.Geometry.Grid.WindowBoundary.Window grid box)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid (Components.Basic.point box.xLower box.yLower))
    (last : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid (Components.Basic.point box.xUpper box.yUpper)) :
    ClearPath.rawWinding ((Grid.connect grid _ _ first last).append
      (Grid.connect grid _ _ last first)).path =
      ClearPath.rawWinding window.boundary.path := by
  rw [Walk.append_winding, window.boundary_winding]
  simp only [Grid.connect,
    Walk.castEndpoints_winding,
    Walk.append_winding]
  rw [Winding.horizontalWalk_winding,
    Winding.verticalWalk_winding,
    Winding.horizontalWalk_winding,
    Winding.verticalWalk_winding,
    Winding.Box.Basic.quadrupledBoxWinding_eq]
  change
    ((Sides.horizontalEdge polynomial box.yLower box.xLower box.xUpper).doubledWinding +
      (Sides.verticalEdge polynomial box.xUpper box.yLower box.yUpper).doubledWinding) +
      ((Sides.horizontalEdge polynomial box.yUpper box.xUpper box.xLower).doubledWinding +
        (Sides.verticalEdge polynomial box.xLower box.yUpper box.yLower).doubledWinding) = _
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {window :
    Polynomial.Geometry.Grid.WindowBoundary.Window bank.grid box} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

/-- The parity is computed from the cached physical holes. It acts at the common starting root of the reversed opposite
connector. -/
theorem corner_target
    (count : Window.BranchCount faces window)
    (edges : RootEdgeBank frames)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid (Components.Basic.point box.xLower
      box.yLower))
    (last : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid (Components.Basic.point box.xUpper
      box.yUpper)) (sheet : Fin 2) :
    RootEdgeBank.target edges (Grid.connect bank.grid _ _ first last) sheet =
      RootEdgeBank.target edges (Grid.connect bank.grid _ _ last first).reverse
        (count.action sheet) := by
  let reference := fun point member =>
    (BranchCellBank.referenceAt bank point member).toLoop
  have loop := Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.target_eq_of_winding edges reference
    ((Grid.connect bank.grid _ _ first last).append
      (Grid.connect bank.grid _ _ last first)) window.boundary first
    (corner_winding window first last) sheet
  rw [RootEdgeBank.target_append edges, count.target] at loop
  have compared := congrArg (RootEdgeBank.target edges
    (Grid.connect bank.grid _ _ last first).reverse) loop
  rw [edges.target_reverse reference
    (Grid.connect bank.grid _ _ last first)] at compared
  exact compared

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

end
