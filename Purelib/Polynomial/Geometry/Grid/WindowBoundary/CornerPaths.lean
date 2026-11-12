module

public import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison

/-! # Exact rooted corner paths of one retained grid window

A boundary followed by the left/top route retracts to the bottom/right
route by two literal reverse/retrace cancellations. The window may contain
branch holes; its boundary action is retained rather than declared trivial.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

open Purelib
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid

variable {polynomial : ClearPath.GaussianPolynomial} {ambient box : Box}
    {grid : ClearGrid polynomial ambient} (window : Window grid box)

/-- Follow the SAME cached bottom and right window sides from southwest to northeast. -/
@[expose] def southEast : Walks.Walk grid
    (Data.Gaussian.Components.Basic.point box.xLower box.yLower)
    (Data.Gaussian.Components.Basic.point box.xUpper box.yUpper) :=
  (window.horizontal window.bottom).append (window.vertical window.right)

/-- The actual boundary followed by the left/top route compares to the bottom/right route on every sheet.

Only the literal opposite side traversals are cancelled. The retained
boundary remains first and its actual arriving sheet starts the suffix;
no zero winding, root closure or vanishing edge valuation is assumed.
-/
theorem boundary_prefix_comparison {frames : RootFrames grid}
    (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, FromStates.ContainsVertex grid point → WindingOneLoop polynomial point) :
    RootEdgeBank.ChainComparison edges vertices
      (window.boundary.append window.northEast) window.southEast := by
  let bottom := window.horizontal window.bottom
  let right := window.vertical window.right
  let top := window.horizontal window.top
  let left := window.vertical window.left
  let lower := bottom.append right
  have first : window.boundary.append window.northEast =
      (lower.append top.reverse).append (left.reverse.append (left.append top)) := by
    change (bottom.append (right.append (top.reverse.append left.reverse))).append (left.append top) = _
    dsimp only [lower]
    simp only [Walks.Walk.append_assoc, -eq_self, -iff_self]
    rfl
  have removeLeft := RootEdgeBank.ChainComparison.erase_reverse_retrace
    (edges := edges) (vertices := vertices) reference (lower.append top.reverse) left top
  have removeTop := (RootEdgeBank.ChainComparison.refl (edges := edges) (vertices := vertices) lower).append
    (RootEdgeBank.ChainComparison.reverse_retrace reference top)
  exact (RootEdgeBank.ChainComparison.of_eq first).trans
    (removeLeft.trans ((RootEdgeBank.ChainComparison.of_eq (Walks.Walk.append_assoc lower top.reverse top)).trans
      (removeTop.trans (RootEdgeBank.ChainComparison.of_eq lower.append_nil))))

end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

end
