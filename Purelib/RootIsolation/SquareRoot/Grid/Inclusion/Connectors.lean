module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! Original canonical connectors on the enlarged root bank. The two
reversals in the left-then-top route are cancelled as finite lifted words,
not by equating root frames on different grids. -/

namespace Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Connectors

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}
  {original grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} (included :
    Geometry.Grid.Extension.CoordinateInclusion original grid)
  {frames : RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)

include reference

/-- Resplitting a twice-reversed original walk compares to resplitting that walk on every retained sheet. -/
private theorem resplit_reverse_reverse {first last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk
  original first last)
    (firstMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex original first) (lastMember :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex original last) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      walk.reverse.reverse lastMember) (included.resplit walk lastMember) :=
  (included.resplit_reverse edges vertices reference walk.reverse lastMember firstMember).trans
    ((Polynomial.Geometry.Grid.AxisChainCoherence.RootEdgeBank.ChainComparison.reverse reference
      (included.resplit_reverse edges vertices reference walk firstMember lastMember)).trans
      (Polynomial.Geometry.Grid.AxisChainCoherence.RootEdgeBank.ChainComparison.reverse_reverse reference _))

/-- The original reversed canonical connector still follows the original
left/top route after subdivision, for every actual new-grid sheet. -/
theorem Window.resplit_reverse_connect_comparison {box : Box} (window :
  Polynomial.Geometry.Grid.WindowBoundary.Window original box)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex original (Gaussian.Components.Basic.point box.xLower
      box.yLower))
    (last : Polynomial.Geometry.Grid.FromStates.ContainsVertex original (Gaussian.Components.Basic.point box.xUpper
      box.yUpper)) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect original _ _ last first).reverse last)
      (included.resplit window.northEast last) := by
  change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
    (included.resplit
      ((Geometry.Grid.Walks.horizontalWalk original box.xUpper box.xLower box.yUpper last.1 first.1 last.2).append
        (Geometry.Grid.Walks.verticalWalk original box.xLower box.yUpper box.yLower first.1 last.2 first.2)).reverse
          last) _
  let middle : Polynomial.Geometry.Grid.FromStates.ContainsVertex original (Gaussian.Components.Basic.point box.xLower
    box.yUpper) := ⟨first.1, last.2⟩
  rw [Polynomial.Geometry.Grid.AxisChainCoherence.horizontalWalk_decreasing window.x window.top,
    Polynomial.Geometry.Grid.AxisChainCoherence.verticalWalk_decreasing window.y window.left,
    Geometry.Grid.Walks.Walk.reverse_append]
  erw [included.resplit_append _ _ middle last, Polynomial.Geometry.Grid.WindowBoundary.Window.northEast,
    included.resplit_append _ _ middle last]
  exact (SquareRoot.Grid.Inclusion.Connectors.resplit_reverse_reverse included edges vertices reference _ first
    middle).append
    (SquareRoot.Grid.Inclusion.Connectors.resplit_reverse_reverse included edges vertices reference _ middle last)

end Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Connectors
