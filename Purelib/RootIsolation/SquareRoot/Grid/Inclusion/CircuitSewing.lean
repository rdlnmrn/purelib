module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

open Purelib.RootIsolation.SquareRoot.Grid

public section

/-! Subdivision preserves the actual rectangular sewing and based circuit
products used by the ordered exterior decomposition. All comparisons retain
the arriving root sheet and finite indexed words up to retracing. -/

section
open Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib
open Purelib.RootIsolation

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}
  {original grid : Geometry.Grid.ClearGrid polynomial ambient} (included :
    CoordinateInclusion original grid)
  {frames : SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : LiftedVertices.VertexBank grid)
  (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)

namespace Purelib.Polynomial.Geometry.Grid.Extension

/-- An original horizontal walk with equal endpoints is the empty walk at that coordinate. -/
private theorem stationary_horizontal (x y : Data.Rat.Fraction.Rational) (member :
  FromStates.ContainsVertex grid (Gaussian.Components.Basic.point x y)) :
    Walks.horizontalWalk grid x x y member.1 member.1 member.2 = .nil
      (Gaussian.Components.Basic.point x y) := by
  rw [AxisChainCoherence.horizontalWalk_increasing (.nil x) (AxisWalks.lookup y
    grid.horizontal member.2)]
  rcases AxisWalks.lookup y grid.horizontal member.2 with ⟨line, onGrid, equal⟩
  cases equal
  rfl

/-- An original vertical walk with equal endpoints is the empty walk at that coordinate. -/
private theorem stationary_vertical (x y : Data.Rat.Fraction.Rational) (member :
  FromStates.ContainsVertex grid (Gaussian.Components.Basic.point x y)) :
    Walks.verticalWalk grid x y y member.1 member.2 member.2 = .nil
      (Gaussian.Components.Basic.point x y) := by
  rw [AxisChainCoherence.verticalWalk_increasing (.nil y) (AxisWalks.lookup x
    grid.vertical member.1)]
  rcases AxisWalks.lookup x grid.vertical member.1 with ⟨line, onGrid, equal⟩
  cases equal
  rfl

/-- Clear segments with the same oriented endpoints produce the same retained grid split. -/
private theorem splitSegment_equal {pathAmbient : Box} {first last : Gaussian.Basic.Canonical}
    (a b : ClearPath.ClearSegment polynomial pathAmbient first last)
    (firstMember : FromStates.ContainsVertex grid first) (lastMember :
      FromStates.ContainsVertex grid last) :
    Walks.splitSegment grid a firstMember lastMember = Walks.splitSegment grid b firstMember
      lastMember := by
  cases a <;> cases b
  · rfl
  · change Walks.horizontalWalk grid _ _ _ _ _ _ = Walks.verticalWalk grid _ _ _ _ _ _
    rw [stationary_horizontal _ _ firstMember, stationary_vertical _ _
      firstMember]
  · change Walks.verticalWalk grid _ _ _ _ _ _ = Walks.horizontalWalk grid _ _ _ _ _ _
    rw [stationary_horizontal _ _ firstMember, stationary_vertical _ _
      firstMember]
  · rfl

end Purelib.Polynomial.Geometry.Grid.Extension

namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

/-- Original adjacent-edge payloads with the same oriented endpoints
subdivide to the same retained word, including stationary-axis cases. -/
theorem resplit_edge {first last : Gaussian.Basic.Canonical} (a b : Walks.Edge original first last) :
    included.resplit (.cons a (.nil last)) a.vertices.2 =
      included.resplit (.cons b (.nil last)) b.vertices.2 := by
  change (Walks.splitSegment grid a.segment (included.vertex a.vertices.1) (included.vertex
    a.vertices.2)).append (.nil last) =
    (Walks.splitSegment grid b.segment (included.vertex b.vertices.1) (included.vertex
      b.vertices.2)).append (.nil last)
  rw [splitSegment_equal a.segment b.segment]

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

include reference

namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

section Anchored

omit reference

variable {anchor : Gaussian.Basic.Canonical}
variable (anchoredReference : Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial anchor)
variable (anchorMember : FromStates.ContainsVertex grid anchor)

include anchoredReference anchorMember

/-- Resplitting a retained rectangular boundary compares to the rectangle of its four resplit original sides. -/
theorem resplit_rectangle_anchored {a b c d : Gaussian.Basic.Canonical}
    (bottom : Walks.Walk original a b) (right : Walks.Walk original b d)
    (top : Walks.Walk original c d) (left : Walks.Walk original a c)
    (aMember : FromStates.ContainsVertex original a) (bMember :
      FromStates.ContainsVertex original b)
    (cMember : FromStates.ContainsVertex original c) (dMember :
      FromStates.ContainsVertex original d) :
    RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Walks.Walk.rectangle bottom right top left) aMember)
      (Walks.Walk.rectangle (included.resplit bottom bMember) (included.resplit right dMember)
        (included.resplit top dMember) (included.resplit left cMember)) := by
  rw [Walks.Walk.rectangle, included.resplit_append _ _ bMember aMember,
    included.resplit_append _ _ dMember aMember, included.resplit_append _ _ cMember aMember]
  exact (RootEdgeBank.ChainComparison.refl _).append
    ((RootEdgeBank.ChainComparison.refl _).append
    ((included.resplit_reverse_anchored edges vertices anchoredReference anchorMember top cMember dMember).append
      (included.resplit_reverse_anchored edges vertices anchoredReference anchorMember left aMember cMember)))

end Anchored

/-- Resplitting a retained rectangular boundary compares to the rectangle of its four resplit original sides. -/
theorem resplit_rectangle {a b c d : Gaussian.Basic.Canonical}
    (bottom : Walks.Walk original a b) (right : Walks.Walk original b d)
    (top : Walks.Walk original c d) (left : Walks.Walk original a c)
    (aMember : FromStates.ContainsVertex original a) (bMember :
      FromStates.ContainsVertex original b)
    (cMember : FromStates.ContainsVertex original c) (dMember :
      FromStates.ContainsVertex original d) :
    RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Walks.Walk.rectangle bottom right top left) aMember)
      (Walks.Walk.rectangle (included.resplit bottom bMember) (included.resplit right dMember)
        (included.resplit top dMember) (included.resplit left cMember)) :=
  included.resplit_rectangle_anchored edges vertices
    (reference a (included.vertex aMember)) (included.vertex aMember)
    bottom right top left aMember bMember cMember dMember

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

namespace Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits

/-- Distribute the subdivided connector through the original circuit tree.
Its intermediate out-and-back words cancel in their actual sheet order. -/
theorem resplit_based_product {first last : Gaussian.Basic.Canonical}
    (stem : Walks.Walk original first last) (tree : CellCircuits original
      last)
    (firstMember : FromStates.ContainsVertex original first) (lastMember :
      FromStates.ContainsVertex original last) :
    RootEdgeBank.ChainComparison edges vertices (included.resplit (tree.based
      stem).product firstMember)
      ((included.resplit stem lastMember).based (included.resplit tree.product lastMember)) := by
  induction tree with
  | nil =>
      change RootEdgeBank.ChainComparison edges vertices (.nil first)
        ((included.resplit stem lastMember).based (.nil last))
      simpa only [Walks.Walk.based, Walks.Walk.append, -eq_self, -iff_self] using
        (RootEdgeBank.ChainComparison.retrace (edges := edges) (vertices :=
          vertices) reference (included.resplit stem lastMember)).symm
  | cell cell member connector =>
      change RootEdgeBank.ChainComparison edges vertices
        (included.resplit ((stem.append connector).based (CellBoundary.Cell.boundaryWalk cell member))
          firstMember) _
      have first := included.resplit_based edges vertices reference (stem.append connector)
        (CellBoundary.Cell.boundaryWalk cell member) firstMember (ClearGrid.Cell.anchor_mem
          cell member)
      rw [included.resplit_append _ _ lastMember (ClearGrid.Cell.anchor_mem cell member)] at first
      have last := (included.resplit_based edges vertices reference connector
        (CellBoundary.Cell.boundaryWalk cell member)
        lastMember (ClearGrid.Cell.anchor_mem cell member)).based (included.resplit stem lastMember)
      refine first.trans ((RootEdgeBank.ChainComparison.of_eq ?_).trans last.symm)
      simp only [Walks.Walk.based, Walks.Walk.reverse_append,
        Walks.Walk.append_assoc, -eq_self, -iff_self]
      rfl
  | append first last ihFirst ihLast =>
      change RootEdgeBank.ChainComparison edges vertices
        (included.resplit ((first.based stem).product.append (last.based stem).product) firstMember)
        ((included.resplit stem lastMember).based (included.resplit (first.product.append last.product) lastMember))
      rw [included.resplit_append _ _ firstMember firstMember, included.resplit_append _ _ lastMember lastMember]
      exact (ihFirst.append ihLast).trans
        (RootEdgeBank.ChainComparison.based_append reference (included.resplit stem
          lastMember)
          (included.resplit first.product lastMember) (included.resplit last.product lastMember))

end Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits

namespace Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

/-- The right-before-left order survives subdivision. The shared side and
the bottom connector are cancelled on their actual arriving sheets. -/
theorem resplit_horizontal_sewing {a b c d e f : Gaussian.Basic.Canonical}
    (bottomLeft : Walks.Walk original a b) (bottomRight : Walks.Walk original b c)
    (right : Walks.Walk original c f) (topRight : Walks.Walk original e f) (topLeft :
      Walks.Walk original d e)
    (left : Walks.Walk original a d) (seam : Walks.Walk original b e)
    (aMember : FromStates.ContainsVertex original a) (bMember :
      FromStates.ContainsVertex original b)
    (cMember : FromStates.ContainsVertex original c) (dMember :
      FromStates.ContainsVertex original d)
    (eMember : FromStates.ContainsVertex original e) (fMember :
      FromStates.ContainsVertex original f) :
    RootEdgeBank.ChainComparison edges vertices
      (included.resplit ((bottomLeft.based (Walks.Walk.rectangle bottomRight right topRight seam)).append
        (Walks.Walk.rectangle bottomLeft seam topLeft left)) aMember)
      (included.resplit (Walks.Walk.rectangle (bottomLeft.append bottomRight) right (topLeft.append
        topRight) left) aMember) := by
  have first := (included.resplit_based edges vertices reference bottomLeft
    (Walks.Walk.rectangle bottomRight right topRight seam) aMember bMember).trans
    ((included.resplit_rectangle edges vertices reference bottomRight right topRight seam
      bMember cMember eMember fMember).based (included.resplit bottomLeft bMember))
  have second := included.resplit_rectangle edges vertices reference bottomLeft seam topLeft left
    aMember bMember dMember eMember
  have outer := included.resplit_rectangle edges vertices reference (bottomLeft.append bottomRight) right
    (topLeft.append topRight) left aMember cMember dMember fMember
  rw [included.resplit_append _ _ bMember cMember, included.resplit_append _ _ eMember fMember] at outer
  rw [included.resplit_append _ _ aMember aMember]
  exact (first.append second).trans
    ((RootEdgeBank.ChainComparison.horizontal_sewing reference (included.resplit
      bottomLeft bMember)
      (included.resplit bottomRight cMember) (included.resplit right fMember)
      (included.resplit topRight fMember) (included.resplit topLeft eMember)
      (included.resplit left dMember) (included.resplit seam eMember)).trans outer.symm)

/-- The lower-before-upper row order likewise retains the subdivided
left connector and shared horizontal side until their exact cancellation. -/
theorem resplit_vertical_sewing {a b c d e f : Gaussian.Basic.Canonical}
    (bottom : Walks.Walk original a b) (rightLower : Walks.Walk original b d)
    (rightUpper : Walks.Walk original d f) (top : Walks.Walk original e f) (leftUpper :
      Walks.Walk original c e)
    (leftLower : Walks.Walk original a c) (seam : Walks.Walk original c d)
    (aMember : FromStates.ContainsVertex original a) (bMember :
      FromStates.ContainsVertex original b)
    (cMember : FromStates.ContainsVertex original c) (dMember :
      FromStates.ContainsVertex original d)
    (eMember : FromStates.ContainsVertex original e) (fMember :
      FromStates.ContainsVertex original f) :
    RootEdgeBank.ChainComparison edges vertices
      (included.resplit ((Walks.Walk.rectangle bottom rightLower seam leftLower).append
        (leftLower.based (Walks.Walk.rectangle seam rightUpper top leftUpper))) aMember)
      (included.resplit (Walks.Walk.rectangle bottom (rightLower.append rightUpper) top (leftLower.append
        leftUpper)) aMember) := by
  have first := included.resplit_rectangle edges vertices reference bottom rightLower seam leftLower
    aMember bMember cMember dMember
  have second := (included.resplit_based edges vertices reference leftLower
    (Walks.Walk.rectangle seam rightUpper top leftUpper) aMember cMember).trans
    ((included.resplit_rectangle edges vertices reference seam rightUpper top leftUpper
      cMember dMember eMember fMember).based (included.resplit leftLower cMember))
  have outer := included.resplit_rectangle edges vertices reference bottom (rightLower.append rightUpper) top
    (leftLower.append leftUpper) aMember bMember eMember fMember
  rw [included.resplit_append _ _ dMember fMember, included.resplit_append _ _ cMember eMember] at outer
  rw [included.resplit_append _ _ aMember aMember]
  exact (first.append second).trans
    ((RootEdgeBank.ChainComparison.vertical_sewing reference (included.resplit
      bottom bMember)
      (included.resplit rightLower dMember) (included.resplit rightUpper fMember)
      (included.resplit top fMember) (included.resplit leftUpper eMember)
      (included.resplit leftLower cMember) (included.resplit seam dMember)).trans outer.symm)

end Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion

end
