module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
public import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CircuitSewing
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.RowOrder
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts

public section

/-! The original ordered rectangular circuit tree sews to the original
exterior after subdivision, on every actual new-grid root sheet. -/

section
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib
open Purelib.RootIsolation

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}
  {original grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} (included :
    Geometry.Grid.Extension.CoordinateInclusion original grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits in
/-- The original horizontal and vertical lookup entries determine an actual retained grid corner. -/
private theorem corner_member {x y : Fraction.Rational}
    (vertical : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate)
      original.vertical x)
    (horizontal : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      original.horizontal y) :
    FromStates.ContainsVertex original (Gaussian.Components.Basic.point x y) :=
  ⟨Data.List.Map.mem_map.mpr ⟨vertical.entry, vertical.member, vertical.coordinate_eq⟩,
    Data.List.Map.mem_map.mpr ⟨horizontal.entry, horizontal.member, horizontal.coordinate_eq⟩⟩

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits in
/-- A retained horizontal lookup at an original line coordinate gives that line's increasing axis walk. -/
private theorem horizontal_entry {first last : Fraction.Rational}
    (x : Geometry.Grid.AxisWalks.IncreasingWalk original.xIntervals first last)
    (entry : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : entry ∈ original.horizontal)
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      original.horizontal entry.coordinate) :
    horizontal x line = Purelib.Polynomial.Geometry.Grid.Walks.Walk.horizontalIncreasing entry member x := by
  rw [Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique original.horizontal_ordered line (⟨entry, member,
    rfl⟩ : Geometry.Grid.AxisWalks.Lookup original.horizontal entry.coordinate)]
  rfl

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

namespace Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

variable {left right : Fraction.Rational} (x : Geometry.Grid.AxisWalks.IncreasingWalk original.xIntervals left right)
  (leftLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) original.vertical
    left)
  (rightLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) original.vertical
    right)
include reference

open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits in
/-- The resplit window-circuit product compares to its original exterior boundary in lower-before-upper row order.

The construction retains the original side lookups, connectors and ordered circuit tree while cancelling shared sides on
the actual arriving sheets. -/
theorem resplit_comparison :
    {bottom top : Fraction.Rational} → (y : Geometry.Grid.AxisWalks.IncreasingWalk original.yIntervals bottom top) →
    (bottomLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      original.horizontal bottom) →
    (topLine : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
      original.horizontal top) →
    (member : FromStates.ContainsVertex original (Gaussian.Components.Basic.point left bottom)) →
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      (Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk x leftLine y).product member)
      (included.resplit (Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary x leftLine rightLine y bottomLine
        topLine) member)
  | _, _, .nil _, bottomLine, topLine, member => by
      have same := Geometry.Grid.WindowCircuitOrder.WindowCircuits.lookup_unique original.horizontal_ordered bottomLine
        topLine
      cases same
      let farMember := Geometry.Grid.WindowCircuitOrder.WindowCircuits.corner_member rightLine bottomLine
      have rectangle := included.resplit_rectangle edges vertices reference (horizontal x bottomLine) (.nil _)
        (horizontal x bottomLine) (.nil _) member farMember member farMember
      change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices
        (included.resplit (Geometry.Grid.Walks.Walk.rectangle (horizontal x bottomLine) (.nil _) (horizontal x
          bottomLine) (.nil _)) member)
        ((included.resplit (horizontal x bottomLine) farMember).append
          ((included.resplit (horizontal x bottomLine) farMember).reverse.append (.nil _))) at rectangle
      rw [Geometry.Grid.Walks.Walk.append_nil] at rectangle
      have cancelled := (SquareRoot.Grid.RootEdgeBank.ChainComparison.retrace reference
        (included.resplit (horizontal x bottomLine) farMember)).symm.trans rectangle.symm
      change SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit (.nil _)
        member)
        (included.resplit (Geometry.Grid.Walks.Walk.rectangle (horizontal x bottomLine) (.nil _) (horizontal x
          bottomLine) (.nil _)) member) at cancelled
      simpa only [Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk,
        Geometry.Grid.RowCircuitOrder.CellCircuits.product, Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary,
        AxisChainCoherence.WindowCircuits.vertical_nil_eq, -eq_self, -iff_self] using cancelled
  | _, _, .cons band bandMember tail, bottomLine, topLine, member => by
      let seam : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
        original.horizontal band.upper.coordinate :=
        ⟨band.upper, (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.horizontal_ordered bandMember).2, rfl⟩
      let leftEdge := Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band bandMember leftLine
      let rightEdge := Geometry.Grid.WindowCircuitOrder.WindowCircuits.side band bandMember rightLine
      let leftSide : Geometry.Grid.Walks.Walk original (Gaussian.Components.Basic.point left band.lower.coordinate)
        (Gaussian.Components.Basic.point left band.upper.coordinate) :=
        .cons leftEdge (.nil _)
      let rightSide : Geometry.Grid.Walks.Walk original (Gaussian.Components.Basic.point right band.lower.coordinate)
        (Gaussian.Components.Basic.point right band.upper.coordinate) :=
        .cons rightEdge (.nil _)
      have row := RowCircuits.resplit_comparison included edges vertices reference band bandMember x leftEdge rightEdge
      have rest := Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits.resplit_comparison tail seam
        topLine leftEdge.vertices.2
      have based := (CellCircuits.resplit_based_product included edges vertices reference leftSide
        (Geometry.Grid.WindowCircuitOrder.WindowCircuits.ofWalk x leftLine tail)
          member leftEdge.vertices.2).trans
        ((rest.based (included.resplit leftSide leftEdge.vertices.2)).trans
          (included.resplit_based edges vertices reference leftSide
            (Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary x leftLine rightLine tail seam topLine)
            member leftEdge.vertices.2).symm)
      have sewn := included.resplit_vertical_sewing edges vertices reference
        (Geometry.Grid.RowCircuitOrder.RowCircuits.bottom band bandMember x)
        rightSide (vertical rightLine tail) (horizontal x topLine) (vertical leftLine tail) leftSide
        (Geometry.Grid.RowCircuitOrder.RowCircuits.top band bandMember x) member rightEdge.vertices.1
          leftEdge.vertices.2 rightEdge.vertices.2
        (Geometry.Grid.WindowCircuitOrder.WindowCircuits.corner_member leftLine topLine)
          (Geometry.Grid.WindowCircuitOrder.WindowCircuits.corner_member rightLine topLine)
      erw [included.resplit_append _ _ member member] at sewn
      have combined := (row.append based).trans sewn
      apply (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_).trans (combined.trans
        (SquareRoot.Grid.RootEdgeBank.ChainComparison.of_eq ?_))
      · rw [← included.resplit_append _ _ member member]
        rfl
      · apply congrArg (fun walk => included.resplit walk member)
        simp only [Geometry.Grid.WindowCircuitOrder.WindowCircuits.boundary,
          Geometry.Grid.WindowCircuitOrder.WindowCircuits.horizontal_entry x band.lower
          (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.horizontal_ordered bandMember).1,
          AxisChainCoherence.WindowCircuits.vertical_cons_eq, Geometry.Grid.Walks.Walk.rectangle,
            Geometry.Grid.Walks.Walk.append, leftSide, rightSide, Geometry.Grid.RowCircuitOrder.RowCircuits.bottom,
            leftEdge, rightEdge, -eq_self, -iff_self]
        rfl

end Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder.WindowCircuits

include reference

namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

/-- Full exterior identification for the original window and original
cell order, using the new mesh's sheet-aware edge bank throughout. -/
theorem resplit_circuits_comparison {box : Box} (window : Window
  original box)
    (member : FromStates.ContainsVertex original (Gaussian.Components.Basic.point box.xLower
      box.yLower)) :
    SquareRoot.Grid.RootEdgeBank.ChainComparison edges vertices (included.resplit
      window.circuits.product member)
      (included.resplit window.boundary member) :=
  Geometry.Grid.WindowCircuitOrder.WindowCircuits.resplit_comparison included edges vertices reference window.x
    window.left window.right
    window.y window.bottom window.top member

end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

end
