module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.PreparedPathClosure
public import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Tactic.QuotientFreeOmega

/-!
# Exact winding preservation under shared-grid subdivision

The actual emitted edge list has the winding of the original clear path.
Finite Cauchy-index telescoping handles arbitrary rational split coordinates,
both traversal directions, and stationary segments.  The proof does not
require grid crossings to lie on an older dyadic refinement.
-/

namespace Purelib.Polynomial.Geometry.Grid.Winding

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib

public section

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

namespace Walk

variable {grid : ClearGrid polynomial ambient}

/-- Appending compatible grid walks adds their exact raw windings.

The original endpoint thread joins the retained edge lists. Integer addition
regroups only the scalar head contribution and the unchanged tail sum. -/
theorem append_winding : {start middle finish : Gaussian.Basic.Canonical} → (first : Geometry.Grid.Walks.Walk grid start
  middle) →
    (second : Geometry.Grid.Walks.Walk grid middle finish) →
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (first.append second).path =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding first.path +
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding second.path
  | _, _, _, .nil _, _ => (Int.Arithmetic.zero_add _).symm
  | _, _, _, .cons edge tail, second => by
      change Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.segment +
        Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (tail.append second).path = _
      rw [Purelib.Polynomial.Geometry.Grid.Winding.Walk.append_winding tail second]
      exact (Int.Arithmetic.add_assoc _ _ _).symm

/-- Reversing a grid walk onto a suffix negates its raw winding and adds the suffix winding.

Each original edge is traversed in reverse order and orientation before the
retained suffix. Segment reversal and direct integer addition identify the sum. -/
theorem reverseOnto_winding : {start middle finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid
  start middle) →
    (suffix : Geometry.Grid.Walks.Walk grid start finish) →
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (walk.reverseOnto suffix).path =
      -Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path +
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding suffix.path
  | _, _, _, .nil _, _ => (Int.Arithmetic.zero_add _).symm
  | _, _, _, .cons edge tail, suffix => by
      change Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (tail.reverseOnto (.cons (.reverse edge)
        suffix)).path = _
      rw [Purelib.Polynomial.Geometry.Grid.Winding.Walk.reverseOnto_winding tail]
      change -Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding tail.path +
        (Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding
          (Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse edge.segment) +
            Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding suffix.path) =
        -(Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding edge.segment +
          Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding tail.path) +
          Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding suffix.path
      rw [Purelib.Riemann.Paths.PreparedPathClosure.ClearSegment.rawWinding_reverse]
      omega

/-- Reversing a grid walk negates its raw winding. -/
theorem reverse_winding {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.reverse.path =
      -Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path := by
  change Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (walk.reverseOnto (.nil start)).path = _
  rw [Geometry.Grid.Winding.Walk.reverseOnto_winding]
  exact Int.add_zero _

/-- Transporting a grid walk along endpoint equalities preserves its raw winding. -/
theorem castEndpoints_winding {start finish first last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid
  start finish)
    (startEq : start = first) (finishEq : finish = last) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (walk.castEndpoints startEq finishEq).path =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path := by
  cases startEq
  cases finishEq
  rfl

/-- An increasing horizontal grid walk has the doubled winding of its complete horizontal edge.

The original adjacent horizontal intervals telescope through their retained
Cauchy indices. Empty walks give the zero difference at one endpoint. -/
theorem horizontalIncreasing_winding (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.horizontalIncreasing line member
      walk).path =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial line.coordinate start finish).doubledWinding
  | _, _, .nil _ => (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  | _, _, .cons interval adjacent tail => by
      change Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding (Geometry.Grid.Walks.Edge.horizontal interval
        adjacent line member).segment +
        Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.horizontalIncreasing line
          member tail).path = _
      rw [Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
        Purelib.Polynomial.Geometry.Grid.Winding.Walk.horizontalIncreasing_winding line member tail]
      exact (Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- An increasing vertical grid walk has the doubled winding of its complete vertical edge.

The original adjacent vertical intervals telescope through their retained
Cauchy indices. Empty walks give the zero difference at one endpoint. -/
theorem verticalIncreasing_winding (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish) →
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.verticalIncreasing line member
      walk).path =
      (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial line.coordinate start finish).doubledWinding
  | _, _, .nil _ => (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  | _, _, .cons interval adjacent tail => by
      change Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding (Geometry.Grid.Walks.Edge.vertical interval
        adjacent line member).segment +
        Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.verticalIncreasing line member
          tail).path = _
      rw [Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding,
        Purelib.Polynomial.Geometry.Grid.Winding.Walk.verticalIncreasing_winding line member tail]
      exact (Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- A horizontal grid walk in either direction has the doubled winding of its oriented full edge. -/
theorem horizontalAxis_winding (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal)
    {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.Walk grid.xIntervals start finish) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.horizontalAxis line member
      walk).path =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial line.coordinate start finish).doubledWinding := by
  cases walk with
  | forward increasing => exact Geometry.Grid.Winding.Walk.horizontalIncreasing_winding line member increasing
  | backward increasing =>
      change Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.horizontalIncreasing line
        member increasing).reverse.path = _
      rw [Geometry.Grid.Winding.Walk.reverse_winding, Geometry.Grid.Winding.Walk.horizontalIncreasing_winding]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _).symm

/-- A vertical grid walk in either direction has the doubled winding of its oriented full edge. -/
theorem verticalAxis_winding (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical)
    {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.Walk grid.yIntervals start finish) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.verticalAxis line member walk).path
      =
      (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial line.coordinate start finish).doubledWinding := by
  cases walk with
  | forward increasing => exact Geometry.Grid.Winding.Walk.verticalIncreasing_winding line member increasing
  | backward increasing =>
      change Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.Walk.verticalIncreasing line
        member increasing).reverse.path = _
      rw [Geometry.Grid.Winding.Walk.reverse_winding, Geometry.Grid.Winding.Walk.verticalIncreasing_winding]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _).symm

end Walk

/-- The horizontal walk constructed from grid coordinates preserves the full edge's doubled winding. -/
theorem horizontalWalk_winding (grid : ClearGrid polynomial ambient) (start finish y :
  Fraction.Rational)
    (startMember : start ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (finishMember : finish ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.horizontalWalk grid start finish y
      startMember finishMember lineMember).path =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial y start finish).doubledWinding := by
  dsimp only [Geometry.Grid.Walks.horizontalWalk]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding,
    Geometry.Grid.Winding.Walk.horizontalAxis_winding,
    (Geometry.Grid.AxisWalks.lookup y grid.horizontal lineMember).coordinate_eq]

/-- The vertical walk constructed from grid coordinates preserves the full edge's doubled winding. -/
theorem verticalWalk_winding (grid : ClearGrid polynomial ambient) (x start finish :
  Fraction.Rational)
    (lineMember : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (startMember : start ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (finishMember : finish ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.verticalWalk grid x start finish
      lineMember startMember finishMember).path =
      (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial x start finish).doubledWinding := by
  dsimp only [Geometry.Grid.Walks.verticalWalk]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding,
    Geometry.Grid.Winding.Walk.verticalAxis_winding,
    (Geometry.Grid.AxisWalks.lookup x grid.vertical lineMember).coordinate_eq]

/-- Subdivision preserves the exact original segment index, even when its
clearance certificate used a different ambient rectangle. -/
theorem splitSegment_winding (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box}
    {start finish : Gaussian.Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment polynomial pathAmbient start
      finish)
    (first : FromStates.ContainsVertex grid start)
    (last : FromStates.ContainsVertex grid finish) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.splitSegment grid segment first
      last).path =
      Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding segment := by
  rw [Riemann.Paths.PreparedPathWinding.ClearSegment.rawWinding_eq_coordinateWinding]
  cases segment with
  | horizontal => exact Geometry.Grid.Winding.horizontalWalk_winding _ _ _ _ _ _ _
  | vertical => exact Geometry.Grid.Winding.verticalWalk_winding _ _ _ _ _ _ _

/-- Exact winding preservation for the complete emitted path. -/
theorem splitPath_winding (grid : ClearGrid polynomial ambient) {pathAmbient : Box} :
    {start finish : Gaussian.Basic.Canonical} → (path : ClearPath polynomial pathAmbient start
      finish) →
    (onGrid : FromStates.ContainsPathVertices grid path) →
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (Geometry.Grid.Walks.splitPath grid path onGrid).path =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding path
  | _, _, .nil _, _ => rfl
  | _, _, .cons head tail, onGrid => by
      change Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding ((Geometry.Grid.Walks.splitSegment grid head
        onGrid.1
        (FromStates.ContainsPathVertices.start grid tail onGrid.2)).append
        (Geometry.Grid.Walks.splitPath grid tail onGrid.2)).path = _
      rw [Geometry.Grid.Winding.Walk.append_winding, Geometry.Grid.Winding.splitSegment_winding,
        Purelib.Polynomial.Geometry.Grid.Winding.splitPath_winding]
      rfl

end

end Purelib.Polynomial.Geometry.Grid.Winding
