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

open Purelib.Riemann.Paths.PreparedPathWinding
open Purelib.Polynomial.Dense.Gaussian.Path.Box

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

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

namespace Walk

variable {grid : ClearGrid polynomial ambient}

/-- Appending compatible grid walks adds their exact raw windings.

The original endpoint thread joins the retained edge lists. Integer addition
regroups only the scalar head contribution and the unchanged tail sum. -/
theorem append_winding : {start middle finish : Gaussian.Basic.Canonical} → (first : Walks.Walk grid start
  middle) →
    (second : Walks.Walk grid middle finish) →
    ClearPath.rawWinding (first.append second).path =
      ClearPath.rawWinding first.path +
      ClearPath.rawWinding second.path
  | _, _, _, .nil _, _ => (Int.Arithmetic.zero_add _).symm
  | _, _, _, .cons edge tail, second => by
      change ClearSegment.rawWinding edge.segment +
        ClearPath.rawWinding (tail.append second).path = _
      rw [Walk.append_winding tail second]
      exact (Int.Arithmetic.add_assoc _ _ _).symm

/-- Reversing a grid walk onto a suffix negates its raw winding and adds the suffix winding.

Each original edge is traversed in reverse order and orientation before the
retained suffix. Segment reversal and direct integer addition identify the sum. -/
theorem reverseOnto_winding : {start middle finish : Gaussian.Basic.Canonical} → (walk : Walks.Walk grid
  start middle) →
    (suffix : Walks.Walk grid start finish) →
    ClearPath.rawWinding (walk.reverseOnto suffix).path =
      -ClearPath.rawWinding walk.path +
      ClearPath.rawWinding suffix.path
  | _, _, _, .nil _, _ => (Int.Arithmetic.zero_add _).symm
  | _, _, _, .cons edge tail, suffix => by
      change ClearPath.rawWinding (tail.reverseOnto (.cons (.reverse edge)
        suffix)).path = _
      rw [Walk.reverseOnto_winding tail]
      change -ClearPath.rawWinding tail.path +
        (ClearSegment.rawWinding
          (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse edge.segment) +
            ClearPath.rawWinding suffix.path) =
        -(ClearSegment.rawWinding edge.segment +
          ClearPath.rawWinding tail.path) +
          ClearPath.rawWinding suffix.path
      rw [Riemann.Paths.PreparedPathClosure.ClearSegment.rawWinding_reverse]
      omega

/-- Reversing a grid walk negates its raw winding. -/
theorem reverse_winding {start finish : Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish) :
    ClearPath.rawWinding walk.reverse.path =
      -ClearPath.rawWinding walk.path := by
  change ClearPath.rawWinding (walk.reverseOnto (.nil start)).path = _
  rw [reverseOnto_winding]
  exact Int.add_zero _

/-- Transporting a grid walk along endpoint equalities preserves its raw winding. -/
theorem castEndpoints_winding {start finish first last : Gaussian.Basic.Canonical} (walk : Walks.Walk grid
  start finish)
    (startEq : start = first) (finishEq : finish = last) :
    ClearPath.rawWinding (walk.castEndpoints startEq finishEq).path =
      ClearPath.rawWinding walk.path := by
  cases startEq
  cases finishEq
  rfl

/-- An increasing horizontal grid walk has the doubled winding of its complete horizontal edge.

The original adjacent horizontal intervals telescope through their retained
Cauchy indices. Empty walks give the zero difference at one endpoint. -/
theorem horizontalIncreasing_winding (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    ClearPath.rawWinding (Walks.Walk.horizontalIncreasing line member
      walk).path =
      (Sides.horizontalEdge polynomial line.coordinate start finish).doubledWinding
  | _, _, .nil _ => (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  | _, _, .cons interval adjacent tail => by
      change ClearSegment.rawWinding (Walks.Edge.horizontal interval
        adjacent line member).segment +
        ClearPath.rawWinding (Walks.Walk.horizontalIncreasing line
          member tail).path = _
      rw [ClearSegment.rawWinding_eq_coordinateWinding,
        Walk.horizontalIncreasing_winding line member tail]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- An increasing vertical grid walk has the doubled winding of its complete vertical edge.

The original adjacent vertical intervals telescope through their retained
Cauchy indices. Empty walks give the zero difference at one endpoint. -/
theorem verticalIncreasing_winding (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.yIntervals start finish) →
    ClearPath.rawWinding (Walks.Walk.verticalIncreasing line member
      walk).path =
      (Sides.verticalEdge polynomial line.coordinate start finish).doubledWinding
  | _, _, .nil _ => (Int.Arithmetic.sub_eq_zero_of_eq (Eq.refl _)).symm
  | _, _, .cons interval adjacent tail => by
      change ClearSegment.rawWinding (Walks.Edge.vertical interval
        adjacent line member).segment +
        ClearPath.rawWinding (Walks.Walk.verticalIncreasing line member
          tail).path = _
      rw [ClearSegment.rawWinding_eq_coordinateWinding,
        Walk.verticalIncreasing_winding line member tail]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_add _ _ _ _ _).symm

/-- A horizontal grid walk in either direction has the doubled winding of its oriented full edge. -/
theorem horizontalAxis_winding (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal)
    {start finish : Fraction.Rational} (walk : AxisWalks.Walk grid.xIntervals start finish) :
    ClearPath.rawWinding (Walks.Walk.horizontalAxis line member
      walk).path =
      (Sides.horizontalEdge polynomial line.coordinate start finish).doubledWinding := by
  cases walk with
  | forward increasing => exact horizontalIncreasing_winding line member increasing
  | backward increasing =>
      change ClearPath.rawWinding (Walks.Walk.horizontalIncreasing line
        member increasing).reverse.path = _
      rw [reverse_winding, horizontalIncreasing_winding]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _).symm

/-- A vertical grid walk in either direction has the doubled winding of its oriented full edge. -/
theorem verticalAxis_winding (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical)
    {start finish : Fraction.Rational} (walk : AxisWalks.Walk grid.yIntervals start finish) :
    ClearPath.rawWinding (Walks.Walk.verticalAxis line member walk).path
      =
      (Sides.verticalEdge polynomial line.coordinate start finish).doubledWinding := by
  cases walk with
  | forward increasing => exact verticalIncreasing_winding line member increasing
  | backward increasing =>
      change ClearPath.rawWinding (Walks.Walk.verticalIncreasing line
        member increasing).reverse.path = _
      rw [reverse_winding, verticalIncreasing_winding]
      exact (Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _).symm

end Walk

/-- The horizontal walk constructed from grid coordinates preserves the full edge's doubled winding. -/
theorem horizontalWalk_winding (grid : ClearGrid polynomial ambient) (start finish y :
  Fraction.Rational)
    (startMember : start ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (finishMember : finish ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) :
    ClearPath.rawWinding (Walks.horizontalWalk grid start finish y
      startMember finishMember lineMember).path =
      (Sides.horizontalEdge polynomial y start finish).doubledWinding := by
  dsimp only [Walks.horizontalWalk]
  rw [Walk.castEndpoints_winding,
    Walk.horizontalAxis_winding,
    (AxisWalks.lookup y grid.horizontal lineMember).coordinate_eq]

/-- The vertical walk constructed from grid coordinates preserves the full edge's doubled winding. -/
theorem verticalWalk_winding (grid : ClearGrid polynomial ambient) (x start finish :
  Fraction.Rational)
    (lineMember : x ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (startMember : start ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate)
    (finishMember : finish ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) :
    ClearPath.rawWinding (Walks.verticalWalk grid x start finish
      lineMember startMember finishMember).path =
      (Sides.verticalEdge polynomial x start finish).doubledWinding := by
  dsimp only [Walks.verticalWalk]
  rw [Walk.castEndpoints_winding,
    Walk.verticalAxis_winding,
    (AxisWalks.lookup x grid.vertical lineMember).coordinate_eq]

/-- Subdivision preserves the exact original segment index, even when its
clearance certificate used a different ambient rectangle. -/
theorem splitSegment_winding (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box}
    {start finish : Gaussian.Basic.Canonical} (segment : ClearPath.ClearSegment polynomial pathAmbient start
      finish)
    (first : FromStates.ContainsVertex grid start)
    (last : FromStates.ContainsVertex grid finish) :
    ClearPath.rawWinding (Walks.splitSegment grid segment first
      last).path =
      ClearSegment.rawWinding segment := by
  rw [ClearSegment.rawWinding_eq_coordinateWinding]
  cases segment with
  | horizontal => exact horizontalWalk_winding _ _ _ _ _ _ _
  | vertical => exact verticalWalk_winding _ _ _ _ _ _ _

/-- Exact winding preservation for the complete emitted path. -/
theorem splitPath_winding (grid : ClearGrid polynomial ambient) {pathAmbient : Box} :
    {start finish : Gaussian.Basic.Canonical} → (path : ClearPath polynomial pathAmbient start
      finish) →
    (onGrid : FromStates.ContainsPathVertices grid path) →
    ClearPath.rawWinding (Walks.splitPath grid path onGrid).path =
      ClearPath.rawWinding path
  | _, _, .nil _, _ => rfl
  | _, _, .cons head tail, onGrid => by
      change ClearPath.rawWinding ((Walks.splitSegment grid head
        onGrid.1
        (FromStates.ContainsPathVertices.start grid tail onGrid.2)).append
        (Walks.splitPath grid tail onGrid.2)).path = _
      rw [Walk.append_winding, splitSegment_winding,
        Winding.splitPath_winding]
      rfl

end

end Purelib.Polynomial.Geometry.Grid.Winding
