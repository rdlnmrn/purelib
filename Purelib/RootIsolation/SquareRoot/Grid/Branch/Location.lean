module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Interior
import Purelib.RootIsolation.Track.Basic
public import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
public import Purelib.Polynomial.Geometry.Grid.Incidence
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Quantitative branch location in the shared grid

One cached positive margin for all retained grid lines gives a uniform
refinement radius.  A winding-one box refined to that radius lies strictly
inside the cell containing its anchor: a box meeting a clear cell boundary
would have winding zero by the existing finite residual estimate.

Each located cell refines the original branch box.  This constructs
branch-to-cell locations, not a classification of every remaining face as
unramified; that still needs the degree-complete winding count.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.Branch.Location

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- A positive grid-wide boundary margin, computed from the line banks
without materializing the Cartesian product of faces. -/
@[expose] def lineMargin (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) : Fraction.Rational :=
  min (Data.Rat.List.Minimum.Maximality.positiveMinimum (grid.vertical.map fun line => line.clearance.bound))
    (Data.Rat.List.Minimum.Maximality.positiveMinimum (grid.horizontal.map fun line => line.clearance.bound))

/-- The grid-wide margin computed from the finite line banks is strictly positive.

Every retained vertical and horizontal line has a positive clearance bound. Their original finite minima and the common
minimum therefore remain strictly positive. -/
theorem lineMargin_positive (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) : 0 <
  SquareRoot.Grid.Branch.Location.lineMargin grid := by
  apply Fraction.Order.Basic.lt_min
  · apply Data.Rat.List.Minimum.Maximality.positiveMinimum_pos
    intro value member
    rcases Data.List.Map.mem_map.mp member with ⟨line, _, equal⟩
    rw [← equal]
    exact line.clearance.positive
  · apply Data.Rat.List.Minimum.Maximality.positiveMinimum_pos
    intro value member
    rcases Data.List.Map.mem_map.mp member with ⟨line, _, equal⟩
    rw [← equal]
    exact line.clearance.positive

/-- The common grid margin is at most every retained vertical-line clearance bound.

The original vertical-line occurrence supplies the corresponding bound for its finite minimum. The common minimum is at
most that retained vertical minimum. -/
theorem lineMargin_le_vertical (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (line :
  Geometry.Grid.ClearGrid.VerticalLine polynomial ambient)
    (member : line ∈ grid.vertical) : SquareRoot.Grid.Branch.Location.lineMargin grid ≤ line.clearance.bound :=
  (Fraction.Order.Basic.min_le_left _ _).trans (Data.Rat.List.Minimum.Maximality.positiveMinimum_le_of_mem
    (Data.List.Map.mem_map_of_mem member))

/-- The common grid margin is at most every retained horizontal-line clearance bound.

The original horizontal-line occurrence supplies the corresponding bound for its finite minimum. The common minimum is
at most that retained horizontal minimum. -/
theorem lineMargin_le_horizontal (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (line :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)
    (member : line ∈ grid.horizontal) : SquareRoot.Grid.Branch.Location.lineMargin grid ≤ line.clearance.bound :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Data.Rat.List.Minimum.Maximality.positiveMinimum_le_of_mem
    (Data.List.Map.mem_map_of_mem member))

/-- The common grid margin is at most every actual grid cell's boundary-clearance bound.

The retained cell occurrence identifies its original two vertical and two horizontal endpoints. The common line margin
is below each of those four bounds and hence below the same cell boundary minimum. -/
theorem lineMargin_le_cell (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (cell :
  Geometry.Grid.ClearGrid.Cell
  polynomial ambient)
    (member : cell ∈ grid.cells) : SquareRoot.Grid.Branch.Location.lineMargin grid ≤ cell.boundaryClearance.bound := by
  rcases Data.List.Flatten.mem_flatMap.mp member with ⟨horizontal, horizontalMember, member⟩
  rcases Data.List.Map.mem_map.mp member with ⟨vertical, verticalMember, equal⟩
  subst cell
  have x := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.vertical_ordered horizontalMember
  have y := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered verticalMember
  exact Fraction.Order.Basic.le_min (SquareRoot.Grid.Branch.Location.lineMargin_le_vertical grid _ x.1)
    (Fraction.Order.Basic.le_min (SquareRoot.Grid.Branch.Location.lineMargin_le_vertical grid _ x.2)
      (Fraction.Order.Basic.le_min (SquareRoot.Grid.Branch.Location.lineMargin_le_horizontal grid _ y.1)
        (SquareRoot.Grid.Branch.Location.lineMargin_le_horizontal grid _ y.2)))

set_option genInjectivity false in
/-- Cached executable numbers used by every branch assigned to this grid.
Alternative checked caches need the semantic bounds, not equality to the
canonical minimum or radius calculation.

The cached margin, Lipschitz coefficient and radius retain their displayed scalar identities and positivity. Every
original cell receives the same boundary margin; the scaled radius fits strictly beneath that same bound. -/
structure BranchBudget (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) where
  /-- The retained grid-wide boundary margin. -/ margin : Fraction.Rational
  /-- The retained common margin is strictly positive. -/ margin_positive : 0 < margin
  /-- The common margin is below every actual grid cell's boundary-clearance bound. -/ margin_le_cell : ∀ cell ∈
    grid.cells, margin ≤ cell.boundaryClearance.bound
  /-- The cached polynomial Lipschitz coefficient on the original ambient box. -/ lipschitz : Fraction.Rational
  /-- The cached coefficient equals the original finite Horner-Lipschitz bound. -/ lipschitz_eq : lipschitz =
    Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient
  /-- The retained common branch-refinement radius. -/ radius : Fraction.Rational
  /-- The retained common radius is strictly positive. -/ radius_positive : 0 < radius
  /-- The retained radius is at most one. -/ radius_le_one : radius ≤ 1
  /-- Four times the cached Lipschitz coefficient and radius fits strictly below the common margin. -/ scaled_lt_margin
    : 4 * lipschitz * radius < margin

constructive_injectivity BranchBudget

namespace BranchBudget

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

/-- A proved finite arithmetic selector; no successful-search premise.

The original finite line margins and polynomial Lipschitz bound determine the retained radius as the same rational
minimum. Direct scalar bounds certify its positivity, unit ceiling and strict scaled margin without a successful-search
premise. -/
@[expose] def ofGrid (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) :
  SquareRoot.Grid.Branch.Location.BranchBudget grid := by
  let margin := SquareRoot.Grid.Branch.Location.lineMargin grid
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient
  let radius := min 1 (margin / (8 * lipschitz))
  have lipschitzPositive : 0 < lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos _ _
  have denominatorPositive : 0 < 8 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have radiusPositive : 0 < radius :=
    Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct
      (SquareRoot.Grid.Branch.Location.lineMargin_positive grid) denominatorPositive)
  have scaled : radius * (8 * lipschitz) ≤ margin :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp (Fraction.Order.Basic.min_le_right _ _)
  refine ⟨margin, SquareRoot.Grid.Branch.Location.lineMargin_positive grid,
    SquareRoot.Grid.Branch.Location.lineMargin_le_cell grid, lipschitz, rfl,
    radius, radiusPositive, Fraction.Order.Basic.min_le_left _ _, ?_⟩
  calc
    4 * lipschitz * radius = 4 * (lipschitz * radius) := by ring1
    _ < 8 * (lipschitz * radius) := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (4 : Fraction.Rational) < 8 by decide) (Fraction.Order.Arithmetic.mul_pos_direct lipschitzPositive
        radiusPositive)
    _ = radius * (8 * lipschitz) := by ring1
    _ ≤ margin := scaled

/-- Squaring the retained branch radius does not increase it. -/
theorem radius_sq_le (budget : SquareRoot.Grid.Branch.Location.BranchBudget grid) : budget.radius ^ 2 ≤ budget.radius :=
  by
  rw [pow_two]
  calc
    budget.radius * budget.radius ≤ 1 * budget.radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.radius_le_one budget.radius_positive.le
    _ = budget.radius := by ring1

/-- The common radius makes the existing finite boundary-exclusion theorem
applicable to every actual grid cell. -/
theorem dominates (budget : SquareRoot.Grid.Branch.Location.BranchBudget grid) (state :
  State.WindingOne.Basic.WindingOneState polynomial ambient)
    (diagonal : state.box.diagonalSq ≤ budget.radius ^ 2)
    (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound polynomial ambient state.box +
      Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient * state.box.diagonalSq) <
        cell.boundaryClearance.bound := by
  have lipschitzPositive : 0 < budget.lipschitz := by
    rw [budget.lipschitz_eq]
    exact Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos _ _
  have factorNonnegative : 0 ≤ 4 * budget.lipschitz :=
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) lipschitzPositive).le
  calc
    2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound polynomial ambient state.box +
        Dense.Gaussian.Bounds.Box.denseLipschitzBound polynomial ambient * state.box.diagonalSq) =
        4 * budget.lipschitz * state.box.diagonalSq := by
          rw [budget.lipschitz_eq]
          unfold Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound
          ring1
    _ ≤ 4 * budget.lipschitz * budget.radius ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal factorNonnegative
    _ ≤ 4 * budget.lipschitz * budget.radius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.radius_sq_le factorNonnegative
    _ < budget.margin := budget.scaled_lt_margin
    _ ≤ cell.boundaryClearance.bound := budget.margin_le_cell cell member

end BranchBudget

set_option genInjectivity false in
/-- The retained refined branch state and its strictly containing grid cell.
These are executable witnesses, not a proposition asserting that a search
will eventually find a face.

The selected refined state and its grid-cell occurrence remain executable witnesses with the original parent identities.
Strict containment and refinement link that exact state, cell and original branch box. -/
structure BranchLocation (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) (original :
  State.WindingOne.Basic.WindingOneState polynomial ambient) where
  /-- The actual refined branch state retained by the locator. -/ state : State.WindingOne.Basic.WindingOneState
    polynomial ambient
  /-- The retained state box refines the original branch box. -/ refines : state.box.Refines original.box
  /-- The actual grid cell containing the refined branch state. -/ cell : Geometry.Grid.ClearGrid.Cell polynomial
    ambient
  /-- The retained cell belongs to the original grid. -/ member : cell ∈ grid.cells
  /-- The retained branch box lies strictly inside the selected grid cell. -/ strict : state.box.StrictInterior cell.box
  /-- The selected grid cell refines the original branch box. -/ cell_refines : cell.box.Refines original.box

constructive_injectivity BranchLocation

namespace BranchLocation

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {original :
  State.WindingOne.Basic.WindingOneState
  polynomial ambient}

/-- Accept a retained sufficiently accurate refinement.  Generated branch
boxes can use this entry without reexecuting the canonical track. -/
@[expose] def ofRefinement (budget : SquareRoot.Grid.Branch.Location.BranchBudget grid) (degreePositive : 0 <
  polynomial.natDegree)
    (state : State.WindingOne.Basic.WindingOneState polynomial ambient) (refines : state.box.Refines original.box)
    (diagonal : state.box.diagonalSq ≤ budget.radius ^ 2)
    (xLower : original.box.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (xUpper : original.box.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (yLower : original.box.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (yUpper : original.box.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
      SquareRoot.Grid.Branch.Location.BranchLocation grid original :=
  let inside := refines.contains state.box.contains_anchor
  let found := Polynomial.Geometry.Grid.ClearGridCoverage.locate grid state.box.anchor
    (Polynomial.Geometry.Grid.FromStates.spanned_of_keys _ _ xLower xUpper original.proper.1 ⟨inside.1, inside.2.1⟩)
    (Polynomial.Geometry.Grid.FromStates.spanned_of_keys _ _ yLower yUpper original.proper.2 inside.2.2)
  let strict := State.WindingOne.Interior.strictInterior_of_anchor_mem_of_dominates polynomial state degreePositive
    found.cell.box_refines found.cell.boundaryClearance found.contains (budget.dominates state diagonal found.cell
      found.member)
  { state := state
    refines := refines
    cell := found.cell
    member := found.member
    strict := strict
    cell_refines := Polynomial.Geometry.Grid.Incidence.cell_refines_of_strict_inner grid found.cell found.member xLower
      xUpper
      yLower yUpper refines strict }

/-- Refine once to the computed common radius and scan the two finite axes.
The track is already supplied by branch isolation and is not reacquired. -/
@[expose] def acquire (budget : SquareRoot.Grid.Branch.Location.BranchBudget grid) (degreePositive : 0 <
  polynomial.natDegree)
    (track : Track.Basic.WindingOneTrack polynomial ambient) (original : State.WindingOne.Basic.WindingOneState
      polynomial ambient)
    (xLower : original.box.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (xUpper : original.box.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (yLower : original.box.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (yUpper : original.box.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
      SquareRoot.Grid.Branch.Location.BranchLocation grid original :=
  let state := track.refine original budget.radius budget.radius_positive
  SquareRoot.Grid.Branch.Location.BranchLocation.ofRefinement budget degreePositive state (track.nested original
    budget.radius budget.radius_positive)
    (track.accurate original budget.radius budget.radius_positive) xLower xUpper yLower yUpper

open Purelib.Data.List in
/-- Two interior-separated cells cannot both strictly contain the same nonempty rational box.

Structural membership compares the displayed two cell occurrences in the original finite list. Pairwise interior
separation and the common retained box anchor exclude distinct containing cells. -/
private theorem cell_unique {small : Box} {cells : List (Geometry.Grid.ClearGrid.Cell polynomial
  ambient)}
    (pairwise : cells.Pairwise (fun first second => first.box.InteriorSeparated second.box))
    {first second : Geometry.Grid.ClearGrid.Cell polynomial ambient} (firstMember : first ∈ cells) (secondMember :
      second ∈ cells)
    (firstStrict : small.StrictInterior first.box) (secondStrict : small.StrictInterior second.box) : first = second :=
      by
  induction cells with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp firstMember with firstEq | firstMember
      · subst first
        rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · exact secondEq.symm
        · have separated := ((List.pairwise_cons.mp pairwise).1 second secondMember).strict_refinements firstStrict
            secondStrict
          exact (separated.points_ne small.contains_anchor small.contains_anchor rfl).elim
      · rcases Membership.mem_cons.mp secondMember with secondEq | secondMember
        · subst second
          have separated := ((List.pairwise_cons.mp pairwise).1 first firstMember).strict_refinements secondStrict
            firstStrict
          exact (separated.points_ne small.contains_anchor small.contains_anchor rfl).elim
        · exact ih (List.pairwise_cons.mp pairwise).2 firstMember secondMember

/-- A sufficiently refined branch cannot belong to two adjacent faces, even
though ordinary point location permits points on shared grid boundaries. -/
theorem unique (location : SquareRoot.Grid.Branch.Location.BranchLocation grid original) (other :
  Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (member : other ∈ grid.cells) (strict : location.state.box.StrictInterior other.box) : location.cell = other :=
  SquareRoot.Grid.Branch.Location.BranchLocation.cell_unique (Polynomial.Geometry.Grid.ClearGridCoverage.cells_pairwise
    grid)
    location.member member location.strict strict

end BranchLocation

end Purelib.RootIsolation.SquareRoot.Grid.Branch.Location
