module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic

public import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample

/-!
# The common clear-line grid of the actual branch tours

The grid retains all four ambient line certificates of every selected branch
box.  Thus every original connector and branch-boundary corner lies on one
shared finite coordinate grid, and every branch box is covered. The original
state owners and ambient line certificates are retained in that common grid.
-/

namespace Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- The original winding-one root-isolation state, indexed by its polynomial and
ambient box. -/
public abbrev BranchState (polynomial : Geometry.ClearPath.GaussianPolynomial) (ambient : Box) :=
  RootIsolation.State.WindingOne.Basic.WindingOneState polynomial ambient

/-- Retain the left and right ambient line-clearance payloads of a branch state's
box.

Both retained vertical side certificates come from the original state. The
ambient endpoint bounds keep those same clearance payloads on the original
polynomial and box. -/
@[expose] public def verticalSides (state : Geometry.Grid.FromStates.BranchState polynomial ambient) : List
  (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) :=
  [⟨state.box.xLower, ⟨state.refinesAmbient.1, state.box.x_valid.trans state.refinesAmbient.2.1⟩,
      state.ambientLeftClearance⟩,
    ⟨state.box.xUpper, ⟨state.refinesAmbient.1.trans state.box.x_valid, state.refinesAmbient.2.1⟩,
      state.ambientRightClearance⟩]

/-- Retain the bottom and top ambient line-clearance payloads of a branch state's
box.

Both retained horizontal side certificates come from the original state. The
ambient endpoint bounds keep those same clearance payloads on the original
polynomial and box. -/
@[expose] public def horizontalSides (state : Geometry.Grid.FromStates.BranchState polynomial ambient) : List
  (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) :=
  [⟨state.box.yLower, ⟨state.refinesAmbient.2.2.1, state.box.y_valid.trans state.refinesAmbient.2.2.2⟩,
      state.ambientBottomClearance⟩,
    ⟨state.box.yUpper, ⟨state.refinesAmbient.2.2.1.trans state.box.y_valid, state.refinesAmbient.2.2.2⟩,
      state.ambientTopClearance⟩]

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- All box-side lines are sorted together; no fresh polynomial-clearance search is
needed to create grid edges or face boundaries.

The displayed states supply the original four side-line payloads. Sorting those
retained payloads once gives the shared coordinate grid. -/
@[expose] public def ofStates (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
  ClearGrid polynomial ambient :=
  ClearGrid.build (states.flatMap Geometry.Grid.FromStates.verticalSides) (states.flatMap
    Geometry.Grid.FromStates.horizontalSides)

/-- Both horizontal endpoint coordinates of every retained state box occur in the
common vertical-line bank.

Both retained side occurrences come from the selected state in the original
list. The grid build preserves their two endpoint coordinates. -/
public theorem ofStates_x_bounds (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient))
    {state : Geometry.Grid.FromStates.BranchState polynomial ambient} (member : state ∈ states) :
    state.box.xLower ∈ (ofStates states).vertical.map
      Geometry.Grid.ClearGrid.VerticalLine.coordinate ∧
      state.box.xUpper ∈ (ofStates states).vertical.map VerticalLine.coordinate := by
  constructor
  · apply (ClearGrid.build_vertical_coordinates _ _ _).2
    exact Data.List.Map.mem_map.mpr ⟨(Geometry.Grid.FromStates.verticalSides state)[0]'(by change 0 < 2; decide),
      Data.List.Flatten.mem_flatMap.mpr ⟨state, member, List.mem_cons_self⟩, rfl⟩
  · apply (ClearGrid.build_vertical_coordinates _ _ _).2
    exact Data.List.Map.mem_map.mpr ⟨(Geometry.Grid.FromStates.verticalSides state)[1]'(by change 1 < 2; decide),
      Data.List.Flatten.mem_flatMap.mpr ⟨state, member, List.mem_cons_of_mem _ List.mem_cons_self⟩, rfl⟩

/-- Both vertical endpoint coordinates of every retained state box occur in the
common horizontal-line bank.

Both retained side occurrences come from the selected state in the original
list. The grid build preserves their two endpoint coordinates. -/
public theorem ofStates_y_bounds (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient))
    {state : Geometry.Grid.FromStates.BranchState polynomial ambient} (member : state ∈ states) :
    state.box.yLower ∈ (ofStates states).horizontal.map
      Geometry.Grid.ClearGrid.HorizontalLine.coordinate ∧
      state.box.yUpper ∈ (ofStates states).horizontal.map HorizontalLine.coordinate := by
  constructor
  · apply (ClearGrid.build_horizontal_coordinates _ _ _).2
    exact Data.List.Map.mem_map.mpr ⟨(Geometry.Grid.FromStates.horizontalSides state)[0]'(by change 0 < 2; decide),
      Data.List.Flatten.mem_flatMap.mpr ⟨state, member, List.mem_cons_self⟩, rfl⟩
  · apply (ClearGrid.build_horizontal_coordinates _ _ _).2
    exact Data.List.Map.mem_map.mpr ⟨(Geometry.Grid.FromStates.horizontalSides state)[1]'(by change 1 < 2; decide),
      Data.List.Flatten.mem_flatMap.mpr ⟨state, member, List.mem_cons_of_mem _ List.mem_cons_self⟩, rfl⟩

/-- Finite coordinate coverage supplies the proof-only span used by the linear-time
locator; the locator still selects its own retained payloads.

The two coordinate membership witnesses retain actual source entries. Their
strict outer order and closed query bounds supply the same span certificate. -/
public theorem spanned_of_keys {Alpha : Type} (key : Alpha → Fraction.Rational) (entries : List Alpha)
    {lower upper point : Fraction.Rational} (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map
      key)
    (strict : lower < upper) (inside : lower ≤ point ∧ point ≤ upper) : Geometry.Grid.ClearGridCoverage.Interval.Spanned
      (key := key) entries point := by
  rcases Data.List.Map.mem_map.mp lowerMember with ⟨left, leftMember, leftEq⟩
  rcases Data.List.Map.mem_map.mp upperMember with ⟨right, rightMember, rightEq⟩
  exact ⟨left, leftMember, right, rightMember, by simpa only [leftEq, rightEq] using strict,
    by simpa only [leftEq] using inside.1, by simpa only [rightEq] using inside.2⟩

/-- Locate a rational point of any retained branch box in the common grid. This
scans the axes only; it does not allocate the entire grid-cell list.

The original state has a proper box containing the supplied point. Its retained
endpoint occurrences give the two spans used by the existing axis locator. -/
@[expose] public def locateInState (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient))
    (state : Geometry.Grid.FromStates.BranchState polynomial ambient) (member : state ∈ states) (point :
      Gaussian.Basic.Canonical)
    (inside : state.box.Contains point) : ClearGridCoverage.Located
      (ofStates states) point :=
  let horizontal := ofStates_x_bounds states member
  let vertical := ofStates_y_bounds states member
  ClearGridCoverage.locate (ofStates states) point
    (spanned_of_keys _ _ horizontal.1 horizontal.2 state.proper.1 ⟨inside.1, inside.2.1⟩)
    (spanned_of_keys _ _ vertical.1 vertical.2 state.proper.2 inside.2.2)

/-- Membership in the actual stored coordinate bank, not a fresh grid computed
independently for each path.

Both coordinate occurrences belong to the same original grid. The predicate
retains the stored vertical and horizontal coordinate banks. -/
@[expose] public def ContainsVertex (grid : ClearGrid polynomial ambient) (point :
  Gaussian.Basic.Canonical) : Prop :=
  point.re ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate ∧ point.im ∈ grid.horizontal.map
    Geometry.Grid.ClearGrid.HorizontalLine.coordinate

/-- Every vertex of the displayed clear path belongs to the retained grid
coordinate banks.

The recursive predicate includes both the start and the final endpoint and
keeps the path's original clearance owner. -/
@[expose] public def ContainsPathVertices (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box} :
    {start finish : Gaussian.Basic.Canonical} → ClearPath polynomial pathAmbient start finish → Prop
  | _, _, .nil point => ContainsVertex grid point
  | start, _, .cons _ tail => ContainsVertex grid start ∧
    ContainsPathVertices grid tail

namespace ContainsPathVertices

/-- The start vertex belongs to the grid whenever all vertices of the retained
clear path do.

The original predicate includes the initial endpoint in either path
constructor. Reading that retained certificate keeps the same grid and point. -/
public theorem start (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box} :
    ∀ {start finish : Gaussian.Basic.Canonical} (path : ClearPath polynomial pathAmbient start
      finish),
      ContainsPathVertices grid path → ContainsVertex grid
        start
  | _, _, .nil _, member => member
  | _, _, .cons _ _, member => member.1

end ContainsPathVertices

namespace ContainsPathVertices

/-- Concatenating two paths whose vertices belong to the retained grid preserves
that membership.

Both input predicates use the same retained coordinate banks. Structural path
recursion keeps the original first-path vertices followed by the second path. -/
public theorem append (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box} :
    ∀ {start middle finish : Gaussian.Basic.Canonical} (first : ClearPath polynomial pathAmbient
      start middle)
      (second : ClearPath polynomial pathAmbient middle finish),
      ContainsPathVertices grid first → ContainsPathVertices
        grid second → ContainsPathVertices grid (first.append second)
  | _, _, _, .nil _, _, _, second => second
  | _, _, _, .cons _ tail, second, firstOn, secondOn =>
      ⟨firstOn.1, append grid tail second
        firstOn.2 secondOn⟩

end ContainsPathVertices

namespace ContainsPathVertices

/-- Reversing a retained clear path preserves membership of all its vertices in the
same grid.

The reversed path uses the same original segment endpoints. The retained start
and tail certificates supply membership in the unchanged grid banks. -/
public theorem reverse (grid : ClearGrid polynomial ambient) {pathAmbient :
  Box} :
    ∀ {start finish : Gaussian.Basic.Canonical} (path : ClearPath polynomial pathAmbient start
      finish),
      ContainsPathVertices grid path → ContainsPathVertices
        grid (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse path)
  | _, _, .nil _, member => member
  | _, _, .cons head tail, member =>
      append grid
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse tail)
        (.cons (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse head) (.nil _))
        (reverse grid tail member.2)
        ⟨start grid tail member.2, member.1⟩

end ContainsPathVertices

/-- The anchor of each retained branch state is a vertex of the common grid.

The anchor uses the original state box lower coordinates. Their two retained
side occurrences certify that same grid vertex. -/
public theorem ofStates_anchor (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient))
    {state : Geometry.Grid.FromStates.BranchState polynomial ambient} (member : state ∈ states) :
    ContainsVertex (ofStates states) state.box.anchor :=
  ⟨(ofStates_x_bounds states member).1, (ofStates_y_bounds
    states member).1⟩

/-- Every actual branch-boundary corner belongs to the common grid, even though its
original clearance certificates use the smaller owner box.

The four original branch-box corners use its retained lower and upper endpoint
occurrences. Their common-grid memberships keep the original boundary path
owner. -/
public theorem ofStates_boundary (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient))
    {state : Geometry.Grid.FromStates.BranchState polynomial ambient} (member : state ∈ states) :
    ContainsPathVertices (ofStates states)
      (Curves.Hyperelliptic.Branches.BranchCutLifts.ownerBoundaryPath state) :=
  let horizontal := ofStates_x_bounds states member
  let vertical := ofStates_y_bounds states member
  ⟨⟨horizontal.1, vertical.1⟩, ⟨horizontal.2, vertical.1⟩,
    ⟨horizontal.2, vertical.2⟩, ⟨horizontal.1, vertical.2⟩, horizontal.1, vertical.1⟩

end Grid

end Purelib.Polynomial.Geometry.Grid.FromStates
