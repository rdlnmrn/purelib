module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
public import Purelib.Riemann.Periods.StandardPeriodGridLines
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

public section

/-!
# Regular incident faces for original standard-period fragments

A fragment on a certified grid line lies on a complete adjacent grid edge.
Select that edge's already proved regular incident face, even if the initial
midpoint locator selected a branch hole. The original oriented fragment
endpoints and their rational positions on the complete edge are retained.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PuncturedVertexStars

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.PuncturedEdgeFaces

open Purelib.Polynomial.Geometry.ClearPath.ClearSegment (pointAt_eq_line)

open Purelib.Riemann.Periods.StandardPeriodGridLines

open Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval HorizontalLine VerticalLine)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell
  PrimitiveFragmentCells LocatedPrimitiveSplits)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {ambient : Rational.Box} {grid : ClearGrid
    curve.polynomial ambient} {axes :
    PrimitiveAxes grid}
  {parent : CenteredEdge curve source} {cuts : List Rational} {partition :
    Partition 0 1 cuts}
  {interval : PreparedAxisPartitions.Interval}

set_option genInjectivity false in
/-- The point may be internal to the complete grid edge or one of its endpoints. Its parameter is certified, not
inferred from a shared coordinate.

Its original closed-unit parameter identifies the point on the retained edge.
Both endpoint positions are permitted and retain their supplied coordinates. -/
structure EdgePoint {start finish : Data.Gaussian.Basic.Canonical} (edge : Edge grid start finish) (point :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained rational location on the original complete grid edge. -/ parameter : Fraction.Rational
  /-- The retained edge parameter lies in the original closed unit interval. -/ inside : 0 ≤ parameter ∧ parameter ≤ 1
  /-- The original complete edge evaluates at the retained parameter to the requested point. -/ point_eq :
    edge.segment.pointAt parameter = point

constructive_injectivity EdgePoint

namespace EdgePoint

/-- Retain the exact normalized position of an original point on its complete horizontal grid edge. -/
@[expose] def horizontal (span : Grid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient
  := ambient)))
    (adjacent : span ∈ grid.xIntervals) (line : HorizontalLine curve.polynomial ambient) (member : line ∈
      grid.horizontal)
    (point : Data.Gaussian.Basic.Canonical) (inside : span.lower.coordinate ≤ point.re ∧ point.re ≤
      span.upper.coordinate)
    (fixed : point.im = line.coordinate) : EdgePoint
      (Edge.horizontal span adjacent line member) point := by
  let parameter := (point.re - span.lower.coordinate) / (span.upper.coordinate - span.lower.coordinate)
  have identity : parameter * (span.upper.coordinate - span.lower.coordinate) = point.re - span.lower.coordinate :=
    Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt (Fraction.Order.Arithmetic.sub_pos_direct span.ordered))
  refine ⟨parameter, Fraction.Order.Field.fraction_inside span.ordered inside, ?_⟩
  apply Data.Gaussian.Basic.ext
  · change span.lower.coordinate + parameter * (span.upper.coordinate - span.lower.coordinate) = point.re
    rw [identity]
    ring1
  · change line.coordinate + parameter * (line.coordinate - line.coordinate) = point.im
    rw [fixed]
    ring1

/-- Retain the exact normalized position of an original point on its complete vertical grid edge. -/
@[expose] def vertical (span : Grid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient
  := ambient)))
    (adjacent : span ∈ grid.yIntervals) (line : VerticalLine curve.polynomial ambient) (member : line ∈
      grid.vertical)
    (point : Data.Gaussian.Basic.Canonical) (inside : span.lower.coordinate ≤ point.im ∧ point.im ≤
      span.upper.coordinate)
    (fixed : point.re = line.coordinate) : EdgePoint
      (Edge.vertical span adjacent line member) point := by
  let parameter := (point.im - span.lower.coordinate) / (span.upper.coordinate - span.lower.coordinate)
  have identity : parameter * (span.upper.coordinate - span.lower.coordinate) = point.im - span.lower.coordinate :=
    Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt (Fraction.Order.Arithmetic.sub_pos_direct span.ordered))
  refine ⟨parameter, Fraction.Order.Field.fraction_inside span.ordered inside, ?_⟩
  apply Data.Gaussian.Basic.ext
  · change line.coordinate + parameter * (line.coordinate - line.coordinate) = point.re
    rw [fixed]
    ring1
  · change span.lower.coordinate + parameter * (span.upper.coordinate - span.lower.coordinate) = point.im
    rw [identity]
    ring1

/-- An original point on a retained edge belongs to every box containing both original edge endpoints. -/
theorem contained {start finish point : Data.Gaussian.Basic.Canonical} {edge : Edge grid start finish} (location :
  EdgePoint edge point)
    {box : Rational.Box} (first : box.Contains start) (last : box.Contains finish) : box.Contains point
      := by
  rw [← location.point_eq, pointAt_eq_line]
  exact Rational.Box.contains_line first last location.inside

end EdgePoint

set_option genInjectivity false in
/-- A retained complete original grid edge with certified positions of both oriented source-fragment endpoints.

The retained edge carries certified parameters for both original fragment
endpoints; it does not substitute a new fragment or reverse their order. -/
structure FragmentGridEdge (fragment : PrimitiveFragmentCell axes parent partition interval) where
  /-- The original complete grid edge starting point. -/ start : Data.Gaussian.Basic.Canonical
  /-- The original complete grid edge finishing point. -/ finish : Data.Gaussian.Basic.Canonical
  /-- The retained complete original grid edge containing the source fragment. -/ edge : Edge grid start finish
  /-- The retained parameter identifying the original fragment start on the complete edge. -/ first :
    EdgePoint edge fragment.first
  /-- The retained parameter identifying the original fragment finish on the complete edge. -/ last :
    EdgePoint edge fragment.last

constructive_injectivity FragmentGridEdge

namespace FragmentGridEdge

/-- The original member cell's horizontal and vertical intervals belong to the corresponding retained grid lists.

The original cell occurrence splits into its retained horizontal and vertical
interval memberships, without searching either coordinate list again. -/
theorem cell_intervals {cell : Cell curve.polynomial ambient} (member : cell ∈ grid.cells) :
    cell.horizontal ∈ grid.xIntervals ∧ cell.vertical ∈ grid.yIntervals := by
  obtain ⟨horizontal, xMember, row⟩ := Flatten.mem_flatMap.mp member
  obtain ⟨vertical, yMember, rfl⟩ := Map.mem_map.mp row
  exact ⟨xMember, yMember⟩

/-- Reuse the located cell's adjacent interval and the actual source line. The fragment keeps its original direction
through its two edge parameters. -/
@[expose] def build (fragment : PrimitiveFragmentCell axes parent partition interval) (onLine :
  ParentOnLine grid parent) :
    FragmentGridEdge fragment := by
  let intervals := cell_intervals
    fragment.cell_member
  if horizontal : (parent.edge.point 0).im ∈ grid.horizontal.map HorizontalLine.coordinate ∧
      (parent.edge.point 1).im = (parent.edge.point 0).im then
    let line := AxisWalks.lookup (parent.edge.point 0).im grid.horizontal horizontal.1
    let edge := Edge.horizontal fragment.cell.horizontal intervals.1 line.entry line.member
    have firstFixed : fragment.first.im = line.entry.coordinate := by
      rw [fragment.first_eq]
      exact (ParentOnLine.horizontal parent horizontal.2 _).trans line.coordinate_eq.symm
    have lastFixed : fragment.last.im = line.entry.coordinate := by
      rw [fragment.last_eq]
      exact (ParentOnLine.horizontal parent horizontal.2 _).trans line.coordinate_eq.symm
    exact ⟨_, _, edge, EdgePoint.horizontal _
      intervals.1 line.entry line.member fragment.first
      ⟨fragment.first_inside.1, fragment.first_inside.2.1⟩ firstFixed,
      EdgePoint.horizontal _ intervals.1 line.entry
        line.member fragment.last
        ⟨fragment.last_inside.1, fragment.last_inside.2.1⟩ lastFixed⟩
  else
    have vertical := onLine.resolve_left horizontal
    let line := AxisWalks.lookup (parent.edge.point 0).re grid.vertical vertical.1
    let edge := Edge.vertical fragment.cell.vertical intervals.2 line.entry line.member
    have firstFixed : fragment.first.re = line.entry.coordinate := by
      rw [fragment.first_eq]
      exact (ParentOnLine.vertical parent vertical.2 _).trans line.coordinate_eq.symm
    have lastFixed : fragment.last.re = line.entry.coordinate := by
      rw [fragment.last_eq]
      exact (ParentOnLine.vertical parent vertical.2 _).trans line.coordinate_eq.symm
    exact ⟨_, _, edge, EdgePoint.vertical _ intervals.2
      line.entry line.member fragment.first
      ⟨fragment.first_inside.2.2.1, fragment.first_inside.2.2.2⟩ firstFixed,
      EdgePoint.vertical _ intervals.2 line.entry
        line.member fragment.last
        ⟨fragment.last_inside.2.2.1, fragment.last_inside.2.2.2⟩ lastFixed⟩

/-- A grid edge uses the containing cell's actual interval in its varying coordinate. -/
private def sameIntervals (cell : Cell curve.polynomial ambient) :
    {start finish : Gaussian} → Edge grid start finish → Prop
  | _, _, .horizontal span _ _ _ => span = cell.horizontal
  | _, _, .vertical span _ _ _ => span = cell.vertical
  | _, _, .reverse edge => sameIntervals cell edge

/-- The original fragment-edge factory preserves the located cell's varying interval. -/
private theorem build_sameIntervals (fragment : PrimitiveFragmentCell axes parent partition interval)
    (onLine : ParentOnLine grid parent) : sameIntervals fragment.cell (build fragment onLine).edge := by
  unfold build
  dsimp only
  by_cases horizontal : (parent.edge.point 0).im ∈ grid.horizontal.map HorizontalLine.coordinate ∧
      (parent.edge.point 1).im = (parent.edge.point 0).im
  · rewrite [dif_pos horizontal]
    rfl
  · rewrite [dif_neg horizontal]
    rfl

/-- Read a containing cell from a cached edge's own line and interval payload, including reversal. -/
private def containingCell (cell : Cell curve.polynomial ambient)
    (horizontalMember : cell.horizontal ∈ grid.xIntervals) (verticalMember : cell.vertical ∈ grid.yIntervals) :
    {start finish : Gaussian} → (edge : Edge grid start finish) → sameIntervals cell edge →
    (point : Gaussian) → (parameter : Rational) → edge.segment.pointAt parameter = point →
    cell.box.Contains point → {geometry : EdgeSides.EdgeCell grid start finish // geometry.cell = cell}
  | _, _, .horizontal span _ line member => fun same point parameter pointEq inside => by
      cases same
      have fixed : point.im = line.coordinate := by
        have equal := congrArg (fun value : Gaussian => value.im) pointEq
        change line.coordinate + parameter * (line.coordinate - line.coordinate) = point.im at equal
        have scalar : line.coordinate + parameter * (line.coordinate - line.coordinate) = line.coordinate := by
          ring1
        exact equal.symm.trans scalar
      have lineInside : cell.vertical.lower.coordinate ≤ line.coordinate ∧
          line.coordinate ≤ cell.vertical.upper.coordinate := by
        rewrite [← fixed]
        exact inside.2.2
      exact EdgeSides.EdgeCell.horizontalInCell cell.horizontal horizontalMember cell.vertical verticalMember
        line member lineInside
  | _, _, .vertical span _ line member => fun same point parameter pointEq inside => by
      cases same
      have fixed : point.re = line.coordinate := by
        have equal := congrArg (fun value : Gaussian => value.re) pointEq
        change line.coordinate + parameter * (line.coordinate - line.coordinate) = point.re at equal
        have scalar : line.coordinate + parameter * (line.coordinate - line.coordinate) = line.coordinate := by
          ring1
        exact equal.symm.trans scalar
      have lineInside : cell.horizontal.lower.coordinate ≤ line.coordinate ∧
          line.coordinate ≤ cell.horizontal.upper.coordinate := by
        rewrite [← fixed]
        exact ⟨inside.1, inside.2.1⟩
      exact EdgeSides.EdgeCell.verticalInCell cell.vertical verticalMember cell.horizontal horizontalMember
        line member lineInside
  | _, _, .reverse edge => fun same point parameter pointEq inside =>
      let previous := containingCell cell horizontalMember verticalMember edge same point (1 - parameter)
        ((Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_pointAt edge.segment parameter).symm.trans
          pointEq) inside
      ⟨previous.val.reverse, previous.property⟩

/-- Attach the once-built fragment edge to the SAME located cell using its complete factory identity.

The executable branch consumes the supplied edge's cached line and interval
payloads. Its factory equality supplies only erased interval-incidence
evidence; the original edge factory and axis lookup are not run again. -/
def selectedCell (fragment : PrimitiveFragmentCell axes parent partition interval)
    (onLine : ParentOnLine grid parent) (retained : FragmentGridEdge fragment)
    (retained_eq : retained = build fragment onLine) :
    {geometry : EdgeSides.EdgeCell grid retained.start retained.finish // geometry.cell = fragment.cell} := by
  have same : sameIntervals fragment.cell retained.edge :=
    Eq.mpr (congrArg (fun value : FragmentGridEdge fragment => sameIntervals fragment.cell value.edge) retained_eq)
      (build_sameIntervals fragment onLine)
  let intervals := cell_intervals fragment.cell_member
  exact containingCell fragment.cell intervals.1 intervals.2 retained.edge same fragment.first
    retained.first.parameter retained.first.point_eq fragment.first_inside

end FragmentGridEdge

variable {branches : Branches.BranchIsolation.Data curve} {higher : 1 <
  curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve branches higher}

set_option genInjectivity false in
/-- A regular incident face contains the original fragment endpoints.

The retained incident face contains both original fragment endpoints.
The selected edge and its position certificates preserve the original direction. -/
structure RegularPrimitiveFragment (axes : PrimitiveAxes base.bank.grid) (parent :
  CenteredEdge curve source)
    {cuts : List Rational} (partition : Partition 0 1 cuts) (interval :
      PreparedAxisPartitions.Interval) where
  /-- The original source fragment with its cached grid cell and endpoint positions. -/ located :
    PrimitiveFragmentCell axes parent partition interval
  /-- The retained complete original grid edge containing the fragment endpoints. -/ source :
    FragmentGridEdge located
  /-- The retained certified regular face incident to the complete original edge. -/ face :
    RegularEdgeCell base source.start source.finish
  /-- The original oriented fragment start belongs to the selected regular face. -/ first_inside :
    face.geometry.cell.box.Contains located.first
  /-- The original oriented fragment finish belongs to the same selected regular face. -/ last_inside :
    face.geometry.cell.box.Contains located.last

constructive_injectivity RegularPrimitiveFragment

namespace RegularPrimitiveFragment

variable {axes : PrimitiveAxes base.bank.grid}
  {parent : CenteredEdge curve source}
  {cuts : List Rational} {partition : Partition 0 1 cuts}
    {interval : PreparedAxisPartitions.Interval}

/-- Select the original complete edge's retained regular incident face and certify both original fragment endpoints
inside it. -/
@[expose] def build (located : PrimitiveFragmentCell axes parent partition interval)
    (onLine : ParentOnLine base.bank.grid parent) :
      RegularPrimitiveFragment axes parent partition
      interval :=
  let source := FragmentGridEdge.build located onLine
  let star := VertexStar.build base source.start source.edge.vertices.1
  let face := RegularEdgeCell.acquire star source.edge
  ⟨located, source, face,
    source.first.contained face.geometry.first.corner.contains face.geometry.last.corner.contains,
    source.last.contained face.geometry.first.corner.contains face.geometry.last.corner.contains⟩

/-- Retain an existing selected regular location on the same once-built fragment edge and geometric cell.

Only the exact cell equality transports the original RegularLocation. The
source fragment, its endpoint parameters and its actual selected payload
remain inputs; no star, incident-face lookup or root classification runs. -/
@[expose] def ofSelectedCell (located : PrimitiveFragmentCell axes parent partition interval)
    (retained : FragmentGridEdge located)
    (selected : {geometry : EdgeSides.EdgeCell base.bank.grid retained.start retained.finish //
      geometry.cell = located.cell})
    (location : PuncturedGridFaces.RegularLocation base.faces.regulars located.cell) :
    RegularPrimitiveFragment axes parent partition interval :=
  ⟨located, retained,
    ⟨selected.val,
      Eq.mpr (congrArg (fun cell => PuncturedGridFaces.RegularLocation base.faces.regulars cell)
        selected.property) location⟩,
    Eq.mpr (congrArg (fun cell => cell.box.Contains located.first) selected.property) located.first_inside,
    Eq.mpr (congrArg (fun cell => cell.box.Contains located.last) selected.property) located.last_inside⟩

/-- The selected-cell construction retains the complete original located fragment. -/
theorem ofSelectedCell_located (located : PrimitiveFragmentCell axes parent partition interval)
    (retained : FragmentGridEdge located)
    (selected : {geometry : EdgeSides.EdgeCell base.bank.grid retained.start retained.finish //
      geometry.cell = located.cell})
    (location : PuncturedGridFaces.RegularLocation base.faces.regulars located.cell) :
    (ofSelectedCell located retained selected location).located = located := rfl

/-- The selected-cell construction retains the complete original fragment-edge cache. -/
theorem ofSelectedCell_source (located : PrimitiveFragmentCell axes parent partition interval)
    (retained : FragmentGridEdge located)
    (selected : {geometry : EdgeSides.EdgeCell base.bank.grid retained.start retained.finish //
      geometry.cell = located.cell})
    (location : PuncturedGridFaces.RegularLocation base.faces.regulars located.cell) :
    (ofSelectedCell located retained selected location).source = retained := rfl

/-- The regular-face payload remains the same original selected location under its exact cell-index transport. -/
theorem ofSelectedCell_location_heq (located : PrimitiveFragmentCell axes parent partition interval)
    (retained : FragmentGridEdge located)
    (selected : {geometry : EdgeSides.EdgeCell base.bank.grid retained.start retained.finish //
      geometry.cell = located.cell})
    (location : PuncturedGridFaces.RegularLocation base.faces.regulars located.cell) :
    HEq (ofSelectedCell located retained selected location).face.located location := by
  have transported {First Last : Sort _} (equal : First = Last) (value : Last) :
      HEq (Eq.mpr equal value) value := by
    cases equal
    rfl
  exact transported
    (congrArg (fun cell => PuncturedGridFaces.RegularLocation base.faces.regulars cell) selected.property) location

end RegularPrimitiveFragment

set_option genInjectivity false in
/-- Regular incident faces aligned with the original interval list.

The recursive certificate aligns each original interval and fragment with
its retained incident face, preserving the source partition order. -/
inductive RegularPrimitiveFragments (axes : PrimitiveAxes base.bank.grid) (parent :
  CenteredEdge curve source)
    (partition : Partition 0 1 (axes.parameters parent)) : List PreparedAxisPartitions.Interval →
      Type
  /-- The empty original fragment list retains no regular faces. -/ | nil :
    RegularPrimitiveFragments axes parent
    partition []
  /-- Retain the original head fragment's regular face followed by the exact fragment tail. -/ | cons {interval :
    PreparedAxisPartitions.Interval} {intervals : List PreparedAxisPartitions.Interval}
      (head : RegularPrimitiveFragment axes parent
        partition interval) (tail :
        RegularPrimitiveFragments axes parent
        partition intervals) :
      RegularPrimitiveFragments axes parent
        partition (interval :: intervals)

constructive_injectivity RegularPrimitiveFragments

namespace RegularPrimitiveFragments

variable {axes : PrimitiveAxes base.bank.grid}
  {parent : CenteredEdge curve source}
  {partition : Partition 0 1 (axes.parameters parent)}

/-- Assign a retained regular incident face to each original located fragment without changing its endpoint order. -/
@[expose] def build (onLine : ParentOnLine base.bank.grid parent) :
    ∀ {intervals : List PreparedAxisPartitions.Interval}, PrimitiveFragmentCells axes parent
      partition intervals →
      RegularPrimitiveFragments axes parent partition
        intervals
  | _, .nil => .nil
  | _, .cons head tail => .cons
    (RegularPrimitiveFragment.build (base := base) head
    onLine) (build
    onLine tail)

end RegularPrimitiveFragments

set_option genInjectivity false in
/-- Regular incident faces aligned with the original splitting spine.

The recursive certificate follows the retained parent and fragment spines.
Every chosen incident face keeps its original owner and endpoint positions. -/
inductive RegularPrimitiveSplits (axes : PrimitiveAxes base.bank.grid) :
    {parents : List (CenteredEdge curve source)} → PrimitiveSplits
      axes parents → Type
  /-- The empty original parent splitting retains no regular fragment faces. -/ | nil :
    RegularPrimitiveSplits axes .nil
  /-- Retain the original head parent's regular fragment faces followed by the exact original splitting tail. -/ | cons
    {parent : CenteredEdge curve source} {parents : List
    (CenteredEdge curve source)}
      {partition : Partition 0 1 (axes.parameters parent)} {splits :
        PrimitiveSplits axes parents}
      (head : RegularPrimitiveFragments axes parent
        partition partition.intervals) (tail :
        RegularPrimitiveSplits axes splits) :
      RegularPrimitiveSplits axes (.cons
        partition splits)

constructive_injectivity RegularPrimitiveSplits

namespace RegularPrimitiveSplits

variable {axes : PrimitiveAxes base.bank.grid}

/-- Assign regular incident faces throughout the original located splitting using its retained source grid-line
certificates. -/
@[expose] def build :
    ∀ {parents : List (CenteredEdge curve source)} {splits :
      PrimitiveSplits axes parents},
      LocatedPrimitiveSplits axes splits → ParentsOnLines base.bank.grid parents →
        RegularPrimitiveSplits axes splits
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, onLines =>
      .cons (RegularPrimitiveFragments.build (base :=
        base) onLines.1 head)
        (build tail
        onLines.2)

end RegularPrimitiveSplits
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
