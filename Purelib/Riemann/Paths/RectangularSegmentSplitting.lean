module
meta import Purelib.Elab.ConstructiveInjectivity
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Data.List.OfFn.Basic
public import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Total cell-contained fragments of actual affine geometry

One cache of grid cuts serves any number of edges. Each split retains its
parameter partition, containing-cell assignments and endpoint coordinates.
The finite walk proves coverage and telescoping for any primitive whatsoever;
splitting does not select another polynomial or change a prepared request.
-/

public section

namespace Purelib.Riemann.Paths.RectangularSegmentSplitting

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial
open Purelib.Data.Gaussian

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Axis)
open Purelib.Riemann.Integration
open Purelib.Riemann.Branches
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (point crossings)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {columns rows : Nat}

set_option genInjectivity false in
/-- Cached coordinate cut lists for the original ordered rectangular axes.

The exact list equations retain every original axis coordinate in order, including the outer endpoints. -/
structure GridCuts (geometry : Geometry columns rows) where
  /-- The cached original horizontal-axis coordinate list. -/ x : List Coordinate
  /-- The horizontal cache equals the exact original finite axis vector readback. -/ x_eq : x = List.ofFn
    geometry.x.coordinates
  /-- The cached original vertical-axis coordinate list. -/ y : List Coordinate
  /-- The vertical cache equals the exact original finite axis vector readback. -/ y_eq : y = List.ofFn
    geometry.y.coordinates

constructive_injectivity GridCuts

namespace GridCuts

/-- Cache the exact horizontal and vertical coordinate lists of the original geometry. -/
@[expose] def build (geometry : Geometry columns rows) : GridCuts geometry :=
  ⟨List.ofFn geometry.x.coordinates, rfl, List.ofFn geometry.y.coordinates, rfl⟩

variable {geometry : Geometry columns rows}

/-- Every original horizontal-axis coordinate belongs to the retained cut list. -/
theorem x_mem (cuts : GridCuts geometry) (index : Fin (columns + 2)) : geometry.x.coordinates index ∈ cuts.x := by
  rw [cuts.x_eq]
  exact OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-- Every original vertical-axis coordinate belongs to the retained cut list. -/
theorem y_mem (cuts : GridCuts geometry) (index : Fin (rows + 2)) : geometry.y.coordinates index ∈ cuts.y := by
  rw [cuts.y_eq]
  exact OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-- The ordered concatenation of horizontal and vertical crossing parameters for the original segment. -/
@[expose] def parameters (cuts : GridCuts geometry) (first last : Gaussian) : List Coordinate :=
  PreparedSegmentCuts.crossings first.re (last.re - first.re) cuts.x ++ PreparedSegmentCuts.crossings first.im (last.im
    - first.im) cuts.y

/-- The original segment's crossing-parameter list has at most columns plus rows plus four entries. -/
theorem parameters_length (cuts : GridCuts geometry) (first last : Gaussian) :
    (cuts.parameters first last).length ≤ columns + rows + 4 := by
  have horizontal := PreparedSegmentCuts.crossings_length first.re (last.re - first.re) cuts.x
  have vertical := PreparedSegmentCuts.crossings_length first.im (last.im - first.im) cuts.y
  have xLength : cuts.x.length = columns + 2 := by rw [cuts.x_eq, OfFn.Basic.length_ofFn]
  have yLength : cuts.y.length = rows + 2 := by rw [cuts.y_eq, OfFn.Basic.length_ofFn]
  rw [xLength] at horizontal
  rw [yLength] at vertical
  unfold parameters
  rw [Append.length_append]
  omega

end GridCuts

namespace Geometry

/-- The point lies between the original rectangular axes' first and last coordinates. -/
@[expose] def Covers (geometry : Geometry columns rows) (point : Gaussian) : Prop :=
  geometry.x.coordinates 0 ≤ point.re ∧ point.re ≤ geometry.x.coordinates (Fin.last (columns + 1)) ∧
    geometry.y.coordinates 0 ≤ point.im ∧ point.im ≤ geometry.y.coordinates (Fin.last (rows + 1))

/-- A point in the original proper box is covered by its exact uniform rectangular geometry. -/
theorem uniform_covers (box : Box) (proper : box.Proper) (steps : Nat) {point : Gaussian}
    (inside : box.Contains point) : Geometry.Covers (Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform box
        proper steps) point
      := by
  change (RectangularUniformGeometry.Axis.uniform steps _ _ proper.1).coordinates 0 ≤ point.re ∧
    point.re ≤ (RectangularUniformGeometry.Axis.uniform steps _ _ proper.1).coordinates (Fin.last (steps + 1)) ∧
    (RectangularUniformGeometry.Axis.uniform steps _ _ proper.2).coordinates 0 ≤ point.im ∧
    point.im ≤ (RectangularUniformGeometry.Axis.uniform steps _ _ proper.2).coordinates (Fin.last (steps + 1))
  rw [RectangularUniformGeometry.Axis.uniform_first, RectangularUniformGeometry.Axis.uniform_last,
    RectangularUniformGeometry.Axis.uniform_first, RectangularUniformGeometry.Axis.uniform_last]
  exact inside

/-- The original grid coverage contains every unit-interval point between two covered segment endpoints. -/
theorem covers_point (geometry : Geometry columns rows) {first last : Gaussian}
    (firstInside : Geometry.Covers geometry first) (lastInside : Geometry.Covers geometry last)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    Geometry.Covers geometry (point first last parameter) := by
  let box : Box := ⟨geometry.x.coordinates 0, geometry.x.coordinates (Fin.last (columns + 1)),
    geometry.y.coordinates 0, geometry.y.coordinates (Fin.last (rows + 1)),
    firstInside.1.trans firstInside.2.1, firstInside.2.2.1.trans firstInside.2.2.2⟩
  have contained : box.Contains (Affine.line first (last - first) parameter) :=
    Box.contains_line (box := box) (start := first) (finish := last) firstInside lastInside inside
  rw [← PreparedSegmentCuts.point_eq_line] at contained
  exact contained

end Geometry

set_option genInjectivity false in
/-- A retained parameter interval and original cell containing the segment's exact interval endpoints.

The original segment endpoints remain indices, and both stored point equations preserve their exact parameter readbacks.
-/
structure SegmentPiece (geometry : Geometry columns rows) (first last : Gaussian) where
  /-- The retained original positive parameter interval. -/ interval : PreparedAxisPartitions.Interval
  /-- The retained interval lies inside the original unit parameter range. -/ within : 0 ≤ interval.lower ∧
    interval.upper ≤ 1
  /-- The original containing cell-column index. -/ column : Fin (columns + 1)
  /-- The original containing cell-row index. -/ row : Fin (rows + 1)
  /-- The cached original segment point at the retained interval's lower endpoint. -/ firstPoint : Gaussian
  /-- The first-point cache equals its exact original parameter readback. -/ first_eq : firstPoint = point first last
    interval.lower
  /-- The cached original segment point at the retained interval's upper endpoint. -/ lastPoint : Gaussian
  /-- The last-point cache equals its exact original parameter readback. -/ last_eq : lastPoint = point first last
    interval.upper
  /-- The retained first point belongs to the exact stored cell. -/ first_inside : (geometry.box column row).Contains
    firstPoint
  /-- The retained last point belongs to the exact stored cell. -/ last_inside : (geometry.box column row).Contains
    lastPoint

constructive_injectivity SegmentPiece

/-- Every parameter in a retained segment piece lies in that piece's original cell box. -/
theorem SegmentPiece.contains_query {geometry : Geometry columns rows} {first last : Gaussian}
    (piece : SegmentPiece geometry first last) (parameter : Coordinate)
    (inside : piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper) :
    (geometry.box piece.column piece.row).Contains (point first last parameter) := by
  let fraction := (parameter - piece.interval.lower) / (piece.interval.upper - piece.interval.lower)
  have positive : 0 < piece.interval.upper - piece.interval.lower := Fraction.Order.Arithmetic.sub_pos_direct
    piece.interval.ordered
  have nonnegative : 0 ≤ fraction := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1) positive.le
  have bounded : fraction ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos positive).mpr
    rw [one_mul]
    exact Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 _
  have equal : piece.interval.lower + fraction * (piece.interval.upper - piece.interval.lower) = parameter := by
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne']
    ring1
  have contained := Box.contains_line piece.first_inside piece.last_inside ⟨nonnegative, bounded⟩
  rw [piece.first_eq,
      piece.last_eq, ← PreparedSegmentCuts.point_eq_line, ← PreparedSegmentCuts.point_affine, equal] at contained
  exact contained

namespace GridCuts

variable {geometry : Geometry columns rows} {first last : Gaussian}

/-- A partition interval with a cell-contained midpoint has both endpoint coordinates in that same original axis cell.

All crossings of the original cell boundaries are present in the retained partition, so the interval cannot cross either
boundary internally. -/
theorem axis_bounds {steps : Nat} (axis : Axis steps) {axisCuts parameters : List Coordinate}
    (present : ∀ index, axis.coordinates index ∈ axisCuts)
    (partition : Geometry.Rectangle.AxisPartition 0 1 parameters) {interval : PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) (start velocity : Coordinate)
    (included : ∀ parameter ∈ PreparedSegmentCuts.crossings start velocity axisCuts, parameter ∈ parameters)
    (index : Fin (steps + 1))
    (inside : axis.coordinates index.castSucc ≤ start + ((interval.lower + interval.upper) / 2) * velocity ∧
      start + ((interval.lower + interval.upper) / 2) * velocity ≤ axis.coordinates index.succ) :
    (axis.coordinates index.castSucc ≤ start + interval.lower * velocity ∧
      start + interval.lower * velocity ≤ axis.coordinates index.succ) ∧
    (axis.coordinates index.castSucc ≤ start + interval.upper * velocity ∧
      start + interval.upper * velocity ≤ axis.coordinates index.succ) := by
  apply PreparedSegmentCuts.coordinate_bounds partition member start velocity _ _ ?_ inside
  intro cut cutMember parameter parameterMember
  apply included parameter
  apply PreparedSegmentCuts.crossings_mono start velocity (last := axisCuts) ?_ parameter parameterMember
  intro value valueMember
  have equal : value = cut := Membership.mem_singleton.mp valueMember
  subst value
  rcases Membership.mem_cons.mp cutMember with rfl | member
  · exact present index.castSucc
  · have equal := Membership.mem_singleton.mp member
    rw [equal]
    exact present index.succ

/-- Assign an original partition interval to the cells located at its exact midpoint.

The retained coordinate cuts certify both endpoint bounds in those same cells, preserving the original interval and
point equations. -/
@[expose] def assign (cuts : GridCuts geometry) (firstInside : Geometry.Covers geometry first) (lastInside :
  Geometry.Covers geometry last)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (cuts.parameters first last))
    (interval : PreparedAxisPartitions.Interval) (member : interval ∈ partition.intervals) : SegmentPiece geometry first
      last := by
  let middle := point first last ((interval.lower + interval.upper) / 2)
  have within := partition.interval_bounds member
  have midpoint := PreparedSegmentCuts.midpoint_bounds interval
  have middleInside := Geometry.covers_point geometry firstInside lastInside
    ⟨within.1.trans midpoint.1.le, midpoint.2.le.trans within.2⟩
  let horizontal := RectangularUniformGeometry.Axis.locate
    geometry.x middle.re middleInside.1 middleInside.2.1
  let vertical := RectangularUniformGeometry.Axis.locate
    geometry.y middle.im middleInside.2.2.1 middleInside.2.2.2
  have xBound := axis_bounds geometry.x cuts.x_mem partition member first.re (last.re - first.re)
    (fun _ member => List.mem_append_left _ member) horizontal.index horizontal.inside
  have yBound := axis_bounds geometry.y cuts.y_mem partition member first.im (last.im - first.im)
    (fun _ member => List.mem_append_right _ member) vertical.index vertical.inside
  exact ⟨interval, within, horizontal.index, vertical.index, point first last interval.lower, rfl,
    point first last interval.upper, rfl, ⟨xBound.1.1, xBound.1.2, yBound.1.1, yBound.1.2⟩,
    ⟨xBound.2.1, xBound.2.2, yBound.2.1, yBound.2.2⟩⟩

/-- Assign the retained interval list to its midpoint-selected cells in order.

The recursion reads each supplied interval exactly once and passes its original membership certificate to the same
midpoint assignment. The retained tail remains in its original order. -/
@[expose] def assignAll (cuts : GridCuts geometry) (firstInside : Geometry.Covers geometry first) (lastInside :
  Geometry.Covers geometry last)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (cuts.parameters first last)) :
    (intervals : List PreparedAxisPartitions.Interval) → (∀ interval ∈ intervals, interval ∈ partition.intervals) →
      List (SegmentPiece geometry first last)
  | [], _ => []
  | interval :: rest, included => cuts.assign firstInside lastInside partition interval (included _ List.mem_cons_self)
    ::
      assignAll cuts firstInside lastInside partition rest (fun _ member => included _ (List.mem_cons_of_mem _ member))

/-- Reading assigned interval owners returns the supplied interval list.

Structural induction retains the head interval literally and transports the unchanged tail through list construction,
without normalizing a predicate beneath the recursion. -/
theorem assignAll_intervals (cuts : GridCuts geometry)
    (firstInside : Geometry.Covers geometry first) (lastInside : Geometry.Covers geometry last)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (cuts.parameters first last))
    (intervals : List PreparedAxisPartitions.Interval) (included : ∀ interval ∈ intervals, interval ∈
      partition.intervals) :
    (assignAll cuts firstInside lastInside partition intervals included).map SegmentPiece.interval = intervals := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
      simp only [assignAll, List.map_cons]
      exact congrArg (List.cons interval) (ih _)

end GridCuts

set_option genInjectivity false in
/-- A finite cell-owned partition of the original segment with its exact retained piece list and count.

The stored pieces read back to the original crossing partition in order, preserving all interval and owner identities.
-/
structure SegmentSplit {geometry : Geometry columns rows} (cuts : GridCuts geometry) (first last : Gaussian) where
  /-- The original unit-interval partition at the exact retained crossing parameters. -/ partition :
    Geometry.Rectangle.AxisPartition 0 1 (cuts.parameters first last)
  /-- The ordered retained original cell-owned segment pieces. -/ pieces : List (SegmentPiece geometry first last)
  /-- The piece intervals equal the original partition intervals in order. -/ intervals_eq : pieces.map
    SegmentPiece.interval = partition.intervals
  /-- The cached original piece count. -/ count : Nat
  /-- The retained count equals the exact stored piece-list length. -/ count_eq : count = pieces.length

constructive_injectivity SegmentSplit

namespace SegmentSplit

variable {geometry : Geometry columns rows} {cuts : GridCuts geometry} {first last : Gaussian}

/-- Partition the original segment at retained grid crossings and cache its exact cell-owned pieces.

The ordered partition supplies the same interval membership proofs used by the midpoint assignments; its complete piece
list and count are retained. -/
@[expose] def build (cuts : GridCuts geometry) (first last : Gaussian)
    (firstInside : Geometry.Covers geometry first) (lastInside : Geometry.Covers geometry last) : SegmentSplit cuts
      first last :=
  let partition := Geometry.Rectangle.AxisPartition.build 0 1 (by decide) (cuts.parameters first last)
  let pieces := cuts.assignAll firstInside lastInside partition partition.intervals (fun _ member => member)
  ⟨partition, pieces, cuts.assignAll_intervals firstInside lastInside partition _ _, pieces.length, rfl⟩

/-- The retained original segment split has at most columns plus rows plus five pieces. -/
theorem count_le (split : SegmentSplit cuts first last) : split.count ≤ columns + rows + 5 := by
  have lengthEq := congrArg List.length split.intervals_eq
  rw [Map.length_map, ← split.count_eq, ← split.partition.count_eq] at lengthEq
  have bounded := split.partition.count_le
  have cutsBound := cuts.parameters_length first last
  omega

/-- Successive increments along the original increasing interval walk sum to its endpoint difference. -/
private theorem intervals_telescope (value : Coordinate → Gaussian) {intervals : List PreparedAxisPartitions.Interval} :
    {first last : Coordinate} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) →
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (walk.edges.map fun interval => value interval.upper - value
        interval.lower) =
        value last - value first
  | _, _, .nil _ => by change (0 : Gaussian) = _ - _; ring1
  | _, _, .cons interval _ tail => by
      change (value interval.upper - value interval.lower) + Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [intervals_telescope value tail]
      simp only [id_eq]
      ring1

/-- Reading retained piece endpoints equals reading their parameter intervals.

Each cached endpoint is transported through its stored scalar equality; list induction preserves the tail and the
original ordered interval owners. -/
private theorem pieces_readback (value : Gaussian → Gaussian) (pieces : List (SegmentPiece geometry first last)) :
    pieces.map (fun piece => value piece.lastPoint - value piece.firstPoint) =
      (pieces.map SegmentPiece.interval).map
        (fun interval => value (point first last interval.upper) - value (point first last interval.lower)) := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
      change (value piece.lastPoint - value piece.firstPoint) :: _ = _ :: _
      have head : value piece.lastPoint - value piece.firstPoint =
          value (point first last piece.interval.upper) - value (point first last piece.interval.lower) := by
        rewrite [piece.first_eq, piece.last_eq]
        exact Eq.refl _
      rewrite [head]
      exact congrArg (List.cons _) ih

/-- The retained segment-piece increments telescope to the original endpoint difference. -/
theorem telescope (split : SegmentSplit cuts first last) (value : Gaussian → Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (split.pieces.map fun piece => value piece.lastPoint - value
      piece.firstPoint) =
      value last - value first := by
  rw [pieces_readback, split.intervals_eq, ← split.partition.walk_edges]
  exact (intervals_telescope (fun parameter => value (point first last parameter)) split.partition.walk).trans
    (by rw [PreparedSegmentCuts.point_zero, PreparedSegmentCuts.point_one])

/-- Every unit-interval parameter belongs to a retained segment piece.

The retained partition supplies a containing interval, and its stored readback equation selects the corresponding
original piece together with exact membership and endpoint bounds. -/
theorem covers (split : SegmentSplit cuts first last) (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
  :
    ∃ piece ∈ split.pieces, piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper := by
  let located := split.partition.locate parameter inside
  have member : located.interval ∈ split.pieces.map SegmentPiece.interval := by
    rw [split.intervals_eq]
    exact located.member
  obtain ⟨piece, present, equal⟩ := Map.mem_map.mp member
  exact ⟨piece, present, equal ▸ located.inside⟩

set_option genInjectivity false in
/-- An original retained segment piece containing the requested parameter, with exact list membership. -/
structure Located (split : SegmentSplit cuts first last) (parameter : Coordinate) where
  /-- The retained original split piece containing the requested parameter. -/ piece : SegmentPiece geometry first last
  /-- The selected piece belongs to the exact original retained piece list. -/ member : piece ∈ split.pieces
  /-- The requested parameter lies between the selected piece's original interval endpoints. -/ inside :
    piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper

constructive_injectivity Located

/-- Find the first retained piece containing the parameter.

The dependent bounds test scans the supplied list in order. A failing head passes the retained coverage witness to the
unchanged tail, and a successful head preserves its exact nominal piece and membership. -/
@[expose] def locatePieces (parameter : Coordinate) : (pieces : List (SegmentPiece geometry first last)) →
    (∃ piece ∈ pieces, piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper) →
      {piece : SegmentPiece geometry first last // piece ∈ pieces ∧ piece.interval.lower ≤ parameter ∧ parameter ≤
        piece.interval.upper}
  | [], covered =>
      have absent : False := by obtain ⟨piece, member, _⟩ := covered; exact List.not_mem_nil member
      absent.elim
  | piece :: rest, covered =>
      if inside : piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper then
        ⟨piece, List.mem_cons_self, inside⟩
      else
        have remaining : ∃ piece ∈ rest, piece.interval.lower ≤ parameter ∧ parameter ≤ piece.interval.upper := by
          obtain ⟨found, member, bounds⟩ := covered
          rcases Membership.mem_cons.mp member with rfl | member
          · exact (inside bounds).elim
          · exact ⟨found, member, bounds⟩
        let found := locatePieces parameter rest remaining
        ⟨found.val, List.mem_cons_of_mem _ found.property.1, found.property.2⟩

/-- Locate the original retained split piece containing a unit-interval parameter. -/
@[expose] def locate (split : SegmentSplit cuts first last) (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter
  ≤ 1) :
    Located split parameter :=
  let found := locatePieces parameter split.pieces (split.covers parameter inside)
  ⟨found.val, found.property.1, found.property.2⟩

/-- The ordered endpoint pairs of the retained original segment pieces. -/
@[expose] def points (split : SegmentSplit cuts first last) : List Gaussian :=
  split.pieces.flatMap fun piece => [piece.firstPoint, piece.lastPoint]

/-- Both endpoints of a retained member piece occur in the original split's point list. -/
theorem points_mem (split : SegmentSplit cuts first last) {piece : SegmentPiece geometry first last}
    (member : piece ∈ split.pieces) : piece.firstPoint ∈ split.points ∧ piece.lastPoint ∈ split.points := by
  exact ⟨Flatten.mem_flatMap.mpr ⟨piece, member, List.mem_cons_self⟩,
    Flatten.mem_flatMap.mpr ⟨piece, member, List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

/-- The retained point list has exactly twice the piece count.

Every supplied piece contributes its two cached endpoints in their retained order. List induction transports this exact
contribution through the original flat-map concatenation. -/
theorem points_length (split : SegmentSplit cuts first last) : split.points.length = 2 * split.count := by
  rw [split.count_eq]
  change (split.pieces.flatMap _).length = _
  generalize split.pieces = pieces
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    simp only [Flatten.flatMap_cons, Append.length_append, List.length_cons, List.length_nil, ih]; omega

end SegmentSplit

end Purelib.Riemann.Paths.RectangularSegmentSplitting

end
