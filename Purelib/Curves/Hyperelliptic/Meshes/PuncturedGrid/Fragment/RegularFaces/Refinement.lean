module

import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Occurrence
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Fraction
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Rat.Interval.ConvexCombination

/-! # Restrictions of the same retained regular fragment

Only the parameter interval is refined. The opaque original cell
restriction, complete containing edge and actual regular face are reused.
No midpoint lookup, classification, query or root selection runs again.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces

open Purelib
open Purelib.Polynomial.Geometry
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Paths

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

namespace EdgePoint

variable {ambient : Box} {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient}

/-- Interpolate two retained positions on the SAME complete grid edge in their supplied orientation. -/
def interpolate {start finish first last : Canonical} {edge : Edge grid start finish}
    (left : EdgePoint edge first) (right : EdgePoint edge last)
    (parameter : Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    EdgePoint edge (Affine.line first (last - first) parameter) := by
  have segmentPoint (time : Rational) : edge.segment.pointAt time = PreparedSegmentCuts.point start finish time :=
    (ClearPath.ClearSegment.pointAt_eq_line edge.segment time).trans
      (PreparedSegmentCuts.point_eq_line start finish time).symm
  refine ⟨left.parameter + parameter * (right.parameter - left.parameter),
    Box.coordinate_between left.inside right.inside inside, ?_⟩
  have endpoints := congrArg₂ (fun a b => PreparedSegmentCuts.point a b parameter)
    ((segmentPoint left.parameter).symm.trans left.point_eq)
    ((segmentPoint right.parameter).symm.trans right.point_eq)
  exact (segmentPoint _).trans
    ((PreparedSegmentCuts.point_affine start finish left.parameter right.parameter parameter).trans
    (endpoints.trans (PreparedSegmentCuts.point_eq_line first last parameter)))

/-- Endpoint-index transport preserves the literal stored edge parameter. -/
theorem castPoint_parameter {start finish first last : Canonical} {edge : Edge grid start finish}
    (same : first = last) (point : EdgePoint edge first) : (same ▸ point).parameter = point.parameter := by
  cases same
  rfl

/-- Interpolation retains its exact original affine edge parameter. -/
theorem interpolate_parameter {start finish first last : Canonical} {edge : Edge grid start finish}
    (left : EdgePoint edge first) (right : EdgePoint edge last)
    (parameter : Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (left.interpolate right parameter inside).parameter =
      left.parameter + parameter * (right.parameter - left.parameter) := by
  unfold interpolate
  rfl

end EdgePoint

variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve differential} {cuts : List Rational}
variable {partition : AxisPartition 0 1 cuts} {interval : PreparedAxisPartitions.Interval}

namespace RegularPrimitiveFragment

variable (original : RegularPrimitiveFragment axes parent partition interval)

/-- The literal parent point is the affine interpolation of this retained fragment's actual endpoints. -/
theorem point_eq_line (time : Rational) : parent.edge.point time =
    Affine.line original.located.first (original.located.last - original.located.first)
      (interval.fraction time) := by
  have first := (PreparedParentSplitting.prepared_point_eq parent interval.lower).symm.trans
    original.located.first_eq.symm
  have last := (PreparedParentSplitting.prepared_point_eq parent interval.upper).symm.trans
    original.located.last_eq.symm
  have normalized := congrArg
    (PreparedSegmentCuts.point (parent.edge.point 0) (parent.edge.point 1)) (interval.fraction_eq time).symm
  have affine := PreparedSegmentCuts.point_affine (parent.edge.point 0) (parent.edge.point 1)
    interval.lower interval.upper (interval.fraction time)
  have endpoints := congrArg₂ (fun a b => PreparedSegmentCuts.point a b (interval.fraction time)) first last
  exact (PreparedParentSplitting.prepared_point_eq parent time).trans
    (normalized.trans (affine.trans (endpoints.trans (PreparedSegmentCuts.point_eq_line _ _ _))))

/-- Every bounded parameter lies in the SAME original regular face geometry. -/
theorem face_contains {time : Rational} (inside : interval.lower ≤ time ∧ time ≤ interval.upper) :
    original.face.geometry.cell.box.Contains (parent.edge.point time) :=
  (original.point_eq_line time).symm ▸ Box.contains_line original.first_inside original.last_inside
    (interval.fraction_inside inside)

/-- Retain a new endpoint position on the complete cached grid edge without another lookup. -/
def edgePoint (time : Rational) (inside : interval.lower ≤ time ∧ time ≤ interval.upper) :
    EdgePoint original.source.edge (parent.edge.point time) :=
  (original.point_eq_line time).symm ▸ original.source.first.interpolate original.source.last
    (interval.fraction time) (interval.fraction_inside inside)

/-- The retained parent query uses the exact affine parameter between the original edge positions. -/
theorem edgePoint_parameter (time : Rational) (inside : interval.lower ≤ time ∧ time ≤ interval.upper) :
    (original.edgePoint time inside).parameter = original.source.first.parameter +
      interval.fraction time * (original.source.last.parameter - original.source.first.parameter) :=
  (EdgePoint.castPoint_parameter (original.point_eq_line time).symm
    (original.source.first.interpolate original.source.last (interval.fraction time)
      (interval.fraction_inside inside))).trans
    (EdgePoint.interpolate_parameter original.source.first original.source.last
      (interval.fraction time) (interval.fraction_inside inside))

/-- Restrict the actual retained cell, edge and face to a child interval in a supplied actual partition.

The original opaque cell restriction is used once. Its endpoint equations
reindex the geometric positions; the complete edge and regular face remain
literal inputs. Exposure retains those exact full-edge/face indices for
dependent SheetEntry and shared-domain consumers.
-/
@[expose] def restrict {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    RegularPrimitiveFragment axes parent refined child :=
  let firstInside : interval.lower ≤ child.lower ∧ child.lower ≤ interval.upper :=
    ⟨inside.1, child.ordered.1.trans inside.2⟩
  let lastInside : interval.lower ≤ child.upper ∧ child.upper ≤ interval.upper :=
    ⟨inside.1.trans child.ordered.1, inside.2⟩
  let located := original.located.restrict refined child member inside
  let source : FragmentGridEdge located.val :=
    ⟨original.source.start, original.source.finish, original.source.edge,
      located.val.first_eq.symm ▸ original.edgePoint child.lower firstInside,
      located.val.last_eq.symm ▸ original.edgePoint child.upper lastInside⟩
  ⟨located.val, source, original.face,
    located.val.first_eq.symm ▸ original.face_contains firstInside,
    located.val.last_eq.symm ▸ original.face_contains lastInside⟩

/-- Restriction consumes the complete original cell-restriction result. -/
theorem restrict_located {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).located =
      (original.located.restrict refined child member inside).val := rfl

/-- The restricted fragment retains the exact original cached cell. -/
theorem restrict_cell {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).located.cell = original.located.cell :=
  (original.located.restrict refined child member inside).property

/-- Restriction retains the complete original grid edge. -/
theorem restrict_edge {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).source.edge = original.source.edge := rfl

/-- Restriction retains the complete original incident regular face. -/
theorem restrict_face {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).face = original.face := rfl

/-- The restricted first position retains its original interpolated edge parameter. -/
theorem restrict_first_parameter {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).source.first.parameter = original.source.first.parameter +
      interval.fraction child.lower * (original.source.last.parameter - original.source.first.parameter) :=
  (EdgePoint.castPoint_parameter (original.located.restrict refined child member inside).val.first_eq.symm
    (original.edgePoint child.lower ⟨inside.1, child.ordered.1.trans inside.2⟩)).trans
    (original.edgePoint_parameter child.lower ⟨inside.1, child.ordered.1.trans inside.2⟩)

/-- The restricted last position retains its original interpolated edge parameter. -/
theorem restrict_last_parameter {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    (original.restrict refined child member inside).source.last.parameter = original.source.first.parameter +
      interval.fraction child.upper * (original.source.last.parameter - original.source.first.parameter) :=
  (EdgePoint.castPoint_parameter (original.located.restrict refined child member inside).val.last_eq.symm
    (original.edgePoint child.upper ⟨inside.1.trans child.ordered.1, inside.2⟩)).trans
    (original.edgePoint_parameter child.upper ⟨inside.1.trans child.ordered.1, inside.2⟩)

/-- A genuine child preserves the original complete edge's forward, reverse or stationary traversal flag. -/
theorem restrict_forward {newCuts : List Rational} (refined : AxisPartition 0 1 newCuts)
    (child : PreparedAxisPartitions.Interval) (member : child ∈ refined.intervals)
    (inside : interval.lower ≤ child.lower ∧ child.upper ≤ interval.upper) :
    decide ((original.restrict refined child member inside).source.first.parameter ≤
      (original.restrict refined child member inside).source.last.parameter) =
      decide (original.source.first.parameter ≤ original.source.last.parameter) := by
  have actual := Data.Rat.Interval.ConvexCombination.interpolation_order
    original.source.first.parameter original.source.last.parameter
    (interval.fraction child.lower) (interval.fraction child.upper) (interval.fraction_lt child.ordered)
  have comparison :
      (original.restrict refined child member inside).source.first.parameter ≤
        (original.restrict refined child member inside).source.last.parameter ↔
      original.source.first.parameter ≤ original.source.last.parameter := by
    rewrite [original.restrict_first_parameter refined child member inside,
      original.restrict_last_parameter refined child member inside]
    exact actual
  by_cases forward : original.source.first.parameter ≤ original.source.last.parameter
  · exact (decide_eq_true (comparison.mpr forward)).trans (decide_eq_true forward).symm
  · exact (decide_eq_false (fun restricted => forward (comparison.mp restricted))).trans
      (decide_eq_false forward).symm

end RegularPrimitiveFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces

end
