module

public import Purelib.Geometry.Gaussian.UnitCircle.Basic
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Coordinates
public import Purelib.Geometry.Triangles.SignedArea
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Polygons.SignedArea.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Integration.Partition.Uniform.Grid
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Fold
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Rational inscribed circle polygons

Each quarter uses the original indices `0, ..., N - 1` and the rational
stereographic chart at `i/N`. Four quarter turns retain those indices in
counterclockwise order, without repeating the endpoint of each quarter.
-/

namespace Purelib.Geometry.Gaussian.UnitCircle.Polygon

open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Geometry
open Purelib.Geometry.Polygons
open Purelib.Data.List
open Purelib.Integration.Partition
open Quarter
open Purelib.Data.Rat.Fraction.Order

/-- The Gaussian unit-circle point in a selected quarter at an exact rational parameter. -/
@[expose] public def quarterPoint (quarter : UnitCircuitQuarter) (parameter : Fraction.Rational) :
    Basic.UnitVertex where
  value := unitCircuitMultiplier quarter * Stereographic.unitQuarterPoint parameter
  unit := by
    rw [Norm.Basic.normSq_mul, unitCircuitMultiplier_unit, Stereographic.unitQuarterPoint_unit]
    decide

/-- Cartesian coordinates retain the exact real and imaginary entries of a Gaussian rational. -/
@[expose] public def planePoint (point : Data.Gaussian.Basic.Canonical) : Plane.Point Fraction.Rational :=
  ⟨point.re, point.im⟩

/-- The Cartesian quadrance from the origin is the original Gaussian squared norm. -/
public theorem quadrance_planePoint (point : Data.Gaussian.Basic.Canonical) :
    Plane.Point.Quadrance.quadrance ⟨0, 0⟩ (planePoint point) = Norm.Basic.normSq point := by
  change (point.re - 0) ^ 2 + (point.im - 0) ^ 2 = point.re ^ 2 + point.im ^ 2
  ring1

/-- The selected quarter chart point has Cartesian unit quadrance. -/
public theorem quarterPoint_quadrance (quarter : UnitCircuitQuarter) (parameter : Fraction.Rational) :
    Plane.Point.Quadrance.quadrance ⟨0, 0⟩ (planePoint (quarterPoint quarter parameter).value) = 1 := by
  rw [quadrance_planePoint]
  exact (quarterPoint quarter parameter).unit

/-- The scalar denominator of the stereographic chart is positive. -/
private theorem chartScalar_pos (parameter : Fraction.Rational) :
    0 < parameter ^ 2 + 1 :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct parameter) (by decide)

/-- The determinant of two original chart points has its exact rational readback.

This equation applies to arbitrary rational parameters; ordered nonnegative
parameters give the counterclockwise sign separately. -/
public theorem chart_determinant (first second : Fraction.Rational) :
    Plane.Point.Determinant.positionDeterminant
      (planePoint (Stereographic.unitQuarterPoint first))
      (planePoint (Stereographic.unitQuarterPoint second)) =
      2 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) := by
  have denominatorPositive := Arithmetic.mul_pos_direct (chartScalar_pos first) (chartScalar_pos second)
  apply Fraction.Field.mul_right_cancel_of_ne denominatorPositive.ne'
  calc
    Plane.Point.Determinant.positionDeterminant
        (planePoint (Stereographic.unitQuarterPoint first))
        (planePoint (Stereographic.unitQuarterPoint second)) *
        ((first ^ 2 + 1) * (second ^ 2 + 1)) =
      ((Stereographic.unitQuarterPoint first).re * (first ^ 2 + 1)) *
          ((Stereographic.unitQuarterPoint second).im * (second ^ 2 + 1)) -
        ((Stereographic.unitQuarterPoint second).re * (second ^ 2 + 1)) *
          ((Stereographic.unitQuarterPoint first).im * (first ^ 2 + 1)) := by
            unfold Plane.Point.Determinant.positionDeterminant planePoint
            ring1
    _ = (1 - first ^ 2) * (2 * second) - (1 - second ^ 2) * (2 * first) := by
      rw [Stereographic.unitQuarterPoint_re_mul_scalar,
        Stereographic.unitQuarterPoint_im_mul_scalar,
        Stereographic.unitQuarterPoint_re_mul_scalar,
        Stereographic.unitQuarterPoint_im_mul_scalar]
    _ = 2 * ((second - first) * (1 + first * second)) := by ring1
    _ = (2 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)))) *
        ((first ^ 2 + 1) * (second ^ 2 + 1)) := by
      calc
        _ = 2 * (((second - first) * (1 + first * second) /
            ((first ^ 2 + 1) * (second ^ 2 + 1))) *
            ((first ^ 2 + 1) * (second ^ 2 + 1))) :=
          congrArg (fun value => 2 * value)
            (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne').symm
        _ = _ := by ring1

/-- The original center-fan triangle has the exact signed area of the chart edge. -/
public theorem chart_triangle_area (first second : Fraction.Rational) :
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (Stereographic.unitQuarterPoint first))
      (planePoint (Stereographic.unitQuarterPoint second)) =
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  calc
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
        (planePoint (Stereographic.unitQuarterPoint first))
        (planePoint (Stereographic.unitQuarterPoint second)) * 2 =
      Plane.Point.Determinant.positionDeterminant
        (planePoint (Stereographic.unitQuarterPoint first))
        (planePoint (Stereographic.unitQuarterPoint second)) := by
      unfold Triangles.SignedArea.triangleSignedArea
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
      unfold Triangles.SignedArea.triangleDoubleSignedArea Plane.Point.Determinant.positionDeterminant
        planePoint
      ring1
    _ = 2 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) := chart_determinant first second
    _ = ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) * 2 := by ring1

/-- Increasing nonnegative chart parameters give a strictly positive oriented fan area. -/
public theorem chart_triangle_area_pos {first second : Fraction.Rational}
    (firstNonnegative : 0 ≤ first) (ordered : first < second) :
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (Stereographic.unitQuarterPoint first))
      (planePoint (Stereographic.unitQuarterPoint second)) := by
  rw [chart_triangle_area]
  have secondNonnegative : 0 ≤ second := firstNonnegative.trans ordered.le
  have productNonnegative := Arithmetic.mul_nonneg_direct firstNonnegative secondNonnegative
  have factorPositive : 0 < 1 + first * second :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) productNonnegative
  exact Field.div_pos_direct
    (Arithmetic.mul_pos_direct (Arithmetic.sub_pos_direct ordered) factorPositive)
    (Arithmetic.mul_pos_direct (chartScalar_pos first) (chartScalar_pos second))

/-- A center-fan triangle reads its area from the determinant of its two endpoints. -/
private theorem triangle_origin (first second : Plane.Point Fraction.Rational) :
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩ first second =
      Plane.Point.Determinant.positionDeterminant first second / 2 := by
  unfold Triangles.SignedArea.triangleSignedArea
  congr 1
  unfold Triangles.SignedArea.triangleDoubleSignedArea Plane.Point.Determinant.positionDeterminant
  ring1

/-- A common quarter rotation preserves the oriented determinant of two chart points. -/
public theorem quarter_determinant (quarter : UnitCircuitQuarter) (first second : Fraction.Rational) :
    Plane.Point.Determinant.positionDeterminant
      (planePoint (quarterPoint quarter first).value)
      (planePoint (quarterPoint quarter second).value) =
    Plane.Point.Determinant.positionDeterminant
      (planePoint (Stereographic.unitQuarterPoint first))
      (planePoint (Stereographic.unitQuarterPoint second)) := by
  cases quarter <;>
    simp only [quarterPoint, unitCircuitMultiplier, planePoint,
      Plane.Point.Determinant.positionDeterminant, Data.Gaussian.Basic.mul_re,
      Data.Gaussian.Basic.mul_im] <;> ring1

/-- Every quarter rotation has the same center-fan edge area as the original chart. -/
public theorem quarter_triangle_area (quarter : UnitCircuitQuarter) (first second : Fraction.Rational) :
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (quarterPoint quarter first).value)
      (planePoint (quarterPoint quarter second).value) =
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)) := by
  rw [triangle_origin, quarter_determinant, ← triangle_origin, chart_triangle_area]

/-- The original triangle quadrea is sixteen times the squared chart-edge area. -/
public theorem quarter_triangle_quadrea (quarter : UnitCircuitQuarter) (first second : Fraction.Rational) :
    Triangles.Quadrea.Basic.quadrea ⟨0, 0⟩
      (planePoint (quarterPoint quarter first).value)
      (planePoint (quarterPoint quarter second).value) =
      16 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) ^ 2 := by
  rw [Triangles.SignedArea.triangle_quadrea_eq_sixteen_signed_area_square _ _ _ (by decide),
    quarter_triangle_area]

/-- Consecutive quarter charts share their cardinal endpoint, including the closing join. -/
public theorem quarter_joins :
    (quarterPoint .first 1).value = (quarterPoint .second 0).value ∧
    (quarterPoint .second 1).value = (quarterPoint .third 0).value ∧
    (quarterPoint .third 1).value = (quarterPoint .fourth 0).value ∧
    (quarterPoint .fourth 1).value = (quarterPoint .first 0).value := by
  decide

/-- Ordered original quarter and parameter indices for a positive `extra + 1` cells per quarter. -/
@[expose] public def indices (extra : Nat) : List (UnitCircuitQuarter × Nat) :=
  let offsets := List.range (extra + 1)
  offsets.map (fun index => (.first, index)) ++
  offsets.map (fun index => (.second, index)) ++
  offsets.map (fun index => (.third, index)) ++
  offsets.map (fun index => (.fourth, index))

/-- Each retained index selects the original stereographic point and its quarter-turn certificate. -/
@[expose] public def indexedVertex (extra : Nat) (index : UnitCircuitQuarter × Nat) : Basic.UnitVertex :=
  quarterPoint index.1 (Uniform.Grid.point (extra + 1) index.2)

/-- Consecutive grid points in every quarter have strictly positive center-fan area.

The successor may be the virtual end of a quarter; `indexed_joins` identifies
that point with the first point of the next quarter, including closure. -/
public theorem indexed_edge_area_pos (extra index : Nat) (quarter : UnitCircuitQuarter) :
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (quarter, index)).value)
      (planePoint (indexedVertex extra (quarter, index + 1)).value) := by
  have nonnegative : 0 ≤ Uniform.Grid.point (extra + 1) index := by
    by_cases zero : index = 0
    · subst index
      rw [Uniform.Grid.point_zero]
    · calc
        (0 : Fraction.Rational) = Uniform.Grid.point (extra + 1) 0 :=
          (Uniform.Grid.point_zero _).symm
        _ ≤ Uniform.Grid.point (extra + 1) index :=
          (Uniform.Grid.point_lt (Nat.succ_pos extra) (Nat.pos_of_ne_zero zero)).le
  have ordered := Uniform.Grid.point_lt (Nat.succ_pos extra) (Nat.lt_succ_self index)
  change 0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
    (planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) index)).value)
    (planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) (index + 1))).value)
  rw [triangle_origin, quarter_determinant, ← triangle_origin]
  exact chart_triangle_area_pos nonnegative ordered

/-- The original grid endpoints join the four quarters and close at the first vertex. -/
public theorem indexed_joins (extra : Nat) :
    (indexedVertex extra (.first, extra + 1)).value = (indexedVertex extra (.second, 0)).value ∧
    (indexedVertex extra (.second, extra + 1)).value = (indexedVertex extra (.third, 0)).value ∧
    (indexedVertex extra (.third, extra + 1)).value = (indexedVertex extra (.fourth, 0)).value ∧
    (indexedVertex extra (.fourth, extra + 1)).value = (indexedVertex extra (.first, 0)).value := by
  simp only [indexedVertex, Uniform.Grid.point_self (Nat.succ_pos extra), Uniform.Grid.point_zero]
  exact quarter_joins

/-- The four actual quarter joins, including the closing edge, are positively oriented. -/
public theorem indexed_join_areas_pos (extra : Nat) :
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (.first, extra)).value)
      (planePoint (indexedVertex extra (.second, 0)).value) ∧
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (.second, extra)).value)
      (planePoint (indexedVertex extra (.third, 0)).value) ∧
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (.third, extra)).value)
      (planePoint (indexedVertex extra (.fourth, 0)).value) ∧
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (.fourth, extra)).value)
      (planePoint (indexedVertex extra (.first, 0)).value) := by
  obtain ⟨firstJoin, secondJoin, thirdJoin, fourthJoin⟩ := indexed_joins extra
  have first := indexed_edge_area_pos extra extra .first
  have second := indexed_edge_area_pos extra extra .second
  have third := indexed_edge_area_pos extra extra .third
  have fourth := indexed_edge_area_pos extra extra .fourth
  rw [firstJoin] at first
  rw [secondJoin] at second
  rw [thirdJoin] at third
  rw [fourthJoin] at fourth
  exact ⟨first, second, third, fourth⟩

/-- The ordered certified unit vertices derived from the original index occurrences. -/
@[expose] public def unitVertices (extra : Nat) : List Basic.UnitVertex :=
  (indices extra).map (indexedVertex extra)

/-- The actual ordered Cartesian polygon used by the signed-area operation. -/
@[expose] public def vertices (extra : Nat) : List (Plane.Point Fraction.Rational) :=
  (unitVertices extra).map (fun point => planePoint point.value)

/-- The finite polygon area is computed by the existing shoelace signed-area owner. -/
@[expose] public def area (extra : Nat) : Fraction.Rational :=
  SignedArea.Basic.polygonSignedArea (vertices extra)

/-- The plane vertices read back from the same ordered quarter/index occurrences. -/
public theorem vertices_eq (extra : Nat) : vertices extra =
    (indices extra).map (fun index => planePoint (indexedVertex extra index).value) := by
  unfold vertices unitVertices
  rw [Purelib.Data.List.Map.map_map]
  rfl

/-- The original index list has exactly four times the positive quarter cell count. -/
public theorem indices_length (extra : Nat) : (indices extra).length = 4 * (extra + 1) := by
  unfold indices
  simp only [Purelib.Data.List.Append.length_append, Purelib.Data.List.Map.length_map,
    Range.Basic.length_range]
  omega0

/-- The polygon retains one vertex for each original quarter/index occurrence. -/
public theorem vertices_length (extra : Nat) : (vertices extra).length = 4 * (extra + 1) := by
  unfold vertices unitVertices
  rw [Purelib.Data.List.Map.length_map, Purelib.Data.List.Map.length_map, indices_length]

/-- Each retained quarter/index occurrence has an index below the positive cell count. -/
public theorem indices_bound (extra : Nat) (entry : UnitCircuitQuarter × Nat)
    (member : entry ∈ indices extra) : entry.2 < extra + 1 := by
  have bound (quarter : UnitCircuitQuarter)
      (inQuarter : entry ∈ (List.range (extra + 1)).map (fun index => (quarter, index))) :
      entry.2 < extra + 1 := by
    obtain ⟨index, inRange, equal⟩ := Purelib.Data.List.Map.mem_map.mp inQuarter
    cases equal
    exact Range.Basic.mem_range.mp inRange
  unfold indices at member
  rcases Purelib.Data.List.Membership.mem_append.mp member with firstThree | fourth
  · rcases Purelib.Data.List.Membership.mem_append.mp firstThree with firstTwo | third
    · rcases Purelib.Data.List.Membership.mem_append.mp firstTwo with first | second
      · exact bound .first first
      · exact bound .second second
    · exact bound .third third
  · exact bound .fourth fourth

/-- Every actual plane vertex has its original bounded quarter/index occurrence. -/
public theorem vertices_origin (extra : Nat) (point : Plane.Point Fraction.Rational)
    (member : point ∈ vertices extra) :
    ∃ entry ∈ indices extra, entry.2 < extra + 1 ∧
      point = planePoint (indexedVertex extra entry).value := by
  rw [vertices_eq] at member
  obtain ⟨entry, retained, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  exact ⟨entry, retained, indices_bound extra entry retained, equal.symm⟩

/-- Every actual polygon vertex has unit quadrance from the Cartesian origin. -/
public theorem vertices_unit (extra : Nat) (point : Plane.Point Fraction.Rational)
    (member : point ∈ vertices extra) : Plane.Point.Quadrance.quadrance ⟨0, 0⟩ point = 1 := by
  change point ∈ (unitVertices extra).map (fun vertex => planePoint vertex.value) at member
  obtain ⟨vertex, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  rw [quadrance_planePoint]
  exact vertex.unit

/-- The Cartesian point selected by a quarter and an original grid index. -/
private def gridVertex (extra : Nat) (quarter : UnitCircuitQuarter) (index : Nat) :
    Plane.Point Fraction.Rational := planePoint (indexedVertex extra (quarter, index)).value

/-- The ordered Cartesian vertices in one quarter. -/
private def quarterVertices (extra : Nat) (quarter : UnitCircuitQuarter) :
    List (Plane.Point Fraction.Rational) :=
  (List.range (extra + 1)).map (gridVertex extra quarter)

/-- A quarter's ordered range starts at its zero index and continues through the original grid nodes. -/
private theorem quarterVertices_eq (extra : Nat) (quarter : UnitCircuitQuarter) :
    quarterVertices extra quarter = gridVertex extra quarter 0 ::
      (Uniform.Grid.nodes (extra + 1) 0 extra).map
        (fun parameter => planePoint (quarterPoint quarter parameter).value) := by
  unfold quarterVertices
  rw [Range.Basic.range_succ_eq_map, List.map_cons,
    Purelib.Data.List.Map.map_map, Uniform.Grid.nodes_eq_map, Purelib.Data.List.Map.map_map]
  apply congrArg (List.cons (gridVertex extra quarter 0))
  apply Purelib.Data.List.Map.map_congr_left
  intro index _
  change planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) (index + 1))).value =
    planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) (0 + index + 1))).value
  rw [Nat.zero_add]

/-- The original polygon is the concatenation of its four ordered quarter lists. -/
private theorem vertices_quarters (extra : Nat) : vertices extra =
    quarterVertices extra .first ++ quarterVertices extra .second ++
      quarterVertices extra .third ++ quarterVertices extra .fourth := by
  rw [vertices_eq]
  unfold indices quarterVertices
  simp only [Purelib.Data.List.Map.map_append, Purelib.Data.List.Map.map_map]
  rfl

/-- A finite run of original grid nodes contributes exactly its consecutive determinants.

The unchanged suffix and closing vertex remain in the original shoelace
recursion, and the final current vertex is the original end index. -/
private theorem grid_nodes_shoelace (extra : Nat) (quarter : UnitCircuitQuarter)
    (first : Plane.Point Fraction.Rational) (suffix : List (Plane.Point Fraction.Rational)) :
    ∀ start count : Nat,
      SignedArea.Basic.polygonDoubleSignedAreaAux first (gridVertex extra quarter start)
          ((Uniform.Grid.nodes (extra + 1) start count).map
            (fun parameter => planePoint (quarterPoint quarter parameter).value) ++ suffix) =
        ((List.range' start count).map (fun index =>
          Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
            (gridVertex extra quarter (index + 1)))).sum +
        SignedArea.Basic.polygonDoubleSignedAreaAux first
          (gridVertex extra quarter (start + count)) suffix
  | start, 0 => by
      change SignedArea.Basic.polygonDoubleSignedAreaAux first
        (gridVertex extra quarter start) suffix =
        0 + SignedArea.Basic.polygonDoubleSignedAreaAux first
          (gridVertex extra quarter (start + 0)) suffix
      rw [Nat.add_zero, Fraction.Field.zero_add]
  | start, count + 1 => by
      change Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter start)
          (gridVertex extra quarter (start + 1)) +
        SignedArea.Basic.polygonDoubleSignedAreaAux first (gridVertex extra quarter (start + 1))
          ((Uniform.Grid.nodes (extra + 1) (start + 1) count).map
            (fun parameter => planePoint (quarterPoint quarter parameter).value) ++ suffix) =
        (Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter start)
          (gridVertex extra quarter (start + 1)) +
          ((List.range' (start + 1) count).map (fun index =>
            Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
              (gridVertex extra quarter (index + 1)))).sum) +
        SignedArea.Basic.polygonDoubleSignedAreaAux first
          (gridVertex extra quarter (start + (count + 1))) suffix
      rw [grid_nodes_shoelace extra quarter first suffix (start + 1) count]
      rw [show start + 1 + count = start + (count + 1) from by omega0]
      ring1

/-- The determinant sum for a full quarter includes its final edge to the next chart. -/
private theorem quarter_det_sum_succ (extra : Nat) (quarter : UnitCircuitQuarter) :
    ((List.range' 0 (extra + 1)).map (fun index =>
      Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
        (gridVertex extra quarter (index + 1)))).sum =
    ((List.range' 0 extra).map (fun index =>
      Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
        (gridVertex extra quarter (index + 1)))).sum +
    Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter extra)
      (gridVertex extra quarter (extra + 1)) := by
  rw [Range.Basic.range'_succ, Nat.zero_add, Purelib.Data.List.Map.map_append,
    Purelib.Data.List.Fold.sum_append Fraction.Field.zero_add Fraction.Field.add_assoc]
  change _ + (_ + 0) = _
  ring1

/-- Following one quarter and its join contributes exactly its original consecutive determinants. -/
private theorem quarter_shoelace (extra : Nat) (quarter : UnitCircuitQuarter)
    (first next : Plane.Point Fraction.Rational) (suffix : List (Plane.Point Fraction.Rational))
    (join : next = gridVertex extra quarter (extra + 1)) :
    SignedArea.Basic.polygonDoubleSignedAreaAux first (gridVertex extra quarter 0)
        ((Uniform.Grid.nodes (extra + 1) 0 extra).map
          (fun parameter => planePoint (quarterPoint quarter parameter).value) ++ next :: suffix) =
      ((List.range' 0 (extra + 1)).map (fun index =>
        Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
          (gridVertex extra quarter (index + 1)))).sum +
      SignedArea.Basic.polygonDoubleSignedAreaAux first next suffix := by
  rw [grid_nodes_shoelace extra quarter first (next :: suffix) 0 extra, Nat.zero_add]
  change _ + (Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter extra) next +
    SignedArea.Basic.polygonDoubleSignedAreaAux first next suffix) = _
  rw [join, quarter_det_sum_succ]
  ring1

/-- The closing quarter includes the edge back to the polygon's first vertex. -/
private theorem quarter_shoelace_close (extra : Nat) (quarter : UnitCircuitQuarter)
    (first : Plane.Point Fraction.Rational) (join : first = gridVertex extra quarter (extra + 1)) :
    SignedArea.Basic.polygonDoubleSignedAreaAux first (gridVertex extra quarter 0)
        ((Uniform.Grid.nodes (extra + 1) 0 extra).map
          (fun parameter => planePoint (quarterPoint quarter parameter).value)) =
      ((List.range' 0 (extra + 1)).map (fun index =>
        Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
          (gridVertex extra quarter (index + 1)))).sum := by
  have path := grid_nodes_shoelace extra quarter first [] 0 extra
  rw [List.append_nil, Nat.zero_add] at path
  rw [path]
  change _ + Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter extra) first = _
  rw [join, quarter_det_sum_succ]

/-- The original ordered determinant sum across one quarter, including its final join. -/
private def quarterDoubleSum (extra : Nat) (quarter : UnitCircuitQuarter) : Fraction.Rational :=
  ((List.range' 0 (extra + 1)).map (fun index =>
    Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
      (gridVertex extra quarter (index + 1)))).sum

/-- The actual shoelace recursion visits all four original quarter runs and their joins. -/
private theorem polygon_double_quarters (extra : Nat) :
    SignedArea.Basic.polygonDoubleSignedArea (vertices extra) =
      quarterDoubleSum extra .first + quarterDoubleSum extra .second +
        quarterDoubleSum extra .third + quarterDoubleSum extra .fourth := by
  have joins := indexed_joins extra
  have firstJoin : gridVertex extra .second 0 = gridVertex extra .first (extra + 1) :=
    (congrArg planePoint joins.1).symm
  have secondJoin : gridVertex extra .third 0 = gridVertex extra .second (extra + 1) :=
    (congrArg planePoint joins.2.1).symm
  have thirdJoin : gridVertex extra .fourth 0 = gridVertex extra .third (extra + 1) :=
    (congrArg planePoint joins.2.2.1).symm
  have closingJoin : gridVertex extra .first 0 = gridVertex extra .fourth (extra + 1) :=
    (congrArg planePoint joins.2.2.2).symm
  rw [vertices_quarters, quarterVertices_eq extra .first, quarterVertices_eq extra .second,
    quarterVertices_eq extra .third, quarterVertices_eq extra .fourth]
  simp only [List.append_assoc, List.cons_append]
  change SignedArea.Basic.polygonDoubleSignedAreaAux
    (gridVertex extra .first 0) (gridVertex extra .first 0) _ = _
  rw [quarter_shoelace extra .first _ _ _ firstJoin,
    quarter_shoelace extra .second _ _ _ secondJoin,
    quarter_shoelace extra .third _ _ _ thirdJoin,
    quarter_shoelace_close extra .fourth _ closingJoin]
  change quarterDoubleSum extra .first + (quarterDoubleSum extra .second +
    (quarterDoubleSum extra .third + quarterDoubleSum extra .fourth)) = _
  ring1

/-- Every quarter's consecutive determinant is twice the first quarter's fan area. -/
private theorem quarter_edge_double (extra index : Nat) (quarter : UnitCircuitQuarter) :
    Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
      (gridVertex extra quarter (index + 1)) =
    2 * Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (gridVertex extra .first index) (gridVertex extra .first (index + 1)) := by
  change Plane.Point.Determinant.positionDeterminant
    (planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) index)).value)
    (planePoint (quarterPoint quarter (Uniform.Grid.point (extra + 1) (index + 1))).value) =
    2 * Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (quarterPoint .first (Uniform.Grid.point (extra + 1) index)).value)
      (planePoint (quarterPoint .first (Uniform.Grid.point (extra + 1) (index + 1))).value)
  rw [quarter_determinant, triangle_origin, quarter_determinant]
  have halves := Fraction.Field.two_halves (Plane.Point.Determinant.positionDeterminant
    (planePoint (Stereographic.unitQuarterPoint (Uniform.Grid.point (extra + 1) index)))
    (planePoint (Stereographic.unitQuarterPoint (Uniform.Grid.point (extra + 1) (index + 1)))) )
  calc
    _ = _ + _ := halves.symm
    _ = _ := by ring1

/-- Summing the original occurrences preserves the quarter-turn fan-area readback. -/
private theorem quarter_sum_triangle (extra : Nat) (quarter : UnitCircuitQuarter) :
    quarterDoubleSum extra quarter = 2 *
      ((List.range' 0 (extra + 1)).map (fun index =>
        Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
          (gridVertex extra .first index) (gridVertex extra .first (index + 1)))).sum := by
  unfold quarterDoubleSum
  generalize List.range' 0 (extra + 1) = indices
  induction indices with
  | nil =>
      change (0 : Fraction.Rational) = 2 * 0
      ring1
  | cons index tail ih =>
      change Plane.Point.Determinant.positionDeterminant (gridVertex extra quarter index)
          (gridVertex extra quarter (index + 1)) +
        (tail.map (fun next => Plane.Point.Determinant.positionDeterminant
          (gridVertex extra quarter next) (gridVertex extra quarter (next + 1)))).sum =
        2 * (Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
          (gridVertex extra .first index) (gridVertex extra .first (index + 1)) +
        (tail.map (fun next => Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
          (gridVertex extra .first next) (gridVertex extra .first (next + 1)))).sum)
      rw [quarter_edge_double, ih]
      ring1

/-- A zero-start unit-step range retains exactly the original natural range. -/
private theorem rangeFromZero (count : Nat) : List.range' 0 count = List.range count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Range.Basic.range'_succ, Nat.zero_add, ih,
        Range.Basic.range_succ]

/-- The actual polygon area is four times its ordered first-quarter center-fan sum.

The shoelace recursion visits the retained grid vertices and all four joins,
including closure. Each quarter-turn preserves its original signed edge area. -/
public theorem area_eq_quarter_triangles (extra : Nat) :
    area extra = 4 * ((List.range (extra + 1)).map (fun index =>
      Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
        (planePoint (indexedVertex extra (.first, index)).value)
        (planePoint (indexedVertex extra (.first, index + 1)).value))).sum := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  change (SignedArea.Basic.polygonDoubleSignedArea (vertices extra) / 2) * 2 = _
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide), polygon_double_quarters,
    quarter_sum_triangle extra .first, quarter_sum_triangle extra .second,
    quarter_sum_triangle extra .third, quarter_sum_triangle extra .fourth,
    rangeFromZero]
  change _ = (4 * ((List.range (extra + 1)).map (fun index =>
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (gridVertex extra .first index) (gridVertex extra .first (index + 1)))).sum) * 2
  ring1

/-- Evaluate one quarter's signed fan triangles and reuse it for all four quarters.

The original positive cell count is `extra + 1`. Each term uses the retained
indexed stereographic vertices and the existing signed triangle-area operation. -/
@[expose] public def quarterArea (extra : Nat) : Fraction.Rational :=
  4 * ((List.range (extra + 1)).map (fun index =>
    Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (planePoint (indexedVertex extra (.first, index)).value)
      (planePoint (indexedVertex extra (.first, index + 1)).value))).sum

/-- Quarter-only evaluation equals the original complete polygon's signed shoelace area. -/
public theorem quarterArea_eq_area (extra : Nat) : quarterArea extra = area extra :=
  (area_eq_quarter_triangles extra).symm

/-- The actual polygon's area reads back as four times the ordered rational edge sum.

Each term uses the original consecutive grid indices and the exact
stereographic fan-area formula. This is a theorem about the shoelace
computation on `vertices`, not a replacement of that geometric observation. -/
public theorem area_eq_grid_sum (extra : Nat) :
    area extra = 4 * ((List.range (extra + 1)).map (fun index =>
      let first := Uniform.Grid.point (extra + 1) index
      let second := Uniform.Grid.point (extra + 1) (index + 1)
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)))).sum := by
  rw [area_eq_quarter_triangles]
  apply congrArg (fun value : Fraction.Rational => 4 * value)
  apply congrArg (fun values : List Fraction.Rational => values.sum)
  apply Purelib.Data.List.Map.map_congr_left
  intro index _
  exact quarter_triangle_area .first (Uniform.Grid.point (extra + 1) index)
    (Uniform.Grid.point (extra + 1) (index + 1))

end Purelib.Geometry.Gaussian.UnitCircle.Polygon
