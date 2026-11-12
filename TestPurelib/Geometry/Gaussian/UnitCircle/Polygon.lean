module

import Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon
import Purelib.Geometry.Gaussian.UnitCircle.Presentation
import Purelib.Geometry.Gaussian.UnitCircle.Polygon.Presentation
import Purelib.Data.List.Map
import Purelib.Tactic.QuotientFreeOmega

namespace TestPurelib.Geometry.Gaussian.UnitCircle.Polygon

open Purelib.Data.Rat
open Purelib.Geometry
open Gaussian.UnitCircle
open Gaussian.UnitCircle.Polygon.Presentation
open Polygons.SignedArea.Basic (polygonSignedArea)
open Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon

example : diamond ≠ rotatedDiamond := diamond_ne_rotated

example : polygonSignedArea rotatedDiamond =
    polygonSignedArea diamond := diamond_rotated_area

example : polygonSignedArea rotatedDiamond = 2 :=
  diamond_rotated_area.trans diamond_area

example : (match Polygon.Presentation.check 0 (.first, 0) with
    | .valid _ => true
    | .outOfRange _ => false) = true := by decide

example : (match Polygon.Presentation.check 0 (.first, 1) with
    | .valid _ => false
    | .outOfRange _ => true) = true := by decide

example : (match Polygon.Presentation.check 3 (.first, 3) with
    | .valid _ => true
    | .outOfRange _ => false) = true := by decide

example : (match Polygon.Presentation.check 3 (.first, 4) with
    | .valid _ => false
    | .outOfRange _ => true) = true := by decide

example : (match Polygon.Presentation.check 3 (.fourth, 9) with
    | .valid _ => false
    | .outOfRange _ => true) = true := by decide

example (extra : Nat) (entry : Quarter.UnitCircuitQuarter × Nat) :
    Polygon.Presentation.Valid extra entry ↔ entry ∈ Polygon.indices extra :=
  Polygon.Presentation.valid_iff_mem extra entry

example (extra : Nat) (display : Polygon.Presentation.Display extra) :
    Polygon.Presentation.vertex extra display ∈ Polygon.unitVertices extra := by
  apply Purelib.Data.List.Map.mem_map.mpr
  exact ⟨display.val, Polygon.Presentation.member extra display, rfl⟩

example (extra : Nat) (display : Polygon.Presentation.Display extra) :
    Polygon.Presentation.quote extra display.val (Polygon.Presentation.member extra display) = display :=
  Polygon.Presentation.quote_member extra display

private def occurrenceFirst : Polygon.Presentation.Display 1 := ⟨(.first, 1), by decide⟩

private def occurrenceSecond : Polygon.Presentation.Display 1 := ⟨(.second, 1), by decide⟩

example : (match Polygon.Presentation.compare occurrenceFirst occurrenceFirst with
    | .isTrue _ => true
    | .isFalse _ => false) = true := by decide

example : (match Polygon.Presentation.compare occurrenceFirst occurrenceSecond with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example (extra : Nat) (entry : Quarter.UnitCircuitQuarter × Nat)
    (first second : Polygon.Presentation.Valid extra entry) :
    (⟨entry, first⟩ : Polygon.Presentation.Display extra) = ⟨entry, second⟩ :=
  Subtype.ext rfl

example (extra : Nat) (index : Quarter.UnitCircuitQuarter × Nat) :
    Presentation.read (Presentation.quote (Polygon.indexedVertex extra index)) =
      Polygon.indexedVertex extra index :=
  Presentation.read_quote _

example (extra : Nat) (vertex : Basic.UnitVertex) (member : vertex ∈ Polygon.unitVertices extra) :
    ∃ original ∈ Polygon.unitVertices extra,
      Presentation.read (Presentation.quote original) = vertex :=
  ⟨vertex, member, Presentation.read_quote vertex⟩

example : (match Presentation.check (0 : Purelib.Data.Gaussian.Basic.Canonical) with
    | .valid _ => false
    | .notUnit _ => true) = true := by decide

example : (match Presentation.check (⟨1, 1⟩ : Purelib.Data.Gaussian.Basic.Canonical) with
    | .valid _ => false
    | .notUnit _ => true) = true := by decide

example : (match Presentation.check (Polygon.indexedVertex 1 (.first, 1)).value with
    | .valid _ => true
    | .notUnit _ => false) = true := by decide

example (extra : Nat) :
    Ordered.read
        (Ordered.quote (Polygon.unitVertices extra)) =
      Polygon.unitVertices extra := Ordered.read_quote _

example (extra : Nat) :
    (Ordered.quote (Polygon.unitVertices extra)).val = Polygon.vertices extra :=
  Ordered.quote_polygon extra

example (extra : Nat) :
    match Ordered.check (Polygon.vertices extra) with
    | .accepted _ => True
    | .notUnit _ _ => False := by
  cases Ordered.check (Polygon.vertices extra) with
  | accepted _ => trivial
  | notUnit index failed =>
    have valid : Ordered.Valid (Polygon.vertices extra) :=
      (Ordered.quote (Polygon.unitVertices extra)).property
    exact False.elim (failed (valid _ (List.getElem_mem index.isLt)))

example : match Ordered.check [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] with
    | .accepted _ => False
    | .notUnit index _ => index.val = 1 := by
  cases Ordered.check [⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩] with
  | accepted valid =>
    have nonunit : ¬ Presentation.Valid (Ordered.coordinates ⟨0, 0⟩) := by decide
    exact nonunit (valid ⟨0, 0⟩ (by decide))
  | notUnit index failed =>
    have notFirst : index.val ≠ 0 := by
      intro equal
      have same : index = ⟨0, by decide⟩ := Fin.ext equal
      subst index
      exact failed (by decide)
    have notLast : index.val ≠ 2 := by
      intro equal
      have same : index = ⟨2, by decide⟩ := Fin.ext equal
      subst index
      exact failed (by decide)
    have bound : index.val < 3 := index.isLt
    omega0

private def originalOrder : Ordered.Display :=
  Ordered.quote (Polygon.unitVertices 0)

private def rotatedOrder : Ordered.Display :=
  Ordered.quote (match Polygon.unitVertices 0 with
    | [] => []
    | first :: rest => rest ++ [first])

example : originalOrder.val = diamond := rfl

example : rotatedOrder.val = rotatedDiamond := by decide

example : (match Ordered.compare originalOrder rotatedOrder with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example : polygonSignedArea rotatedOrder.val =
    polygonSignedArea originalOrder.val := by
  change polygonSignedArea rotatedDiamond =
    polygonSignedArea diamond
  exact diamond_rotated_area

example : ((Polygon.unitVertices 0).all fun vertex =>
    match Presentation.check vertex.value with
    | .valid _ => true
    | .notUnit _ => false) = true := by decide

private def east : Presentation.Display := ⟨⟨1, 0⟩, by decide⟩

private def north : Presentation.Display := ⟨⟨0, 1⟩, by decide⟩

example : (match Presentation.compare east east with
    | .isTrue _ => true
    | .isFalse _ => false) = true := by decide

example : (match Presentation.compare east north with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example (display : Presentation.Display) : Presentation.quote (Presentation.read display) = display :=
  Presentation.quote_read display

example (point : Purelib.Data.Gaussian.Basic.Canonical)
    (first second : Purelib.Data.Gaussian.Norm.Basic.normSq point = 1) :
    (⟨point, first⟩ : Basic.UnitVertex) = ⟨point, second⟩ :=
  Basic.UnitVertex.eq_of_value_eq rfl

example (left right : Presentation.Display) :
    Presentation.Same left right ↔ Presentation.read left = Presentation.read right :=
  Presentation.same_iff_read_eq left right

example (extra : Nat) : (Polygon.vertices extra).length = 4 * (extra + 1) :=
  Polygon.vertices_length extra

example (extra : Nat) (point : Plane.Point Fraction.Rational) (member : point ∈ Polygon.vertices extra) :
    Plane.Point.Quadrance.quadrance ⟨0, 0⟩ point = 1 := Polygon.vertices_unit extra point member

example (extra : Nat) (point : Plane.Point Fraction.Rational) (member : point ∈ Polygon.vertices extra) :
    ∃ entry ∈ Polygon.indices extra, entry.2 < extra + 1 ∧
      point = Polygon.planePoint (Polygon.indexedVertex extra entry).value :=
  Polygon.vertices_origin extra point member

example (extra : Nat) :
    (Polygon.indexedVertex extra (.fourth, extra + 1)).value =
      (Polygon.indexedVertex extra (.first, 0)).value := (Polygon.indexed_joins extra).2.2.2

example (extra index : Nat) (quarter : Quarter.UnitCircuitQuarter) :
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (Polygon.planePoint (Polygon.indexedVertex extra (quarter, index)).value)
      (Polygon.planePoint (Polygon.indexedVertex extra (quarter, index + 1)).value) :=
  Polygon.indexed_edge_area_pos extra index quarter

example (extra : Nat) :
    0 < Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
      (Polygon.planePoint (Polygon.indexedVertex extra (.fourth, extra)).value)
      (Polygon.planePoint (Polygon.indexedVertex extra (.first, 0)).value) :=
  (Polygon.indexed_join_areas_pos extra).2.2.2

example : Triangles.SignedArea.triangleSignedArea ⟨0, 0⟩
    (Polygon.planePoint (Polygon.quarterPoint .second 0).value)
    (Polygon.planePoint (Polygon.quarterPoint .second (1 / 2)).value) = 2 / 5 := by
  rw [Polygon.quarter_triangle_area]
  decide

example (quarter : Quarter.UnitCircuitQuarter) (first second : Fraction.Rational) :
    Triangles.Quadrea.Basic.quadrea ⟨0, 0⟩
      (Polygon.planePoint (Polygon.quarterPoint quarter first).value)
      (Polygon.planePoint (Polygon.quarterPoint quarter second).value) =
      16 * ((second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1))) ^ 2 :=
  Polygon.quarter_triangle_quadrea quarter first second

example : polygonSignedArea
    Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon.diamond = 2 :=
  Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon.diamond_area

example : polygonSignedArea
    Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon.octagon = 14 / 5 :=
  Purelib.Examples.Geometry.Gaussian.UnitCircle.Polygon.octagon_area

example : Polygon.area 0 = 2 := by decide

example : Polygon.area 1 = 14 / 5 := by decide

example (extra : Nat) :
    Polygon.area extra = 4 * ((List.range (extra + 1)).map (fun index =>
      let first := Purelib.Integration.Partition.Uniform.Grid.point (extra + 1) index
      let second := Purelib.Integration.Partition.Uniform.Grid.point (extra + 1) (index + 1)
      (second - first) * (1 + first * second) /
        ((first ^ 2 + 1) * (second ^ 2 + 1)))).sum :=
  Polygon.area_eq_grid_sum extra

example : Polygon.area 0 = 2 := by
  rw [Polygon.area_eq_grid_sum]
  decide

example : Polygon.area 1 = 14 / 5 := by
  rw [Polygon.area_eq_grid_sum]
  decide

end TestPurelib.Geometry.Gaussian.UnitCircle.Polygon
