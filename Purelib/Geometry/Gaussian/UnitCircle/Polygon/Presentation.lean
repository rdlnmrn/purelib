module

public import Purelib.Data.Presentation
public import Purelib.Geometry.Gaussian.UnitCircle.Polygon
public import Purelib.Geometry.Gaussian.UnitCircle.Presentation
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Search
import Purelib.Data.List.Attach

namespace Purelib.Geometry.Gaussian.UnitCircle.Polygon.Presentation

open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter

/-- An original quarter/index pair is admissible when its index is below the cell count. -/
@[expose] public def Valid (extra : Nat) (entry : UnitCircuitQuarter × Nat) : Prop :=
  entry.2 < extra + 1

set_option genInjectivity false in
/-- The result of checking an original polygon quarter/index pair. -/
public inductive Check (extra : Nat) (entry : UnitCircuitQuarter × Nat) where
  /-- The occurrence lies within the original quarter grid. -/ | valid (bound : Valid extra entry)
  /-- The index is at or beyond the original quarter cell count. -/ | outOfRange (bound : extra + 1 ≤ entry.2)

/-- Check the original index bound, retaining a proof in either branch. -/
@[expose] public def check (extra : Nat) (entry : UnitCircuitQuarter × Nat) : Check extra entry :=
  if bound : entry.2 < extra + 1 then .valid bound else .outOfRange (Nat.le_of_not_gt bound)

/-- Decide admissibility using the typed original-index checker. -/
@[expose] public def recognize (extra : Nat) (entry : UnitCircuitQuarter × Nat) :
    Decidable (Valid extra entry) :=
  match check extra entry with
  | .valid bound => .isTrue bound
  | .outOfRange bound => .isFalse (Nat.not_lt_of_ge bound)

/-- Decide the bound of an original polygon occurrence. -/
public instance (extra : Nat) (entry : UnitCircuitQuarter × Nat) : Decidable (Valid extra entry) :=
  recognize extra entry

/-- Original quarter/index pairs with their actual finite bound. -/
public abbrev Display (extra : Nat) := {entry : UnitCircuitQuarter × Nat // Valid extra entry}

/-- The finite bound accepts exactly the occurrences retained by the original polygon.

Every quarter maps the same finite range to its own original pairs. The reverse
implication uses the polygon owner's existing bound on its retained indices. -/
public theorem valid_iff_mem (extra : Nat) (entry : UnitCircuitQuarter × Nat) :
    Valid extra entry ↔ entry ∈ Polygon.indices extra := by
  constructor
  · intro bound
    rcases entry with ⟨quarter, index⟩
    have mapped (q : UnitCircuitQuarter) : (q, index) ∈
        (List.range (extra + 1)).map (fun i => (q, i)) :=
      Map.mem_map.mpr ⟨index, Range.Basic.mem_range.mpr bound, rfl⟩
    unfold Polygon.indices
    cases quarter with
    | first => exact Membership.mem_append.mpr (.inl (Membership.mem_append.mpr
        (.inl (Membership.mem_append.mpr (.inl (mapped .first))))))
    | second => exact Membership.mem_append.mpr (.inl (Membership.mem_append.mpr
        (.inl (Membership.mem_append.mpr (.inr (mapped .second))))))
    | third => exact Membership.mem_append.mpr (.inl (Membership.mem_append.mpr (.inr (mapped .third))))
    | fourth => exact Membership.mem_append.mpr (.inr (mapped .fourth))
  · exact Polygon.indices_bound extra entry

/-- Quote an actual retained polygon occurrence using its original membership proof. -/
@[expose] public def quote (extra : Nat) (entry : UnitCircuitQuarter × Nat)
    (member : entry ∈ Polygon.indices extra) : Display extra :=
  ⟨entry, Polygon.indices_bound extra entry member⟩

/-- The accepted pair is a member of the original ordered polygon index list. -/
public theorem member (extra : Nat) (display : Display extra) : display.val ∈ Polygon.indices extra :=
  (valid_iff_mem extra display.val).mp display.property

/-- The quoted occurrence retains the exact original quarter/index pair. -/
public theorem quote_val (extra : Nat) (entry : UnitCircuitQuarter × Nat)
    (proof : entry ∈ Polygon.indices extra) : (quote extra entry proof).val = entry := rfl

/-- Quoting an accepted occurrence recovers its pair and bound up to proof irrelevance. -/
public theorem quote_member (extra : Nat) (display : Display extra) :
    quote extra display.val (member extra display) = display := by
  apply Subtype.ext
  rfl

/-- The vertex of an accepted occurrence is the original indexed polygon vertex. -/
@[expose] public def vertex (extra : Nat) (display : Display extra) : Basic.UnitVertex :=
  Polygon.indexedVertex extra display.val

/-- Two accepted occurrences are the same exactly when their original pairs agree. -/
@[expose] public def Same {extra : Nat} (left right : Display extra) : Prop := left.val = right.val

/-- Decide occurrence identity by comparing the original quarter and natural index. -/
@[expose] public def compare {extra : Nat} (left right : Display extra) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-!
## Polygon occurrences

The typed input is the original quarter and natural index; `check` accepts
exactly those below `extra + 1` and retains a proof of the failed bound on
rejection. `valid_iff_mem` relates this finite test to the original ordered
`indices` list. `quote` retains each original pair and `vertex` calls the
original `indexedVertex` on it. `compare` decides pair identity, which is
separate from equality of vertex coordinates or signed areas. Natural order,
the four-quarter equality and the original finite list constructions supply
the decisions and membership laws; the proof-system and runtime boundaries
are inherited separately.
-/
/-- The explicit finite presentation of original quarter/index occurrences. -/
@[expose] public def occurrence (extra : Nat) : Purelib.Data.Presentation (UnitCircuitQuarter × Nat) where
  Valid := Valid extra
  recognize := recognize extra
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

namespace Ordered

open Purelib.Data.Rat
open Purelib.Geometry

/-- An ordered polygon display is the original finite list of Cartesian points. -/
public abbrev Code := List (Plane.Point Fraction.Rational)

/-- Read Cartesian coordinates as the original Gaussian rational. -/
@[expose] public def coordinates (point : Plane.Point Fraction.Rational) :
    Purelib.Data.Gaussian.Basic.Canonical := ⟨point.x, point.y⟩

/-- Every retained point of the ordered display has unit quadrance. -/
@[expose] public def Valid (points : Code) : Prop :=
  ∀ point ∈ points, UnitCircle.Presentation.Valid (coordinates point)

set_option genInjectivity false in
/-- A list check returns all unit certificates or the bounded nonunit occurrence. -/
public inductive Check (points : Code) where
  /-- Each point is an exact unit vertex. -/ | accepted (valid : Valid points)
  /-- This original bounded position is not on the unit circle. -/
  | notUnit (index : Fin points.length)
      (failed : ¬ UnitCircle.Presentation.Valid (coordinates (points.get index)))

/-- Check the finite ordered list using the original unit-vertex decision. -/
public def check (points : Code) : Check points :=
  match result : Purelib.Data.List.Search.firstOccurrence
      (fun point => ¬ UnitCircle.Presentation.Valid (coordinates point))
      (fun point => inferInstance) points with
  | some occurrence =>
      .notUnit occurrence.index (by
        rw [List.get_eq_getElem, ← occurrence.entry_eq]
        exact occurrence.accepted)
  | none =>
      have valid : Valid points := by
        intro point member
        by_cases unit : UnitCircle.Presentation.Valid (coordinates point)
        · exact unit
        · have selected := Purelib.Data.List.Search.firstAccepted
            (fun point => ¬ UnitCircle.Presentation.Valid (coordinates point))
            (fun point => inferInstance) points ⟨point, member, unit⟩
          have impossible : none = some selected.val := result.symm.trans selected.property
          cases impossible
      .accepted valid

/-- Decide the list invariant through its located typed checker. -/
public def recognize (points : Code) : Decidable (Valid points) :=
  match check points with
  | .accepted valid => .isTrue valid
  | .notUnit index failed => .isFalse (fun valid =>
      failed (valid (points.get index) (List.getElem_mem index.isLt)))

/-- An accepted ordered list retains its original points and their unit invariant. -/
public abbrev Display := {points : Code // Valid points}

/-- Build one original unit vertex from its checked Cartesian coordinates. -/
@[expose] public def readVertex (point : Plane.Point Fraction.Rational)
    (unit : UnitCircle.Presentation.Valid (coordinates point)) : Basic.UnitVertex :=
  UnitCircle.Presentation.read ⟨coordinates point, unit⟩

/-- Construct the original certified vertex list from the accepted points. -/
@[expose] public def read (display : Display) : List Basic.UnitVertex :=
  display.val.attach.map (fun (point : {value // value ∈ display.val}) =>
    readVertex point.val (display.property point.val point.property))

/-- Project the exact ordered Cartesian points from existing unit vertices. -/
@[expose] public def quote (vertices : List Basic.UnitVertex) : Display :=
  ⟨vertices.map (fun vertex => Polygon.planePoint vertex.value), by
    intro point member
    obtain ⟨vertex, _, same⟩ := Map.mem_map.mp member
    subst point
    cases vertex with
    | mk value unit => cases value; exact unit⟩

/-- Reading preserves the exact ordered Cartesian point list. -/
public theorem read_points (display : Display) :
    (read display).map (fun vertex => Polygon.planePoint vertex.value) = display.val := by
  unfold read
  rw [Map.map_map]
  calc
    _ = display.val.attach.map Subtype.val := by
      apply Map.map_congr_left
      intro point _
      cases point with
      | mk value property => cases value; rfl
    _ = display.val := Purelib.Data.List.attach_map_subtype_val display.val

/-- Projecting a certified vertex into the plane preserves its identity. -/
public theorem planePoint_injective : Function.Injective
    (fun vertex : Basic.UnitVertex => Polygon.planePoint vertex.value) := by
  intro left right same
  apply Basic.UnitVertex.eq_of_value_eq
  apply Purelib.Data.Gaussian.Basic.Canonical.ext
  · exact congrArg Plane.Point.x same
  · exact congrArg Plane.Point.y same

/-- Reading a quotation recovers the original ordered list of certified vertices. -/
public theorem read_quote (vertices : List Basic.UnitVertex) : read (quote vertices) = vertices := by
  apply (Map.map_inj_right planePoint_injective).mp
  exact read_points (quote vertices)

/-- Quoting a readback recovers the original ordered point display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  exact read_points display

/-- An actual indexed polygon quotes to its original Cartesian vertex list. -/
public theorem quote_polygon (extra : Nat) :
    (quote (Polygon.unitVertices extra)).val = Polygon.vertices extra := rfl

/-- Equality compares the retained ordered Cartesian points. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Decide list identity using the original point and finite-list decisions. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Ordered display equality is exactly equality of the original vertex lists. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    apply (Map.map_inj_right planePoint_injective).mp
    exact (read_points left).trans (same.trans (read_points right).symm)
  · intro same
    exact (read_points left).symm.trans
      ((congrArg (fun vertices => vertices.map (fun vertex => Polygon.planePoint vertex.value)) same).trans
        (read_points right))

/-!
The display is a finite ordered list of the Cartesian points used by the
polygon area owner. `check` uses the unit-vertex decision and returns the
original bounded position of a nonunit point. Its successful case supplies a
certificate for each point, while `read` constructs the existing unit vertices
and `quote` projects their retained coordinates. `read_quote`, `quote_read` and
`quote_polygon` link both lists to the original owners. `compare` decides
ordered list identity; cyclic rotation and equal signed area are separate
relations. The search and comparisons traverse finite lists and use the
existing rational decisions; proof-system and runtime boundaries are inherited.
-/

/-- The explicit presentation retains ordered point identity. -/
public def presentation : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Ordered

end Purelib.Geometry.Gaussian.UnitCircle.Polygon.Presentation
