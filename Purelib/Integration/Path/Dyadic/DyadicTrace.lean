module

import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-! The recursive dyadic boundary has an exact finite indexed vertex trace.
The join vertex occurs once and every child edge contributes its full area. -/
namespace Purelib.Integration.Path.Dyadic.DyadicTrace

open Purelib.Data.List

open Purelib.Data.Rat in
/-- The rational carrier for dyadic subdivision parameters. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for traced areas. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
/-- List the successive terminal subdivision vertices of a dyadic interval in their original left-to-right recursion
order.

The initial endpoint is supplied separately; depth zero retains only the terminal endpoint. -/
@[expose] def tail : Nat → Fraction.Rational → Fraction.Rational → List Fraction.Rational
  | 0, _, last => [last]
  | depth + 1, first, last => Purelib.Integration.Path.Dyadic.DyadicTrace.tail depth first
    (PreparedBoxPartitions.midpoint first last) ++ Purelib.Integration.Path.Dyadic.DyadicTrace.tail depth
    (PreparedBoxPartitions.midpoint first last) last

/-- Read the last vertex of a list, using the retained starting vertex when the list is empty. -/
@[expose] def terminal {Vertex : Type} (first : Vertex) : List Vertex → Vertex
  | [] => first
  | head :: rest => Purelib.Integration.Path.Dyadic.DyadicTrace.terminal head rest

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Sum consecutive primitive-point edge areas from a retained starting vertex through an ordered vertex list.

The empty tail contributes zero. Every nonempty step adds the edge from the retained current vertex to the next original
vertex, with no implicit closing edge. -/
@[expose] def areaFrom {Vertex : Type} (values : Vertex → Stokes.PrimitivePoint) (first : Vertex) : List Vertex →
  Basic.Canonical
  | [] => 0
  | head :: rest => Stokes.edgeArea (values first) (values head) + Purelib.Integration.Path.Dyadic.DyadicTrace.areaFrom
    values head rest

open Purelib.Integration.Path in
/-- The terminal vertex of concatenated tails is obtained by continuing from the first tail's terminal vertex. -/
theorem terminal_append {Vertex : Type} (first : Vertex) (left right : List Vertex) :
    Dyadic.DyadicTrace.terminal first (left ++ right) = Dyadic.DyadicTrace.terminal (Dyadic.DyadicTrace.terminal first
      left) right := by
  induction left generalizing first with
  | nil => rfl
  | cons head rest ih => exact ih head

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The area of concatenated tails splits at the exact terminal vertex of the first tail.

The same retained terminal vertex supplies the starting point of the second
trace, so no closing edge or replacement join is introduced. -/
theorem areaFrom_append {Vertex : Type} (values : Vertex → Stokes.PrimitivePoint) (first : Vertex) (left right : List
  Vertex) :
    Dyadic.DyadicTrace.areaFrom values first (left ++ right) = Dyadic.DyadicTrace.areaFrom values first left +
      Dyadic.DyadicTrace.areaFrom values (Dyadic.DyadicTrace.terminal first left) right := by
  induction left generalizing first with
  | nil =>
      change _ = 0 + _
      exact (Purelib.Data.Gaussian.Basic.zero_add _).symm
  | cons head rest ih =>
      simp only [List.cons_append, Dyadic.DyadicTrace.areaFrom, Dyadic.DyadicTrace.terminal, ih]
      ring1

open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The dyadic subdivision tail ends at the original interval endpoint. -/
theorem tail_terminal (depth : Nat) (first last : Fraction.Rational) : Dyadic.DyadicTrace.terminal first
  (Dyadic.DyadicTrace.tail depth first last) = last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [Dyadic.DyadicTrace.tail, Dyadic.DyadicTrace.terminal_append, ih, ih]

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The ordered dyadic vertex trace has exactly the recursively defined dyadic boundary area.

At depth zero the one original edge supplies the area. Each successor
concatenates its original half traces at their common retained midpoint. -/
theorem tail_area (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last : Fraction.Rational) :
    Dyadic.DyadicTrace.areaFrom values first (Dyadic.DyadicTrace.tail depth first last) =
      DyadicBilinearBoundaryRibbon.dyadicArea values depth first last := by
  induction depth generalizing first last with
  | zero =>
      rewrite [Dyadic.DyadicTrace.tail, Dyadic.DyadicTrace.areaFrom,
        Dyadic.DyadicTrace.areaFrom, DyadicBilinearBoundaryRibbon.dyadicArea_zero]
      exact Purelib.Data.Gaussian.Basic.add_zero _
  | succ depth ih =>
    rw [Dyadic.DyadicTrace.tail, Dyadic.DyadicTrace.areaFrom_append, Dyadic.DyadicTrace.tail_terminal, ih, ih,
      DyadicBilinearBoundaryRibbon.dyadicArea_succ]

/-- Read a bounded vertex from the retained starting vertex followed by its tail list. -/
@[expose] def indexed {Vertex : Type} (first : Vertex) (rest : List Vertex) (vertex : Fin (rest.length + 1)) : Vertex :=
  (first :: rest)[vertex]

section
open Purelib.Integration.Path
/-- The first indexed vertex is the original starting vertex. -/
theorem indexed_first {Vertex : Type} (first : Vertex) (rest : List Vertex) : Dyadic.DyadicTrace.indexed first rest 0 =
  first := rfl

/-- The last indexed vertex is the original trace's terminal vertex. -/
theorem indexed_last {Vertex : Type} (first : Vertex) (rest : List Vertex) :
    Dyadic.DyadicTrace.indexed first rest (Fin.last rest.length) = Dyadic.DyadicTrace.terminal first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons head rest ih => exact ih head

end

open Purelib.Algebra in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The indexed path area equals the ordered list trace area. -/
theorem indexed_area {Vertex : Type} (values : Vertex → Stokes.PrimitivePoint) (first : Vertex) (rest : List Vertex) :
    CenteredBilinearPath.area (fun vertex => values (Dyadic.DyadicTrace.indexed first rest vertex)) =
      Dyadic.DyadicTrace.areaFrom values first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons head rest ih =>
      rw [CenteredBilinearPath.area, FiniteSum.Fin.sumFin_succ]
      change Stokes.edgeArea (values first) (values head) +
        CenteredBilinearPath.area (fun vertex => values (Dyadic.DyadicTrace.indexed head rest vertex)) = _
      rw [ih]
      rfl

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The indexed dyadic trace area equals the original recursive dyadic boundary area. -/
theorem indexed_dyadic_area (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    CenteredBilinearPath.area (fun vertex => values (Dyadic.DyadicTrace.indexed first (Dyadic.DyadicTrace.tail depth
      first last) vertex)) = DyadicBilinearBoundaryRibbon.dyadicArea values depth first last :=
  (Dyadic.DyadicTrace.indexed_area values first _).trans (Dyadic.DyadicTrace.tail_area values depth first last)

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
/-- Every retained dyadic tail vertex lies between the ordered original interval endpoints.

The original interval order bounds its midpoint and both child intervals.
Membership follows the actual concatenated tails without replacing the vertices. -/
theorem tail_inside (depth : Nat) {first last : Fraction.Rational} (ordered : first ≤ last)
    {parameter : Fraction.Rational} (member : parameter ∈ Dyadic.DyadicTrace.tail depth first last) : first ≤ parameter
      ∧ parameter ≤ last := by
  induction depth generalizing first last with
  | zero =>
      have equal : parameter = last := Membership.mem_singleton.mp member
      subst parameter
      exact ⟨ordered, le_rfl⟩
  | succ depth ih =>
      have between := PreparedBoxPartitions.midpoint_between ordered
      rcases Membership.mem_append.mp member with left | right
      · have bounded := ih between.1 left
        exact ⟨bounded.1, bounded.2.trans between.2⟩
      · have bounded := ih between.2 right
        exact ⟨between.1.trans bounded.1, bounded.2⟩

open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Every indexed dyadic trace vertex lies in the original ordered interval. -/
theorem indexed_inside (depth : Nat) {first last : Fraction.Rational} (ordered : first ≤ last)
    (vertex : Fin ((Dyadic.DyadicTrace.tail depth first last).length + 1)) :
    first ≤ Dyadic.DyadicTrace.indexed first (Dyadic.DyadicTrace.tail depth first last) vertex ∧
      Dyadic.DyadicTrace.indexed first (Dyadic.DyadicTrace.tail depth first last) vertex ≤ last := by
  have member : Dyadic.DyadicTrace.indexed first (Dyadic.DyadicTrace.tail depth first last) vertex ∈ first ::
    Dyadic.DyadicTrace.tail depth first last :=
    List.getElem_mem _
  rcases Membership.mem_cons.mp member with equal | member
  · rw [equal]
    exact ⟨le_rfl, ordered⟩
  · exact Dyadic.DyadicTrace.tail_inside depth ordered member

end Purelib.Integration.Path.Dyadic.DyadicTrace
