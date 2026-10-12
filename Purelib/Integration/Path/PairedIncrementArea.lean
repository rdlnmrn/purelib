module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Paths.PathArea
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

public section

/-!
# Paired primitive increment areas

Each primitive increment retains two Gaussian coordinates. The area pairs each
increment with its exact tail displacement; the summary caches total displacement
and signed area in one structural traversal. Coordinate bounds and the retained
list count control that same area, including its dyadic specialization.
-/
namespace Purelib.Integration.Path.PairedIncrementArea

open Purelib.Data.List
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for paired increment areas. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The rational carrier for paired increment bounds. -/
abbrev Coordinate := Fraction.Rational

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Sum the two coordinates of the retained primitive-point increments separately. -/
@[expose] def total (values : List Stokes.PrimitivePoint) : PrimitivePoint :=
  ⟨gaussianSum (values.map Stokes.PrimitivePoint.left), Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map
    Stokes.PrimitivePoint.right)⟩

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Retain each primitive increment's edge area with the exact total of all later increments. -/
@[expose] def terms : List Stokes.PrimitivePoint → List Gaussian
  | [] => []
  | first :: rest => Stokes.edgeArea first (total rest) ::
    terms rest

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Sum the ordered primitive increment pair-area terms. -/
@[expose] def area (values : List Stokes.PrimitivePoint) : Gaussian := Data.Gaussian.Norm.Sum.Basic.gaussianSum
  (terms values)

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Accumulate the original primitive-point increments from the retained start and sum each consecutive edge area. -/
@[expose] def traceArea (start : Stokes.PrimitivePoint) : List Stokes.PrimitivePoint → Gaussian
  | [] => 0
  | value :: rest => Stokes.edgeArea start (start.add value) + traceArea
    (start.add value) rest

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The traced area is the increment area plus the starting point's edge area with total displacement. -/
theorem traceArea_eq (start : Stokes.PrimitivePoint) (values : List Stokes.PrimitivePoint) :
    traceArea start values = area values + Stokes.edgeArea start
      (total values) := by
  induction values generalizing start with
  | nil =>
    simp only [traceArea, area, terms,
      total, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Stokes.edgeArea]; ring1
  | cons value rest ih =>
    rw [traceArea, ih]
    change Stokes.edgeArea start (start.add value) + (area rest + Stokes.edgeArea (start.add value)
      (total rest)) =
      (Stokes.edgeArea value (total rest) + area rest) + Stokes.edgeArea start
        (value.add (total rest))
    simp only [Stokes.edgeArea, Stokes.PrimitivePoint.add]
    ring1

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The paired increment area equals the trace area starting at the zero primitive point.

The trace identity separates the increment area from the starting point's edge
contribution. A zero start makes that scalar contribution vanish. -/
theorem area_eq_trace (values : List Stokes.PrimitivePoint) : area values =
  traceArea Stokes.PrimitivePoint.zero values := by
  rw [traceArea_eq]
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.zero]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Uniform bounds and a length capacity control both coordinates of the paired total.

Mapping either retained coordinate preserves the increment count. The Gaussian
sum estimate applies separately to those two lists with their supplied pointwise
bounds and the same nonnegative allowance. -/
theorem total_bound {values : List Stokes.PrimitivePoint} {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Bounded value bound)
    {count : Nat} (countLe : values.length ≤ count) : Bounded
      (total values) ((count : Coordinate)^2 * bound) := by
  constructor
  · rw [← Norm.Basic.normSq_eq_canonical]
    apply IncrementArea.sum_bound_of_length nonnegative _ (by simpa only [Map.length_map] using countLe)
    intro value member
    obtain ⟨point, inValues, rfl⟩ := Map.mem_map.mp member
    simpa only [Norm.Basic.normSq_eq_canonical] using (bounded point inValues).1
  · rw [← Norm.Basic.normSq_eq_canonical]
    apply IncrementArea.sum_bound_of_length nonnegative _ (by simpa only [Map.length_map] using countLe)
    intro value member
    obtain ⟨point, inValues, rfl⟩ := Map.mem_map.mp member
    simpa only [Norm.Basic.normSq_eq_canonical] using (bounded point inValues).2

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The pair-area term list retains the original increment count. -/
private theorem terms_length (values : List Stokes.PrimitivePoint) : (terms values).length =
  values.length := by
  induction values with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon
/-- Each pair-area term is bounded by four times count squared times the coordinate bound squared.

The head pairs with the exact total of its retained tail. The tail's length
capacity and separate coordinate bounds give the edge estimate; structural
membership passes the unchanged remaining terms to the inductive certificate. -/
private theorem terms_bound {values : List Stokes.PrimitivePoint} {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Bounded value bound)
    {count : Nat} (countLe : values.length ≤ count) :
    ∀ term ∈ terms values, Data.Gaussian.Norm.Basic.normSq term ≤ 4 * (count :
      Coordinate)^2 * bound^2 := by
  induction values with
  | nil => intro term member; cases member
  | cons first rest ih =>
    have tailBound := fun value member => bounded value (List.mem_cons_of_mem first member)
    have tailCount : rest.length ≤ count := (Nat.le_succ _).trans countLe
    intro term member
    rcases Membership.mem_cons.mp member with rfl | inTail
    · have scalar := PrimitiveAreaBounds.PrimitivePoint.area_bound (bounded first (List.mem_cons_self ..))
        (total_bound nonnegative tailBound tailCount)
      rw [← Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans_eq (by ring1)
    · exact ih tailBound tailCount term inTail

/-- The paired increment area's squared norm is bounded by four times the squared count-squared allowance.

Each original primitive increment retains separate left and right coordinate bounds. The count is the exact retained
list length, with no identification of the paired coordinates. -/
theorem area_bound (values : List Stokes.PrimitivePoint) {bound : Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ value ∈ values, Bounded value bound) :
    Data.Gaussian.Norm.Basic.normSq (area values) ≤ 4 * ((values.length :
      Coordinate)^2 * bound)^2 := by
  have estimate := Norm.Sum.Bounds.normSq_sum_le (terms values) _
    (terms_bound nonnegative bounded (count := values.length) le_rfl)
  rw [terms_length] at estimate
  exact estimate.trans_eq (by ring1)

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- For exactly two-to-depth increments, quarter-radius coordinate bounds cancel the dyadic count factor.

Nonnegative density and movement give an area norm bound of four times their squared product, preserving the exact depth
and list count. -/
theorem dyadic_area_bound (values : List Stokes.PrimitivePoint) (depth : Nat)
    (count : values.length = 2 ^ depth) {density movement : Coordinate}
    (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤ movement)
    (bounded : ∀ value ∈ values,
      Bounded value (density * Geometric.Basic.quarterRadius movement depth)) :
    Data.Gaussian.Norm.Basic.normSq (area values) ≤ 4 * (density * movement)^2 := by
  have estimate := area_bound values (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
    (Geometric.Basic.quarterRadius_nonneg movementNonnegative depth)) bounded
  rw [count] at estimate
  have cancel : (((2 ^ depth : Nat) : Coordinate)^2 *
      (density * Geometric.Basic.quarterRadius movement depth)) = density * movement := by
    calc
      _ = density * (((2 ^ depth : Nat) : Coordinate) *
        (((2 ^ depth : Nat) : Coordinate) * Geometric.Basic.quarterRadius movement depth)) := by
          ring1
      _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]
  rwa [cancel] at estimate

set_option genInjectivity false in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Cached total primitive displacement and Gaussian area for the exact retained increment list.

The two coordinates of the displacement remain distinct, and both caches have exact original-list equalities. -/
structure Summary (values : List Stokes.PrimitivePoint) where
  /-- The retained paired total displacement. -/ totalValue : Stokes.PrimitivePoint
  /-- The paired total equals the exact original increment total. -/ total_eq : totalValue = total
    values
  /-- The retained Gaussian increment area. -/ areaValue : Gaussian
  /-- The retained area equals the exact original increment area. -/ area_eq : areaValue = area
    values

constructive_injectivity Summary

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Build the paired increment summary in one recursion, reusing each retained tail's total and area. -/
@[expose] def Summary.build : (values : List Stokes.PrimitivePoint) → Summary values
  | [] => ⟨PrimitivePoint.zero, rfl, 0, rfl⟩
  | first :: rest =>
    let tail := Summary.build rest
    { totalValue := first.add tail.totalValue
      total_eq := by rw [tail.total_eq]; rfl
      areaValue := Stokes.edgeArea first tail.totalValue + tail.areaValue
      area_eq := by rw [tail.total_eq, tail.area_eq]; rfl }

end Purelib.Integration.Path.PairedIncrementArea

end
