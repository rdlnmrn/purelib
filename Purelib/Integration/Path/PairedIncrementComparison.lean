module

import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# Comparison of paired increment areas

An ordered pair list retains each first and second primitive reading. Difference
terms use their exact separate tail totals; their sum is the signed difference
of the two increment areas. Count-based and dyadic estimates keep separate
magnitude and pointwise error bounds on those same retained pairs.
-/
namespace Purelib.Integration.Path.PairedIncrementComparison

open Purelib.Data.List

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The total of original paired primitive differences equals the difference of their two retained totals. -/
theorem total_differences (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)) :
    PairedIncrementArea.total (pairs.map (fun pair => Stokes.PrimitivePoint.sub pair.1 pair.2)) =
      Stokes.PrimitivePoint.sub (PairedIncrementArea.total (pairs.map Prod.fst)) (PairedIncrementArea.total (pairs.map
        Prod.snd)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    change (Stokes.PrimitivePoint.sub pair.1 pair.2).add (PairedIncrementArea.total (rest.map (fun pair =>
      Stokes.PrimitivePoint.sub pair.1 pair.2))) =
      Stokes.PrimitivePoint.sub (pair.1.add (PairedIncrementArea.total (rest.map Prod.fst))) (pair.2.add
        (PairedIncrementArea.total (rest.map Prod.snd)))
    rw [ih]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> simp only [Stokes.PrimitivePoint.add, Stokes.PrimitivePoint.sub] <;>
      ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Retain each pair's area difference against the respective exact original tail totals. -/
private def differenceTerms : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint) → List Basic.Canonical
  | [] => []
  | pair :: rest =>
      (Stokes.edgeArea pair.1 (PairedIncrementArea.total (rest.map Prod.fst)) - Stokes.edgeArea pair.2
        (PairedIncrementArea.total (rest.map Prod.snd))) ::
        Purelib.Integration.Path.PairedIncrementComparison.differenceTerms rest

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The retained area-difference term list has exactly the original pair count. -/
private theorem differenceTerms_length (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)) :
    (PairedIncrementComparison.differenceTerms pairs).length = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The retained difference terms sum to the exact difference of the original two paired path areas. -/
private theorem differenceTerms_sum (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (PairedIncrementComparison.differenceTerms pairs) =
      PairedIncrementArea.area
      (pairs.map Prod.fst) - PairedIncrementArea.area (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | cons pair rest ih =>
    simp only [PairedIncrementComparison.differenceTerms, List.map_cons, PairedAreaBlocks.area_cons,
      Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]
    ring1

open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- A pointwise bound and length capacity bound a mapped paired total by count squared times the allowance.

Every mapped point retains a source pair and its membership certificate. The
structural map preserves the pair count, so the supplied capacity and
nonnegative pointwise bound apply to the exact mapped total. -/
private theorem total_map_bound {pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)}
    (value : Stokes.PrimitivePoint × Stokes.PrimitivePoint → Stokes.PrimitivePoint) {bound :
      PairedIncrementArea.Coordinate}
    (nonnegative : 0 ≤ bound) (bounded : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (value pair) bound)
    {count : Nat} (countLe : pairs.length ≤ count) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total (pairs.map value)) ((count :
      PairedIncrementArea.Coordinate)^2 * bound) :=
  PairedIncrementArea.total_bound nonnegative (by
    intro point member
    obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
    exact bounded pair inPairs) (by simpa only [Map.length_map] using countLe)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Each retained area-difference term obeys the count-squared error-times-magnitude estimate.

Both original point families remain bounded separately, and the exact pair differences retain their common nonnegative
error allowance. -/
private theorem differenceTerms_bounded {pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)}
    {error bound : PairedIncrementArea.Coordinate} (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub pair.1 pair.2)
      error)
    (leftBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 bound) (rightBound : ∀ pair ∈ pairs,
      PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 bound)
    {count : Nat} (countLe : pairs.length ≤ count) :
    ∀ value ∈ PairedIncrementComparison.differenceTerms pairs, Data.Gaussian.Norm.Basic.normSq value ≤ 16 * (count :
      PairedIncrementArea.Coordinate)^2 * error * bound := by
  induction pairs with
  | nil => intro value member; cases member
  | cons pair rest ih =>
    have tailCount : rest.length ≤ count := (Nat.le_succ _).trans countLe
    have tailErrors := fun other member => errors other (List.mem_cons_of_mem pair member)
    have tailLeft := fun other member => leftBound other (List.mem_cons_of_mem pair member)
    have tailRight := fun other member => rightBound other (List.mem_cons_of_mem pair member)
    intro value member
    rcases Membership.mem_cons.mp member with rfl | member
    · have first := PrimitiveAreaBounds.PrimitivePoint.area_bound (errors pair (List.mem_cons_self ..))
        (PairedIncrementComparison.total_map_bound Prod.fst boundNonnegative tailLeft tailCount)
      have last := PrimitiveAreaBounds.PrimitivePoint.area_bound (rightBound pair (List.mem_cons_self ..))
        (PairedIncrementComparison.total_map_bound (fun pair => Stokes.PrimitivePoint.sub pair.1 pair.2)
          errorNonnegative tailErrors tailCount)
      rw [PairedIncrementComparison.total_differences] at last
      rw [← Norm.Basic.normSq_eq_canonical] at first last
      have expanded : Stokes.edgeArea pair.1 (PairedIncrementArea.total (rest.map Prod.fst)) - Stokes.edgeArea pair.2
        (PairedIncrementArea.total (rest.map Prod.snd)) =
          Stokes.edgeArea (Stokes.PrimitivePoint.sub pair.1 pair.2) (PairedIncrementArea.total (rest.map Prod.fst)) +
            Stokes.edgeArea pair.2 (Stokes.PrimitivePoint.sub (PairedIncrementArea.total (rest.map Prod.fst))
              (PairedIncrementArea.total (rest.map Prod.snd))) := by
        simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
        ring1
      rw [expanded]
      exact (Norm.Bounds.normSq_add_le_two _ _).trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first last) (by decide)).trans_eq (by
          ring1))
    · exact ih tailErrors tailLeft tailRight tailCount value member

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The original paired path-area difference has squared norm at most sixteen times count to the fourth power times
error and magnitude.

The ordered pairs retain separate left and right bounds and a common pointwise difference certificate. -/
theorem area_difference_bound (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)) {error bound :
  PairedIncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub pair.1 pair.2)
      error)
    (leftBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 bound) (rightBound : ∀ pair ∈ pairs,
      PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 bound) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (pairs.map Prod.fst) - PairedIncrementArea.area (pairs.map
      Prod.snd)) ≤
      16 * (pairs.length : PairedIncrementArea.Coordinate)^4 * error * bound := by
  rw [← PairedIncrementComparison.differenceTerms_sum]
  have estimate := Norm.Sum.Bounds.normSq_sum_le (PairedIncrementComparison.differenceTerms pairs) _
    (PairedIncrementComparison.differenceTerms_bounded errorNonnegative boundNonnegative errors leftBound rightBound
      (count := pairs.length) le_rfl)
  rw [PairedIncrementComparison.differenceTerms_length] at estimate
  exact estimate.trans_eq (by ring1)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Dyadically scaled paired errors and magnitudes give a depth-independent area-difference estimate.

The exact count is two to the retained depth; the bound keeps both original densities and the square of the movement
scale. -/
theorem dyadic_area_difference_bound (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint))
    (depth : Nat) (count : pairs.length = 2 ^ depth) {movement errorDensity density : PairedIncrementArea.Coordinate}
    (movementNonnegative : 0 ≤ movement) (errorNonnegative : 0 ≤ errorDensity) (densityNonnegative : 0 ≤ density)
    (errors : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub pair.1 pair.2)
      (errorDensity * Geometric.Basic.quarterRadius movement depth))
    (leftBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 (density *
      Geometric.Basic.quarterRadius movement depth))
    (rightBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 (density *
      Geometric.Basic.quarterRadius movement depth)) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (pairs.map Prod.fst) - PairedIncrementArea.area (pairs.map
      Prod.snd)) ≤
      16 * errorDensity * density * movement^2 := by
  have distanceNonnegative := Geometric.Basic.quarterRadius_nonneg movementNonnegative depth
  have bounded := PairedIncrementComparison.area_difference_bound pairs (Fraction.Order.Arithmetic.mul_nonneg_direct
    errorNonnegative distanceNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative distanceNonnegative) errors leftBound rightBound
  rw [count] at bounded
  have identity : 16 * (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate)^4) *
      (errorDensity * Geometric.Basic.quarterRadius movement depth) *
      (density * Geometric.Basic.quarterRadius movement depth) =
        16 * errorDensity * density * movement^2 := by
    calc
      _ = 16 * errorDensity * density *
        ((((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) *
          (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) * Geometric.Basic.quarterRadius movement depth))^2) :=
            by ring1
      _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]
  exact bounded.trans_eq identity

end Purelib.Integration.Path.PairedIncrementComparison

end
