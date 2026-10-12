module
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Grouped paired areas retain all internal excursions and block totals. -/
namespace Purelib.Integration.Path.PairedAreaBlocks

open Purelib.Data.List

open Purelib.Integration.Path.PairedIncrementArea (Coordinate total area terms area_bound Summary)

section
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- Concatenation adds the paired primitive totals of both increment lists.

The two coordinate sums retain the original left and right spines. Their
ordered concatenation gives the same paired primitive total. -/
theorem total_append (first last : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (first ++ last) = (PairedIncrementArea.total first).add (PairedIncrementArea.total last)
      := by
  unfold PairedIncrementArea.total
  simp only [Map.map_append, IncrementArea.sum_append, Stokes.PrimitivePoint.add, -eq_self, -iff_self]
  rfl

/-- The total of flattened paired blocks equals the total of their exact ordered block totals. -/
theorem total_flatten (blocks : List (List Stokes.PrimitivePoint)) :
    PairedIncrementArea.total blocks.flatten = PairedIncrementArea.total (blocks.map PairedIncrementArea.total) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    rw [List.flatten_cons, PairedAreaBlocks.total_append, ih]
    rfl

/-- Prepending a paired increment adds its directed area against the exact tail total. -/
theorem area_cons (first : Stokes.PrimitivePoint) (rest : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (first :: rest) = Stokes.edgeArea first (PairedIncrementArea.total rest) +
      PairedIncrementArea.area rest := rfl

end

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- Concatenation adds the original paired areas and the directed cross-area of their exact totals. -/
theorem area_append (first last : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (first ++ last) = PairedIncrementArea.area first + PairedIncrementArea.area last +
      Stokes.edgeArea (PairedIncrementArea.total first) (PairedIncrementArea.total last) := by
  induction first with
  | nil =>
    simp only [List.nil_append, PairedIncrementArea.area, PairedIncrementArea.terms,
      Data.Gaussian.Norm.Sum.Basic.gaussianSum,
      PairedIncrementArea.total, List.map_nil, Stokes.edgeArea]; ring1
  | cons value rest ih =>
    rw [List.cons_append, PairedAreaBlocks.area_cons, PairedAreaBlocks.area_cons, ih, PairedAreaBlocks.total_append]
    change Stokes.edgeArea value ((PairedIncrementArea.total rest).add (PairedIncrementArea.total last)) +
      (PairedIncrementArea.area rest + PairedIncrementArea.area last + Stokes.edgeArea (PairedIncrementArea.total rest)
        (PairedIncrementArea.total last)) =
      (Stokes.edgeArea value (PairedIncrementArea.total rest) + PairedIncrementArea.area rest) +
        PairedIncrementArea.area last + Stokes.edgeArea (value.add (PairedIncrementArea.total rest))
        (PairedIncrementArea.total last)
    simp only [Stokes.edgeArea, Stokes.PrimitivePoint.add]
    ring1

/-- Flattened paired area splits into the sum of original block areas and the area of their ordered totals. -/
theorem area_flatten (blocks : List (List Stokes.PrimitivePoint)) :
    PairedIncrementArea.area blocks.flatten = Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      PairedIncrementArea.area) +
      PairedIncrementArea.area (blocks.map PairedIncrementArea.total) := by
  induction blocks with
  | nil => change (0 : Basic.Canonical) = 0 + 0; ring1
  | cons block rest ih =>
    simp only [List.flatten_cons, List.map_cons, PairedAreaBlocks.area_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
      PairedAreaBlocks.area_cons, ih, PairedAreaBlocks.total_flatten]
    ring1

end

open Purelib.Approximation.Rational in
open Purelib.Integration.Path in
/-- The squared dyadic count cancels quarter-radius decay while preserving the original density and movement factors. -/
private theorem dyadic_weight_cancel (density movement : PairedIncrementArea.Coordinate) (depth : Nat) :
    (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) ^ 2 * (density * Geometric.Basic.quarterRadius movement
      depth)) = density * movement := by
  calc
    _ = density * (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) *
        (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) * Geometric.Basic.quarterRadius movement depth)) := by
          ring1
    _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Separate retained block-area and block-total bounds control the flattened paired area.

The estimate preserves the original ordered blocks and distinct squared-count internal and fourth-power total
contributions. -/
theorem blocks_area_bound (blocks : List (List Stokes.PrimitivePoint)) {areaBound totalBound :
  PairedIncrementArea.Coordinate}
    (totalNonnegative : 0 ≤ totalBound)
    (areas : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area block) ≤ areaBound)
    (totals : ∀ block ∈ blocks, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total block) totalBound)
      :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area blocks.flatten) ≤ 2 *
      ((blocks.length : PairedIncrementArea.Coordinate) ^ 2 * areaBound + 4 * ((blocks.length :
        PairedIncrementArea.Coordinate) ^ 2 * totalBound) ^ 2) := by
  rw [PairedAreaBlocks.area_flatten]
  have internal := Norm.Sum.Bounds.normSq_sum_le (blocks.map PairedIncrementArea.area) areaBound (by
    intro value member
    obtain ⟨block, inBlocks, rfl⟩ := Map.mem_map.mp member
    exact areas block inBlocks)
  have coarse := PairedIncrementArea.area_bound (blocks.map PairedIncrementArea.total) totalNonnegative (by
    intro value member
    obtain ⟨block, inBlocks, rfl⟩ := Map.mem_map.mp member
    exact totals block inBlocks)
  rw [Map.length_map] at internal coarse
  have sum := add_le_add internal coarse
  calc
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      PairedIncrementArea.area)) +
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (blocks.map PairedIncrementArea.total))) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((blocks.length : PairedIncrementArea.Coordinate) * ((blocks.length : PairedIncrementArea.Coordinate) *
      areaBound) +
        4 * ((blocks.length : PairedIncrementArea.Coordinate) ^ 2 * totalBound) ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide)
    _ = _ := by ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Dyadic count and radius scaling bound the total internal-area contribution by four times density-times-movement
squared. -/
private theorem dyadic_internal_area_bound {density movement : PairedIncrementArea.Coordinate}
    (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤ movement) (depth : Nat) :
    (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) ^ 2 * (4 * (density * Geometric.Basic.quarterRadius movement
      depth) ^ 2)) ≤
      4 * (density * movement) ^ 2 := by
  have boundLe : density * Geometric.Basic.quarterRadius movement depth ≤ density * movement :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Geometric.Basic.quarterRadius_le_scale movementNonnegative depth) densityNonnegative
  have product : (density * movement) * (density * Geometric.Basic.quarterRadius movement depth) ≤ (density * movement)
    * (density * movement) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct boundLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative movementNonnegative)
  calc
    _ = 4 * ((((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) ^ 2 * (density * Geometric.Basic.quarterRadius
      movement depth)) *
        (density * Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = 4 * ((density * movement) * (density * Geometric.Basic.quarterRadius movement depth)) := by
      rw [PairedAreaBlocks.dyadic_weight_cancel]
    _ ≤ 4 * ((density * movement) * (density * movement)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)
    _ = _ := by ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- A dyadic family of bounded paired blocks has flattened area norm at most sixteen times density-times-movement
squared.

The original block count is exactly two to the retained depth, and both density and movement are nonnegative. -/
theorem dyadic_blocks_area_bound (blocks : List (List Stokes.PrimitivePoint)) (depth : Nat) (count : blocks.length = 2 ^
  depth)
    {density movement : PairedIncrementArea.Coordinate} (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤
      movement)
    (areas : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area block) ≤ 4 * (density *
      Geometric.Basic.quarterRadius movement depth) ^ 2)
    (totals : ∀ block ∈ blocks, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total block) (density *
      Geometric.Basic.quarterRadius movement depth)) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area blocks.flatten) ≤ 16 * (density * movement) ^ 2 := by
  have nonnegative : 0 ≤ density * Geometric.Basic.quarterRadius movement depth :=
    Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
    (Geometric.Basic.quarterRadius_nonneg movementNonnegative depth)
  have estimate := PairedAreaBlocks.blocks_area_bound blocks nonnegative areas totals
  rw [count, PairedAreaBlocks.dyadic_weight_cancel density movement depth] at estimate
  have internal := PairedAreaBlocks.dyadic_internal_area_bound densityNonnegative movementNonnegative depth
  have sum : (((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) ^ 2 * (4 * (density * Geometric.Basic.quarterRadius
    movement depth) ^ 2)) +
      4 * (density * movement) ^ 2 ≤ 4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2 :=
    add_le_add internal (le_refl (4 * (density * movement) ^ 2))
  have scaled : 2 * ((((2 ^ depth : Nat) : PairedIncrementArea.Coordinate) ^ 2 * (4 * (density *
    Geometric.Basic.quarterRadius movement depth) ^ 2)) +
      4 * (density * movement) ^ 2) ≤ 2 * (4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide)
  have result : 2 * (4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2) = 16 * (density * movement) ^ 2 := by
    ring1
  exact estimate.trans (scaled.trans_eq result)

open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- Combine the exact two retained paired summaries using their cached totals, areas and directed cross-area term. -/
@[expose] def Summary.append {first last : List Stokes.PrimitivePoint} (left : PairedIncrementArea.Summary first) (right
  : PairedIncrementArea.Summary last) :
    PairedIncrementArea.Summary (first ++ last) where
  totalValue := left.totalValue.add right.totalValue
  total_eq := by rw [left.total_eq, right.total_eq, PairedAreaBlocks.total_append]
  areaValue := left.areaValue + right.areaValue + Stokes.edgeArea left.totalValue right.totalValue
  area_eq := by rw [left.area_eq, right.area_eq, left.total_eq, right.total_eq, PairedAreaBlocks.area_append]

end Purelib.Integration.Path.PairedAreaBlocks
