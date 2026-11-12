module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Area paid for finite connectors between retained blocks

A connector is prepended to the next block. Its area cost uses that block's
cached total, and the aggregate estimate pays both the internal corrections
and the polygon of block totals. No bound depends on the number of children
inside an individual block.
-/

namespace Purelib.Integration.Path.IncrementAreaJoins

open Purelib.Data.List

open Purelib.Integration.Path.IncrementArea

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Path.BoundaryRibbon (area area_bound)

namespace Summary

section
open Purelib.Integration.Path
/-- Prepend the exact connector to the original increment list and retain its updated total and area.

The construction reuses the original summary and adds the connector's boundary-area contribution against its retained
total. -/
@[expose] def prepend {increments : List Gaussian} (summary : Summary increments) (connector
  : Gaussian) :
    Summary (connector :: increments) where
  total := connector + summary.total
  total_eq := by rw [summary.total_eq]; rfl
  area := summary.area + area connector summary.total
  area_eq := by rw [summary.area_eq, summary.total_eq, pathArea_cons]

/-- Prepending a connector changes the retained total by exactly that connector. -/
theorem prepend_total_error {increments : List Gaussian} (summary : Summary increments)
  (connector : Gaussian) :
    (prepend summary connector).total - summary.total = connector := by
  change connector + summary.total - summary.total = connector
  ring1

end

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
/-- A connector with squared norm at most the error changes area by squared norm at most four times error times the
original total bound. -/
theorem prepend_area_error {increments : List Gaussian} (summary : Summary increments)
  (connector : Gaussian)
    {error bound : Coordinate} (small : Norm.Basic.normSq connector ≤ error) (bounded :
      Norm.Basic.normSq summary.total ≤ bound) :
    Norm.Basic.normSq ((prepend summary connector).area - summary.area) ≤ 4 *
      error
      * bound := by
  have difference : (prepend summary connector).area - summary.area = area
    connector summary.total := by
    change summary.area + area connector summary.total - summary.area = _
    ring1
  rw [difference]
  have product := Arithmetic.mul_le_mul_direct small bounded (Norm.Basic.normSq_nonneg summary.total)
    ((Norm.Basic.normSq_nonneg connector).trans small)
  calc
    _ ≤ 4 * Norm.Basic.normSq connector * Norm.Basic.normSq summary.total :=
      area_bound
      connector summary.total
    _ = 4 * (Norm.Basic.normSq connector * Norm.Basic.normSq summary.total) := by ring1
    _ ≤ 4 * (error * bound) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
          decide : (0 : Coordinate) ≤ 4)
    _ = 4 * error * bound := by ring1

/-- The prepended total has squared norm at most twice the sum of connector and original-total bounds. -/
theorem prepend_total_bound {increments : List Gaussian} (summary : Summary increments)
  (connector : Gaussian)
    {error bound : Coordinate} (small : Norm.Basic.normSq connector ≤ error) (bounded :
      Norm.Basic.normSq summary.total ≤ bound) :
    Norm.Basic.normSq (prepend summary connector).total ≤ 2 * (error + bound)
      :=
  (Norm.Bounds.normSq_add_le_two connector summary.total).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add small bounded) (by decide))

end Summary

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound the area change caused by prepending one small connector to each original block.

The exact ordered blocks and connectors remain fixed; the estimate retains separate squared-count area and fourth-power
total-interaction contributions. -/
theorem joined_blocks_area_bound (blocks : List (Gaussian × List Gaussian)) {error bound :
  Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (small : ∀ block ∈ blocks, Norm.Basic.normSq block.1 ≤ error)
    (bounded : ∀ block ∈ blocks, Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum block.2) ≤
      bound) :
    Norm.Basic.normSq (pathArea (blocks.map (fun block => block.1 :: block.2)).flatten -
      pathArea (blocks.map Prod.snd).flatten) ≤
      2 * ((blocks.length : Coordinate) ^ 2 * (4 * error * bound) +
        16 * (blocks.length : Coordinate) ^ 4 * error * (2 * (error + bound))) := by
  have sharedNonnegative : 0 ≤ 2 * (error + bound) :=
    Arithmetic.mul_nonneg_direct (by decide) (add_nonneg errorNonnegative boundNonnegative)
  have sourceBound : bound ≤ 2 * (error + bound) :=
    (le_add_of_nonneg_right (add_nonneg
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2) errorNonnegative)
        boundNonnegative)).trans_eq
      (by ring1)
  have estimate := IncrementAreaComparison.blocks_area_difference_bound (blocks.map (fun block => (block.1 :: block.2,
    block.2)))
    errorNonnegative sharedNonnegative (by
      intro pair member
      obtain ⟨block, inBlocks, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      let summary := Summary.build block.2
      have totalBound : Norm.Basic.normSq summary.total ≤ bound := summary.total_eq ▸ bounded block
        inBlocks
      have cost := Summary.prepend_area_error summary block.1 (small block inBlocks) totalBound
      rw [(Summary.prepend summary block.1).area_eq, summary.area_eq] at cost
      exact cost) (by
      intro pair member
      obtain ⟨block, inBlocks, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      change Norm.Basic.normSq (block.1 + Norm.Sum.Basic.gaussianSum block.2 -
        Norm.Sum.Basic.gaussianSum block.2) ≤ error
      rw [show block.1 + Norm.Sum.Basic.gaussianSum block.2 - Norm.Sum.Basic.gaussianSum
        block.2 = block.1 by
        ring1]
      exact small block inBlocks) (by
      intro pair member
      obtain ⟨block, inBlocks, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact (Norm.Bounds.normSq_add_le_two block.1 (Norm.Sum.Basic.gaussianSum block.2)).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (small block inBlocks) (bounded block
          inBlocks)) (by decide))) (by
      intro pair member
      obtain ⟨block, inBlocks, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact (bounded block inBlocks).trans sourceBound)
  simp only [Map.map_map, Map.length_map] at estimate
  dsimp only [Function.comp_def] at estimate
  exact estimate

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The difference between the joined and original block totals is exactly the ordered sum of their connectors. -/
private theorem connector_sum (blocks : List (Gaussian × List Gaussian)) :
    Norm.Sum.Basic.gaussianSum (blocks.map (fun block => block.1 :: block.2)).flatten -
      Norm.Sum.Basic.gaussianSum (blocks.map Prod.snd).flatten =
      Norm.Sum.Basic.gaussianSum (blocks.map Prod.fst) := by
  induction blocks with
  | nil => change (0 : Gaussian) - 0 = 0; ring1
  | cons block blocks ih =>
      simp only [List.map_cons, List.flatten_cons, Norm.Sum.Basic.gaussianSum, sum_append]
      rw [show block.1 + Norm.Sum.Basic.gaussianSum block.2 + Norm.Sum.Basic.gaussianSum
        (blocks.map (fun
        block => block.1 :: block.2)).flatten -
        (Norm.Sum.Basic.gaussianSum block.2 + Norm.Sum.Basic.gaussianSum (blocks.map
          Prod.snd).flatten) =
        block.1 + (Norm.Sum.Basic.gaussianSum (blocks.map (fun block => block.1 :: block.2)).flatten -
          Norm.Sum.Basic.gaussianSum (blocks.map Prod.snd).flatten) by ring1, ih]

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
/-- The squared norm of the joined-block total change is bounded by count squared times the uniform connector error. -/
theorem joined_blocks_total_bound (blocks : List (Gaussian × List Gaussian)) {error :
  Coordinate}
    (small : ∀ block ∈ blocks, Norm.Basic.normSq block.1 ≤ error) :
    Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum (blocks.map (fun block => block.1 ::
      block.2)).flatten -
      Norm.Sum.Basic.gaussianSum (blocks.map Prod.snd).flatten) ≤ (blocks.length :
        Coordinate) ^ 2 *
        error := by
  rw [connector_sum]
  have estimate := Norm.Sum.Bounds.normSq_sum_le (blocks.map Prod.fst) error (by
    intro value member
    obtain ⟨block, member, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact small block member)
  rw [Map.length_map] at estimate
  exact estimate.trans_eq (by ring1)

section
open Purelib.Integration.Path
/-- Expand the joined-block area estimate into its squared-count and fourth-power terms. -/
private theorem cost_expand (count error bound : Coordinate) :
    2 * (count ^ 2 * (4 * error * bound) + 16 * count ^ 4 * error * (2 * (error + bound))) =
      8 * count ^ 2 * error * bound + 64 * count ^ 4 * error * (bound + error) := by ring1

/-- Factor the common enlarged bound from the two count-dependent cost terms. -/
private theorem cost_factor (count error bound : Coordinate) :
    512 * count ^ 2 * error * (bound + 3 * error) + 512 * count ^ 4 * error * (bound + 3 * error) =
      512 * (count ^ 2 + count ^ 4) * error * (bound + 3 * error) := by ring1

/-- The rational cost coefficient 512 is nonnegative. -/
private theorem cost_coefficient_nonnegative : (0 : Coordinate) ≤ 512 := by decide +kernel
/-- The rational first-term coefficient eight is bounded by 512. -/
private theorem cost_first_coefficient : (8 : Coordinate) ≤ 512 := by decide +kernel
/-- The rational last-term coefficient 64 is bounded by 512. -/
private theorem cost_last_coefficient : (64 : Coordinate) ≤ 512 := by decide +kernel

end

open Purelib.Data.Rat
open Purelib.Integration.Path
/-- Increase a product's coefficient and final bound while preserving its nonnegative power and error factors. -/
private theorem cost_term {coefficient limit power error value enlarged : Coordinate}
    (coefficientLe : coefficient ≤ limit) (limitNonnegative : 0 ≤ limit) (powerNonnegative : 0 ≤ power)
    (errorNonnegative : 0 ≤ error) (valueNonnegative : 0 ≤ value) (valueLe : value ≤ enlarged) :
    coefficient * power * error * value ≤ limit * power * error * enlarged :=
  Arithmetic.mul_le_mul_direct
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe powerNonnegative) errorNonnegative)
    valueLe valueNonnegative
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct limitNonnegative powerNonnegative) errorNonnegative)

/-- A nonnegative error is bounded by three times itself. -/
private theorem error_triple {error : Coordinate} (nonnegative : 0 ≤ error) : error ≤ 3 * error :=
  (le_add_of_nonneg_right (Arithmetic.mul_nonneg_direct (by decide : (0 : Coordinate) ≤ 2)
    nonnegative)).trans_eq (by ring1)

/-- The joined-block area estimate fits the common 512-weighted count cost.

The original count, error and magnitude bound are nonnegative; the enlarged magnitude term is the bound plus three times
the error. -/
theorem joined_blocks_cost (count error bound : Coordinate) (countNonnegative : 0 ≤ count)
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound) :
    2 * (count ^ 2 * (4 * error * bound) + 16 * count ^ 4 * error * (2 * (error + bound))) ≤
      512 * (count ^ 2 + count ^ 4) * error * (bound + 3 * error) := by
  have first := cost_term cost_first_coefficient
    cost_coefficient_nonnegative
    (Arithmetic.sq_nonneg_direct count) errorNonnegative boundNonnegative
    (le_add_of_nonneg_right (Arithmetic.mul_nonneg_direct (by
        decide : (0 : Coordinate) ≤ 3) errorNonnegative))
  have last := cost_term cost_last_coefficient
    cost_coefficient_nonnegative
    (Arithmetic.pow_nonneg_direct countNonnegative 4) errorNonnegative
    (add_nonneg boundNonnegative errorNonnegative) (add_le_add (le_refl bound) (error_triple
      errorNonnegative))
  exact (cost_expand count error bound).trans_le ((add_le_add first last).trans_eq
    (cost_factor count error bound))

end Purelib.Integration.Path.IncrementAreaJoins
