module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Full paired block comparison retains the polygon of block totals. -/
namespace Purelib.Integration.Path.PairedBlockComparison

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare the two original flattened paired-block areas using separate block-area and block-total errors.

The exact ordered block pairs retain both total magnitude bounds. The estimate keeps its distinct squared-count
internal-area and fourth-power total-interaction contributions. -/
theorem blocks_area_difference_bound (pairs : List (List Stokes.PrimitivePoint × List Stokes.PrimitivePoint))
    {areaError totalError bound : PairedIncrementArea.Coordinate} (totalNonnegative : 0 ≤ totalError) (boundNonnegative
      : 0 ≤ bound)
    (areas : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 - PairedIncrementArea.area
      pair.2) ≤ areaError)
    (totals : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub
      (PairedIncrementArea.total pair.1) (PairedIncrementArea.total pair.2)) totalError)
    (leftBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total pair.1) bound)
    (rightBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total pair.2) bound) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (pairs.map Prod.fst).flatten - PairedIncrementArea.area
      (pairs.map Prod.snd).flatten) ≤
      2 * ((pairs.length : PairedIncrementArea.Coordinate)^2 * areaError + 16 * (pairs.length :
        PairedIncrementArea.Coordinate)^4 * totalError * bound) := by
  have difference : Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => PairedIncrementArea.area pair.1 -
    PairedIncrementArea.area pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => PairedIncrementArea.area pair.1)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => PairedIncrementArea.area pair.2)) := by
    clear areas totals leftBound rightBound
    induction pairs with
    | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
    | cons pair tail ih =>
        change (_ - _) + _ = (_ + _) - (_ + _)
        rw [ih]
        ring1
  have areaBound := Norm.Sum.Bounds.normSq_sum_le (pairs.map (fun pair => PairedIncrementArea.area pair.1 -
    PairedIncrementArea.area pair.2)) areaError (by
    intro value member
    obtain ⟨pair, inPairs, rfl⟩ := Map.mem_map.mp member
    exact areas pair inPairs)
  rw [Map.length_map, difference] at areaBound
  have coarse := PairedIncrementComparison.area_difference_bound (pairs.map (fun pair => (PairedIncrementArea.total
    pair.1, PairedIncrementArea.total pair.2)))
    totalNonnegative boundNonnegative
    (by
      intro pair member
      obtain ⟨original, inPairs, rfl⟩ := Map.mem_map.mp member
      exact totals original inPairs)
    (by
      intro pair member
      obtain ⟨original, inPairs, rfl⟩ := Map.mem_map.mp member
      exact leftBound original inPairs)
    (by
      intro pair member
      obtain ⟨original, inPairs, rfl⟩ := Map.mem_map.mp member
      exact rightBound original inPairs)
  simp only [Map.map_map, Map.length_map] at coarse
  dsimp only [Function.comp_def] at coarse
  rw [PairedAreaBlocks.area_flatten, PairedAreaBlocks.area_flatten]
  simp only [Map.map_map]
  dsimp only [Function.comp_def]
  have rearrange (a b c d : Basic.Canonical) : (a + b) - (c + d) = (a - c) + (b - d) := by ring1
  rw [rearrange]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add areaBound coarse) (by decide)).trans_eq (by
      ring1))

end Purelib.Integration.Path.PairedBlockComparison
