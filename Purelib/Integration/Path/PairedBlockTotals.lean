module
import Purelib.Data.List.Map

import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Basic

public section

/-! Endpoint error of a concatenation, retaining every block's endpoint error. -/
namespace Purelib.Integration.Path.PairedBlockTotals

open Purelib.Data.List

open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Pointwise errors between retained block totals bound the difference of their two flattened totals.

The original ordered block pairs remain fixed, and the two-coordinate bound is count squared times the common
nonnegative block error. -/
theorem blocks_total_difference_bound
    (pairs : List (List Stokes.PrimitivePoint × List Stokes.PrimitivePoint))
    {error : PairedIncrementArea.Coordinate} (nonnegative : 0 ≤ error)
    (errors : ∀ pair ∈ pairs,
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total pair.1)
        (PairedIncrementArea.total pair.2)) error) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total (pairs.map
      Prod.fst).flatten)
      (PairedIncrementArea.total (pairs.map Prod.snd).flatten))
        ((pairs.length : PairedIncrementArea.Coordinate)^2 * error) := by
  have bounded := PairedIncrementArea.total_bound nonnegative (values :=
    pairs.map (fun pair => Stokes.PrimitivePoint.sub (PairedIncrementArea.total pair.1) (PairedIncrementArea.total
      pair.2))) (by
      intro point member
      obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
      exact errors pair present) (count := pairs.length) (by
        rw [Map.length_map])
  have difference := PairedIncrementComparison.total_differences
    (pairs.map (fun pair => (PairedIncrementArea.total pair.1, PairedIncrementArea.total pair.2)))
  simp only [Map.map_map] at difference
  dsimp only [Function.comp_def] at difference
  rw [difference] at bounded
  simp only [PairedAreaBlocks.total_flatten, Map.map_map] at bounded ⊢
  dsimp only [Function.comp_def] at bounded ⊢
  exact bounded

end Purelib.Integration.Path.PairedBlockTotals
