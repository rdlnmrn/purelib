module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedBlockTotals
import Purelib.Integration.Path.ConjugateBlockComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Basic

public section

/-! Retain endpoint and magnitude bounds while assembling scalar source blocks. -/
namespace Purelib.Integration.Path.ConjugateBlockTotals

open Purelib.Data.List

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare the flattened paired total with the conjugate-diagonal embedding of the exact original Gaussian total.

Each retained block pair supplies its own original total error; the common nonnegative bound is amplified by the squared
block count. -/
theorem conjugate_blocks_total_difference_bound
    (pairs : List (List Stokes.PrimitivePoint × List Basic.Canonical))
    {error : PairedIncrementArea.Coordinate} (nonnegative : 0 ≤ error)
    (errors : ∀ pair ∈ pairs,
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total pair.1)
        (ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) error) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total (pairs.map
      Prod.fst).flatten)
      (ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd).flatten)))
        ((pairs.length : PairedIncrementArea.Coordinate)^2 * error) := by
  have bounded := PairedIncrementArea.total_bound nonnegative (values := pairs.map (fun pair =>
    Stokes.PrimitivePoint.sub (PairedIncrementArea.total pair.1) (ConjugatePathReadback.conjugateDiagonal
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)))) (by
      intro point member
      obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
      exact errors pair present) (count := pairs.length) (by rw [Map.length_map])
  have difference := PairedIncrementComparison.total_differences
    (pairs.map (fun pair => (PairedIncrementArea.total pair.1, ConjugatePathReadback.conjugateDiagonal
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))))
  simp only [Map.map_map] at difference
  dsimp only [Function.comp_def] at difference
  rw [difference] at bounded
  have source : PairedIncrementArea.total (pairs.map (fun pair => ConjugatePathReadback.conjugateDiagonal
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) =
      ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd).flatten)
        := by
    rw [IncrementArea.sum_flatten, Map.map_map]
    have equality := ConjugateBlockComparison.conjugateDiagonal_total (pairs.map (fun pair =>
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))
    simp only [Map.map_map] at equality
    dsimp only [Function.comp_def] at equality
    exact equality
  rw [source] at bounded
  simp only [PairedAreaBlocks.total_flatten, Map.map_map] at bounded ⊢
  dsimp only [Function.comp_def] at bounded ⊢
  exact bounded

open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- A common nonnegative bound on each original paired block total bounds the flattened total by count squared times
that bound. -/
theorem blocks_total_bounded (blocks : List (List Stokes.PrimitivePoint))
    {bound : PairedIncrementArea.Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ block ∈ blocks, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total block) bound) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total blocks.flatten) ((blocks.length :
      PairedIncrementArea.Coordinate)^2 * bound) := by
  rw [PairedAreaBlocks.total_flatten]
  apply PairedIncrementArea.total_bound nonnegative
  · intro point member
    obtain ⟨block, present, rfl⟩ := Map.mem_map.mp member
    exact bounded block present
  · rw [Map.length_map]

end Purelib.Integration.Path.ConjugateBlockTotals
