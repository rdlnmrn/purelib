module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedBlockComparison
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

public section

/-! Compare complete physical paths with scalar source paths, including joins. -/
namespace Purelib.Integration.Path.ConjugateBlockComparison

open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal conjugateDiagonal_area)

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The total of conjugate-diagonal increments is the embedding of the exact original Gaussian sum. -/
theorem conjugateDiagonal_total (values : List Basic.Canonical) :
    PairedIncrementArea.total (values.map ConjugatePathReadback.conjugateDiagonal) =
      ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    change (ConjugatePathReadback.conjugateDiagonal value).add (PairedIncrementArea.total (rest.map
      ConjugatePathReadback.conjugateDiagonal)) =
      ConjugatePathReadback.conjugateDiagonal (value + Data.Gaussian.Norm.Sum.Basic.gaussianSum rest)
    rw [ih]
    exact congrArg₂ Stokes.PrimitivePoint.mk (Basic.conj_add _ _).symm rfl

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare retained paired blocks with Gaussian blocks through their exact conjugate-diagonal readbacks.

The original block pairs, area errors, total errors and both magnitude certificates remain separate; the same
squared-count and fourth-power interaction costs are retained. -/
theorem conjugate_blocks_area_difference_bound
    (pairs : List (List Stokes.PrimitivePoint × List Basic.Canonical))
    {areaError totalError bound : PairedIncrementArea.Coordinate}
    (totalNN : 0 ≤ totalError) (boundNN : 0 ≤ bound)
    (areas : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 - IncrementArea.pathArea pair.2) ≤ areaError)
    (errors : ∀ pair ∈ pairs,
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total pair.1)
        (ConjugatePathReadback.conjugateDiagonal (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) totalError)
    (leftBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total pair.1) bound)
    (rightBound : ∀ pair ∈ pairs, PrimitiveAreaBounds.PrimitivePoint.Bounded (ConjugatePathReadback.conjugateDiagonal
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) bound) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (pairs.map Prod.fst).flatten -
      IncrementArea.pathArea (pairs.map Prod.snd).flatten) ≤
      2 * ((pairs.length : PairedIncrementArea.Coordinate)^2 * areaError +
        16 * (pairs.length : PairedIncrementArea.Coordinate)^4 * totalError * bound) := by
  have estimate := PairedBlockComparison.blocks_area_difference_bound
    (pairs.map (fun pair => (pair.1, pair.2.map ConjugatePathReadback.conjugateDiagonal))) totalNN boundNN
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      rw [ConjugatePathReadback.conjugateDiagonal_area]
      exact areas original present)
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      rw [ConjugateBlockComparison.conjugateDiagonal_total]
      exact errors original present)
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      exact leftBound original present)
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      rw [ConjugateBlockComparison.conjugateDiagonal_total]
      exact rightBound original present)
  simp only [-eq_self, -iff_self, Purelib.Data.List.Map.map_map, Function.comp_def,
    Purelib.Data.List.Map.length_map] at estimate
  have sourceRead : (pairs.map (fun pair => pair.2.map ConjugatePathReadback.conjugateDiagonal)).flatten =
      ((pairs.map Prod.snd).flatten).map conjugateDiagonal := by
    clear areas errors leftBound rightBound estimate
    induction pairs with
    | nil => rfl
    | cons pair rest ih =>
      simp only [-eq_self, -iff_self, List.map_cons, List.flatten_cons, Purelib.Data.List.Map.map_append]
      exact congrArg (fun tail => pair.2.map ConjugatePathReadback.conjugateDiagonal ++ tail) ih
  rw [sourceRead, ConjugatePathReadback.conjugateDiagonal_area] at estimate
  exact estimate

end Purelib.Integration.Path.ConjugateBlockComparison
