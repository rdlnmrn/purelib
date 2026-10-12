module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic

public import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

public section

/-!
# Subdivision-independent area estimates for finite path models

The increments are the actual cell integral samples. The two dyadic estimates
pay a uniform subdivision within each parent, followed by a uniform bank of
parents with possibly different child depths. No total-integral cancellation
is used to discard a block's internal area.
-/

namespace Purelib.Riemann.Paths.PathArea

open Purelib.Data.List

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)

section
open Purelib.Data
/-- The Gaussian rational type of actual path increments and area readbacks. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational scalar type of path area bounds. -/
abbrev Coordinate := Rat.Fraction.Rational

end

open Purelib.Integration in
/-- Read the ordered list of integral samples from the retained path cells. -/
@[expose] def increments (path : Polynomial.Gaussian.Path.Basic.PathModel) : List Gaussian := path.cells.map
  (·.integralSample)

open Purelib.Integration in
open Purelib.Data in
/-- The sum of the actual cell increments is the path's integral sample. -/
theorem increments_sum (path : Polynomial.Gaussian.Path.Basic.PathModel) : Data.Gaussian.Norm.Sum.Basic.gaussianSum
  (increments path) = path.integralSample := by
  cases path with
  | mk cells =>
      induction cells with
      | nil => rfl
      | cons cell cells ih => exact congrArg (cell.integralSample + ·) ih

section
open Purelib.Integration
/-- Concatenating path models concatenates their actual increment lists.

Each original cell keeps its integral sample, and concatenation preserves the order of both retained cell lists. -/
theorem increments_append (first last : Polynomial.Gaussian.Path.Basic.PathModel) :
    increments (first.concat last) = increments first ++ increments last := Map.map_append _ _ _

/-- Cache the total and full primitive area of the actual path-cell increments. -/
@[expose] def sample (path : Polynomial.Gaussian.Path.Basic.PathModel) : Path.IncrementArea.Summary (increments path) :=
  Path.IncrementArea.Summary.build (increments path)

/-- The cached increment total equals the path's retained integral sample. -/
theorem sample_total (path : Polynomial.Gaussian.Path.Basic.PathModel) : (sample path).total = path.integralSample :=
  (sample path).total_eq.trans (increments_sum path)

end

open Purelib.Approximation in
/-- The squared dyadic count cancels the matching quarter-radius factor. -/
private theorem dyadic_weight_cancel (density movement : Coordinate) (depth : Nat) :
    (((2 ^ depth : Nat) : Coordinate) ^ 2 * (density * Rational.Geometric.Basic.quarterRadius movement depth)) = density
      * movement := by
  calc
    _ = density * (((2 ^ depth : Nat) : Coordinate) *
        (((2 ^ depth : Nat) : Coordinate) * Rational.Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = _ := by rw [Rational.Geometric.DyadicCount.dyadic_count_cancel]

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- A dyadic family of uniformly bounded increments has a subdivision-independent area bound.

There are exactly two to the depth increments, each with quadrance at most density times the matching quarter-radius
movement bound. -/
theorem dyadic_area_bound (values : List Gaussian) (depth : Nat) (count : values.length = 2 ^ depth)
    {density movement : Coordinate} (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤ movement)
    (bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ density *
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea values) ≤ 4 * (density * movement) ^ 2 := by
  have boundNonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
    (Rational.Geometric.Basic.quarterRadius_nonneg movementNonnegative depth)
  have estimate := Path.IncrementArea.pathArea_bound values boundNonnegative bounded
  rw [count] at estimate
  rw [dyadic_weight_cancel] at estimate
  exact estimate

open Purelib.Integration in
open Purelib.Data in
/-- Bound a flattened path's area by its retained internal block areas and coarse polygon area.

Every block satisfies the same area bound and its total has quadrance at most the nonnegative total bound; the estimate
retains the number of original blocks. -/
theorem blocks_area_bound (blocks : List (List Gaussian)) {areaBound totalBound : Coordinate}
    (totalNonnegative : 0 ≤ totalBound)
    (areas : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea block) ≤ areaBound)
    (totals : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum block) ≤
      totalBound) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea blocks.flatten) ≤ 2 *
      ((blocks.length : Coordinate) ^ 2 * areaBound + 4 * ((blocks.length : Coordinate) ^ 2 * totalBound) ^ 2) := by
  rw [Path.IncrementArea.pathArea_flatten]
  have internal := Gaussian.Norm.Sum.Bounds.normSq_sum_le (blocks.map Path.IncrementArea.pathArea) areaBound (by
    intro value member
    obtain ⟨block, inBlocks, rfl⟩ := List.Map.mem_map.mp member
    exact areas block inBlocks)
  have coarse := Path.IncrementArea.pathArea_bound (blocks.map Data.Gaussian.Norm.Sum.Basic.gaussianSum)
    totalNonnegative (by
    intro value member
    obtain ⟨block, inBlocks, rfl⟩ := List.Map.mem_map.mp member
    exact totals block inBlocks)
  rw [Map.length_map] at internal coarse
  have sum := add_le_add internal coarse
  calc
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map
      Path.IncrementArea.pathArea)) + Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (blocks.map
      Data.Gaussian.Norm.Sum.Basic.gaussianSum))) :=
      Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((blocks.length : Coordinate) * ((blocks.length : Coordinate) * areaBound) +
        4 * ((blocks.length : Coordinate) ^ 2 * totalBound) ^ 2) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide)
    _ = _ := by ring1

open Purelib.Approximation in
open Purelib.Data in
/-- The dyadic count-weighted internal area estimate is bounded by four times squared density-movement product. -/
private theorem dyadic_internal_area_bound {density movement : Coordinate}
    (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤ movement) (depth : Nat) :
    (((2 ^ depth : Nat) : Coordinate) ^ 2 * (4 * (density * Rational.Geometric.Basic.quarterRadius movement depth) ^ 2))
      ≤
      4 * (density * movement) ^ 2 := by
  have boundLe : density * Rational.Geometric.Basic.quarterRadius movement depth ≤ density * movement :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rational.Geometric.Basic.quarterRadius_le_scale movementNonnegative depth) densityNonnegative
  have product : (density * movement) * (density * Rational.Geometric.Basic.quarterRadius movement depth) ≤ (density *
    movement) * (density * movement) :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct boundLe
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative movementNonnegative)
  calc
    _ = 4 * ((((2 ^ depth : Nat) : Coordinate) ^ 2 * (density * Rational.Geometric.Basic.quarterRadius movement depth))
      *
        (density * Rational.Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = 4 * ((density * movement) * (density * Rational.Geometric.Basic.quarterRadius movement depth)) := by
      rw [dyadic_weight_cancel]
    _ ≤ 4 * ((density * movement) * (density * movement)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)
    _ = _ := by ring1

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- A dyadic bank of path blocks has area quadrance at most sixteen times squared density-movement product.

Each block retains its internal area and total-increment estimates at the common parent depth, independently of its own
finer subdivision. -/
theorem dyadic_blocks_area_bound (blocks : List (List Gaussian)) (depth : Nat) (count : blocks.length = 2 ^ depth)
    {density movement : Coordinate} (densityNonnegative : 0 ≤ density) (movementNonnegative : 0 ≤ movement)
    (areas : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea block) ≤ 4 * (density *
      Rational.Geometric.Basic.quarterRadius movement depth) ^ 2)
    (totals : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum block) ≤
      density * Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea blocks.flatten) ≤ 16 * (density * movement) ^ 2 :=
      by
  have nonnegative : 0 ≤ density * Rational.Geometric.Basic.quarterRadius movement depth :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
    (Rational.Geometric.Basic.quarterRadius_nonneg movementNonnegative depth)
  have estimate := blocks_area_bound blocks nonnegative areas totals
  rw [count, dyadic_weight_cancel density movement depth] at estimate
  have internal := dyadic_internal_area_bound densityNonnegative movementNonnegative depth
  have sum : (((2 ^ depth : Nat) : Coordinate) ^ 2 * (4 * (density * Rational.Geometric.Basic.quarterRadius movement
    depth) ^ 2)) +
      4 * (density * movement) ^ 2 ≤ 4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2 :=
    add_le_add internal (le_refl (4 * (density * movement) ^ 2))
  have scaled : 2 * ((((2 ^ depth : Nat) : Coordinate) ^ 2 * (4 * (density * Rational.Geometric.Basic.quarterRadius
    movement depth) ^ 2)) +
      4 * (density * movement) ^ 2) ≤ 2 * (4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2) :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide)
  have result : 2 * (4 * (density * movement) ^ 2 + 4 * (density * movement) ^ 2) = 16 * (density * movement) ^ 2 := by
    ring1
  exact estimate.trans (scaled.trans_eq result)

end Purelib.Riemann.Paths.PathArea
