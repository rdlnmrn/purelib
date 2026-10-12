module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite area comparison of paired increment paths

The difference of the two cumulative path areas is a sum of paired cross
terms. A small error in each paired increment pays both suffix sums and both
factors of the outer count. This retains the full polygon of block totals.
-/

namespace Purelib.Integration.Path.IncrementAreaComparison
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Integration.Path.IncrementArea

open Purelib.Data.Gaussian.Basic.Canonical

/-- The sum of retained paired differences equals the difference of the two original ordered sums. -/
private theorem sum_differences (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => pair.1 - pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : IncrementArea.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih => simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- Read each pair's area difference against its retained original left and right tail sums. -/
private def pairedTerms : List (IncrementArea.Gaussian × IncrementArea.Gaussian) → List IncrementArea.Gaussian
  | [] => []
  | pair :: remaining =>
      (BoundaryRibbon.area pair.1 (Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map Prod.fst)) -
        BoundaryRibbon.area pair.2 (Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map Prod.snd))) ::
          Purelib.Integration.Path.IncrementAreaComparison.pairedTerms remaining

/-- The retained paired-area term list has exactly the original pair count. -/
private theorem pairedTerms_length (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
  (IncrementAreaComparison.pairedTerms pairs).length = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Summing the paired-area terms gives the exact difference of the two original path areas. -/
private theorem pairedTerms_sum (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (IncrementAreaComparison.pairedTerms pairs) = IncrementArea.pathArea
      (pairs.map
      Prod.fst) - IncrementArea.pathArea (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : IncrementArea.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      simp only [IncrementAreaComparison.pairedTerms, Data.Gaussian.Norm.Sum.Basic.gaussianSum, List.map_cons,
        IncrementArea.pathArea_cons, ih]
      ring1

/-- Split an area difference into the first-entry difference contribution and the second-entry difference contribution.
-/
private theorem area_difference_pair (first second third fourth : IncrementArea.Gaussian) :
    BoundaryRibbon.area first third - BoundaryRibbon.area second fourth = BoundaryRibbon.area (first - second) third +
      BoundaryRibbon.area second (third - fourth) := by
  apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re, Basic.sub_im,
    Basic.add_re,
    Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Retained squared-norm bounds control the squared area norm by four times their product. -/
private theorem area_bound_of_bounds {first last : IncrementArea.Gaussian} {firstBound lastBound :
  IncrementArea.Coordinate}
    (firstLe : Data.Gaussian.Norm.Basic.normSq first ≤ firstBound) (lastLe : Data.Gaussian.Norm.Basic.normSq last ≤
      lastBound)
      (firstNonnegative : 0 ≤ firstBound) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area first last) ≤ 4 * firstBound * lastBound := by
  calc
    _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last := BoundaryRibbon.area_bound _
      _
    _ = 4 * (Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last) := by ring1
    _ ≤ 4 * (firstBound * lastBound) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_direct firstLe lastLe (Norm.Basic.normSq_nonneg _) firstNonnegative) (by
        decide)
    _ = _ := by ring1

/-- A retained uniform pointwise bound and length capacity control the squared norm of the original mapped sum.

Every displayed mapped entry retains an original pair membership witness. The unchanged finite map length transports the
supplied count capacity to the original norm-sum estimate. -/
private theorem sum_map_bound {pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)} (value :
  IncrementArea.Gaussian × IncrementArea.Gaussian → IncrementArea.Gaussian)
    {bound : IncrementArea.Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq
      (value pair) ≤ bound)
    {count : Nat} (countLe : pairs.length ≤ count) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map value)) ≤ (count :
      IncrementArea.Coordinate)
      ^ 2 * bound :=
  IncrementArea.sum_bound_of_length nonnegative (by
    intro point member
    obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact bounded pair inPairs) (by simpa only [Map.length_map] using countLe)

/-- Each retained paired-area term meets the explicit count-squared, error and magnitude bound. -/
private theorem pairedTerms_bounded {pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)} {error bound :
  IncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ error)
    (leftBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq pair.1 ≤ bound) (rightBound : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq pair.2 ≤ bound)
    {count : Nat} (countLe : pairs.length ≤ count) :
    ∀ value ∈ IncrementAreaComparison.pairedTerms pairs, Data.Gaussian.Norm.Basic.normSq value ≤ 16 * (count :
      IncrementArea.Coordinate) ^ 2 * error * bound := by
  induction pairs with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons pair remaining ih =>
      have tailCount : remaining.length ≤ count := (Nat.le_succ _).trans countLe
      have tailErrors := fun other member => errors other (List.mem_cons_of_mem pair member)
      have tailLeft := fun other member => leftBound other (List.mem_cons_of_mem pair member)
      have tailRight := fun other member => rightBound other (List.mem_cons_of_mem pair member)
      intro value member
      rcases Membership.mem_cons.mp member with same | member
      · subst value
        have first := IncrementAreaComparison.area_bound_of_bounds (errors pair (List.mem_cons_self ..))
          (IncrementAreaComparison.sum_map_bound Prod.fst boundNonnegative tailLeft tailCount) errorNonnegative
        have last := IncrementAreaComparison.area_bound_of_bounds (rightBound pair (List.mem_cons_self ..))
          (IncrementAreaComparison.sum_map_bound (fun pair => pair.1 - pair.2) errorNonnegative tailErrors tailCount)
            boundNonnegative
        rw [IncrementAreaComparison.sum_differences] at last
        rw [IncrementAreaComparison.area_difference_pair]
        exact (Norm.Bounds.normSq_add_le_two _ _).trans
          ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first last) (by decide)).trans_eq (by
            ring1))
      · exact ih tailErrors tailLeft tailRight tailCount value member

/-- The original paired path-area difference is bounded by sixteen times count to the fourth power times error and
magnitude bound.

The two original ordered increment lists remain paired, with separate magnitude certificates and a pointwise
squared-difference bound. -/
theorem pathArea_difference_bound (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) {error bound :
  IncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ error)
    (leftBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq pair.1 ≤ bound) (rightBound : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq pair.2 ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (pairs.map Prod.fst) - IncrementArea.pathArea (pairs.map
      Prod.snd)) ≤
      16 * (pairs.length : IncrementArea.Coordinate) ^ 4 * error * bound := by
  rw [← IncrementAreaComparison.pairedTerms_sum]
  have estimate := Norm.Sum.Bounds.normSq_sum_le (IncrementAreaComparison.pairedTerms pairs) _
    (IncrementAreaComparison.pairedTerms_bounded errorNonnegative boundNonnegative errors leftBound rightBound (count :=
      pairs.length) le_rfl)
  rw [IncrementAreaComparison.pairedTerms_length] at estimate
  exact estimate.trans_eq (by ring1)

/-- Bound the area difference of the two original flattened block paths using separate block-area and block-total
errors.

The retained ordered block pairs contribute a squared-count area term and a fourth-power total-interaction term with the
exact original factors. -/
theorem blocks_area_difference_bound (pairs : List (List IncrementArea.Gaussian × List IncrementArea.Gaussian))
    {areaError totalError bound : IncrementArea.Coordinate} (totalNonnegative : 0 ≤ totalError) (boundNonnegative : 0 ≤
      bound)
    (areas : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea
      pair.2)
      ≤ areaError)
    (totals : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ totalError)
    (leftBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤
      bound)
    (rightBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤
      bound) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (pairs.map Prod.fst).flatten - IncrementArea.pathArea
      (pairs.map
      Prod.snd).flatten) ≤
      2 * ((pairs.length : IncrementArea.Coordinate) ^ 2 * areaError + 16 * (pairs.length : IncrementArea.Coordinate) ^
        4 * totalError * bound) := by
  have areaDifference := IncrementAreaComparison.sum_differences (pairs.map (fun pair => (IncrementArea.pathArea pair.1,
    IncrementArea.pathArea pair.2)))
  simp only [Map.map_map, Function.comp_def] at areaDifference
  have areaBound := Norm.Sum.Bounds.normSq_sum_le (pairs.map (fun pair => IncrementArea.pathArea pair.1 -
    IncrementArea.pathArea pair.2)) areaError (by
    intro value member
    obtain ⟨pair, inPairs, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact areas pair inPairs)
  rw [Map.length_map, areaDifference] at areaBound
  have coarse := IncrementAreaComparison.pathArea_difference_bound (pairs.map (fun pair =>
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1, Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)))
    totalNonnegative boundNonnegative
    (by
      intro pair member
      obtain ⟨original, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]; exact totals original inPairs)
    (by
      intro pair member
      obtain ⟨original, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]; exact leftBound original inPairs)
    (by
      intro pair member
      obtain ⟨original, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]; exact rightBound original inPairs)
  simp only [Map.map_map, Function.comp_def, Map.length_map] at coarse
  rw [IncrementArea.pathArea_flatten, IncrementArea.pathArea_flatten]
  simp only [Map.map_map, Function.comp_def]
  rw [show Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => IncrementArea.pathArea pair.1)) +
    IncrementArea.pathArea (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1)) -
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => IncrementArea.pathArea pair.2)) +
        IncrementArea.pathArea
        (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) =
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => IncrementArea.pathArea pair.1)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => IncrementArea.pathArea pair.2))) +
        (IncrementArea.pathArea (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1)) -
          IncrementArea.pathArea (pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) by ring1]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add areaBound coarse) (by decide)).trans_eq (by
      ring1))

end Purelib.Integration.Path.IncrementAreaComparison

end
