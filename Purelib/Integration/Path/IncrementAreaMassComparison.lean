module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# Area comparison using the actual squared-increment sums

Nonuniform period refinements retain a bounded count-weighted movement sum.
Summing the individual error charges before estimating the polygon preserves
that bound; replacing them by their maximum would lose two powers of count.
-/

namespace Purelib.Integration.Path.IncrementAreaMassComparison

open Purelib.Data.List

open Purelib.Integration.Path.IncrementArea

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat.Fraction.Compatibility

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- The sum of squared Gaussian norms over the original list is nonnegative. -/
private theorem normSum_nonnegative : ∀ values : List IncrementArea.Gaussian, 0 ≤ Norm.Sum.Basic.gaussianNormSqSum
  values
  | [] => le_rfl
  | value :: values => add_nonneg (Basic.Canonical.normSq_nonneg value)
    (normSum_nonnegative values)

/-- Summing the original pairwise differences equals the difference of the two projected sums. -/
private theorem sum_differences (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => pair.1 - pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : IncrementArea.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      change pair.1 - pair.2 + Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map (fun pair => pair.1 - pair.2)) = _
      rw [ih]
      change _ = (pair.1 + Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.fst)) - (pair.2 +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (pairs.map Prod.snd))
      ring1

/-- List the signed cross-area differences for each original paired head and its original paired tail totals. -/
private def terms : List (IncrementArea.Gaussian × IncrementArea.Gaussian) → List IncrementArea.Gaussian
  | [] => []
  | pair :: remaining =>
      (BoundaryRibbon.area pair.1 (Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map Prod.fst)) -
        BoundaryRibbon.area pair.2 (Data.Gaussian.Norm.Sum.Basic.gaussianSum (remaining.map Prod.snd))) ::
          terms remaining

end

open Purelib.Integration.Path in
/-- There is one retained area-difference term per original input pair. -/
private theorem terms_length (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
  (terms pairs).length = pairs.length := by
  induction pairs with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The retained term sum equals the signed area difference of the two original projected paths. -/
private theorem terms_sum (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms pairs) = IncrementArea.pathArea
      (pairs.map
      Prod.fst) - IncrementArea.pathArea (pairs.map Prod.snd) := by
  induction pairs with
  | nil => change (0 : IncrementArea.Gaussian) = 0 - 0; ring1
  | cons pair pairs ih =>
      change _ + Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms pairs) = _
      rw [ih]
      simp only [List.map_cons, IncrementArea.pathArea_cons]
      ring1

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
/-- An original list's count and squared-norm mass bounds control the squared norm of its total. -/
private theorem sum_bound {values : List IncrementArea.Gaussian} {count : Nat} {bound : IncrementArea.Coordinate}
    (countLe : values.length ≤ count) (massLe : Norm.Sum.Basic.gaussianNormSqSum values ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum values) ≤ (count :
      IncrementArea.Coordinate) * bound :=
      by
  rw [Norm.Basic.normSq_eq_canonical]
  exact (Norm.Sum.Basic.normSq_gaussianSum_le values).trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct (Fraction.Cast.Order.natCast_le_direct countLe) massLe
      (normSum_nonnegative values) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
        count)))

/-- Bound the difference of two cross areas using original coordinate errors and retained magnitude bounds.

The separate displacement-error and opposite-coordinate magnitude contributions remain explicit in the eightfold
estimate. -/
private theorem area_pair_bound (first second third fourth : IncrementArea.Gaussian) {leftError rightError :
  IncrementArea.Coordinate}
    (thirdBound : Data.Gaussian.Norm.Basic.normSq third ≤ leftError) (differenceBound : Data.Gaussian.Norm.Basic.normSq
      (third -
      fourth) ≤ rightError) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area first third - BoundaryRibbon.area second fourth) ≤
      8 * (Data.Gaussian.Norm.Basic.normSq (first - second) * leftError + Data.Gaussian.Norm.Basic.normSq second *
        rightError) :=
        by
  have equality : BoundaryRibbon.area first third - BoundaryRibbon.area second fourth =
      BoundaryRibbon.area (first - second) third + BoundaryRibbon.area second (third - fourth) := by
    apply Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re, Basic.sub_im,
      Basic.add_re,
      Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  rw [equality]
  have firstLe := (BoundaryRibbon.area_bound (first - second) third).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct thirdBound (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide) (Norm.Basic.normSq_nonneg _)))
  have secondLe := (BoundaryRibbon.area_bound second (third - fourth)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct differenceBound
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg _)))
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct firstLe
      secondLe) (by decide)).trans_eq (by ring1))

/-- Control the total squared-norm mass of retained cross-area difference terms from the original paired masses.

The estimate retains original pair count, pairwise error mass and the separate left and right projected masses. -/
private theorem terms_mass (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) {count : Nat} {error left :
  IncrementArea.Coordinate}
    (countLe : pairs.length ≤ count)
    (errors : Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 - pair.2)) ≤ error)
    (leftBound : Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) ≤ left) :
    Norm.Sum.Basic.gaussianNormSqSum (terms pairs) ≤ 8 * (count : IncrementArea.Coordinate)
      *
      (Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 - pair.2)) * left +
        Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd) * error) := by
  induction pairs with
  | nil =>
      change (0 : IncrementArea.Coordinate) ≤ 8 * _ * (0 * _ + 0 * _)
      rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct, _root_.zero_add,
        Fraction.Field.mul_zero_direct]
  | cons pair pairs ih =>
      have tailCount : pairs.length ≤ count := (Nat.le_succ _).trans countLe
      have tailErrors : Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 - pair.2)) ≤ error :=
        (le_add_of_nonneg_left (Basic.Canonical.normSq_nonneg (pair.1 - pair.2))).trans errors
      have tailLeft : Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) ≤ left :=
        (le_add_of_nonneg_left (Basic.Canonical.normSq_nonneg pair.1)).trans leftBound
      have leftSum := sum_bound (count := count) (by rw [Map.length_map]; exact tailCount)
        tailLeft
      have errorSum := sum_bound (count := count) (by rw [Map.length_map]; exact tailCount)
        tailErrors
      rw [sum_differences] at errorSum
      have head := area_pair_bound pair.1 pair.2 _ _ leftSum errorSum
      rw [Norm.Basic.normSq_eq_canonical] at head
      have total := Fraction.Order.Arithmetic.add_le_add_direct head (ih tailCount tailErrors tailLeft)
      exact total.trans_eq (by simp only [List.map_cons, Norm.Sum.Basic.gaussianNormSqSum,
        Norm.Basic.normSq_eq_canonical]; ring1)

/-- Bound the original paired paths' area difference by their count-weighted error and magnitude masses.

The eightfold product keeps the actual list length and both projected norm sums, without replacing the original pairs.
-/
theorem pathArea_difference_mass (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (pairs.map Prod.fst) - IncrementArea.pathArea (pairs.map
      Prod.snd)) ≤
      8 * ((pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 -
        pair.2))) *
        ((pairs.length : IncrementArea.Coordinate) *
          (Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) + Norm.Sum.Basic.gaussianNormSqSum (pairs.map
            Prod.snd))) := by
  rw [Norm.Basic.normSq_eq_canonical, ← terms_sum]
  have total := Norm.Sum.Basic.normSq_gaussianSum_le (terms pairs)
  rw [terms_length] at total
  exact (total.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (terms_mass
    pairs le_rfl le_rfl le_rfl)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))).trans_eq (by ring1)

/-- Count-weighted pairwise error and right-path mass bounds control the original area difference.

For nonnegative supplied bounds, the result is thirty-two times error times the sum of right mass bound and error. -/
theorem pathArea_difference_of_mass_bounds (pairs : List (IncrementArea.Gaussian × IncrementArea.Gaussian)) {error bound
  : IncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : (pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair =>
      pair.1 - pair.2)) ≤ error)
    (bounded : (pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd) ≤
      bound) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (pairs.map Prod.fst) - IncrementArea.pathArea (pairs.map
      Prod.snd)) ≤ 32 * error * (bound + error) := by
  have left : Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) ≤
      2 * (Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd) + Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair
        => pair.1 - pair.2))) := by
    clear errors bounded
    induction pairs with
    | nil => change (0 : IncrementArea.Coordinate) ≤ 2 * (0 + 0); decide
    | cons pair pairs ih =>
        have head := Norm.Bounds.normSq_add_le_two (pair.1 - pair.2) pair.2
        rw [sub_add_cancel, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
          Norm.Basic.normSq_eq_canonical] at head
        exact (Fraction.Order.Arithmetic.add_le_add_direct head ih).trans_eq (by
          simp only [List.map_cons, Norm.Sum.Basic.gaussianNormSqSum]
          ring1)
  have leftMass := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct left
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le pairs.length))
  have leftPaid : (pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) ≤ 2
    * (bound + error) :=
    leftMass.trans ((show (pairs.length : IncrementArea.Coordinate) * (2 * (_ + _)) =
      2 * ((pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd) +
        (pairs.length : IncrementArea.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 -
          pair.2))) by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct bounded
        errors) (by decide)))
  have both : (pairs.length : IncrementArea.Coordinate) *
      (Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) + Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd)) ≤
        4 * (bound + error) := by
    rw [mul_add]
    have extra : 2 * (bound + error) + bound ≤ 4 * (bound + error) := by
      have nonnegative := add_nonneg boundNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 :
        IncrementArea.Coordinate) ≤ 2) errorNonnegative)
      exact (le_add_of_nonneg_right nonnegative : 2 * (bound + error) + bound ≤ _).trans_eq (by ring1)
    exact (Fraction.Order.Arithmetic.add_le_add_direct leftPaid bounded).trans extra
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct errors both
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      (add_nonneg (normSum_nonnegative _) (normSum_nonnegative
        _))) errorNonnegative
  exact (pathArea_difference_mass pairs).trans
    ((show 8 * (_ * _) * _ = 8 * (((pairs.length : IncrementArea.Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 - pair.2))) *
      ((pairs.length : IncrementArea.Coordinate) * (Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) +
        Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.snd)))) by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)).trans_eq (by ring1)))

end Purelib.Integration.Path.IncrementAreaMassComparison
