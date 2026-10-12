module
import Purelib.Data.List.Search
import Purelib.Data.List.Flatten
import Purelib.Data.List.Permutation
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Finite Gaussian sums and squared-norm bounds

The three retained sums use their original head-plus-tail recurrences. Coordinate
readback identifies the Gaussian sum with two rational coordinate sums. Their
finite square-sum certificates bound its squared norm by list length times the
sum of the same entries' squared norms.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Sum.Basic

-- Preserve the two established distinct public sum owner names.

open Purelib
open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List

namespace DividedDifference

/-- Compute the Gaussian list sum by adding each retained head to its recursive tail sum.

The empty list contributes zero. The finite recurrence preserves the original
entry order and the same Gaussian addition operation at every retained head. -/
@[expose] def sumGaussian : List Basic.Canonical → Basic.Canonical
  | [] => 0
  | value :: remaining => value + Purelib.Data.Gaussian.Norm.Sum.Basic.DividedDifference.sumGaussian remaining

-- Preserve this original public Gaussian sum API and its retained reduction clients.

end DividedDifference
/-- Compute the Gaussian list sum from zero using the original head-plus-tail recurrence.

The original Gaussian addition combines each displayed head with its unchanged tail sum. The empty list supplies zero,
preserving order and every repeated occurrence. -/
@[expose] def gaussianSum : List Basic.Canonical → Basic.Canonical
  | [] => 0
  | value :: values => value + gaussianSum values

-- Preserve this original public Gaussian sum API and its retained reduction clients.
/-- Concatenating two Gaussian lists adds their retained sums.

Structural induction keeps the original head-plus-tail addition recurrence
and entry order. The unchanged suffix supplies the second sum. -/
theorem gaussianSum_append (first second : List Basic.Canonical) :
    gaussianSum (first ++ second) = gaussianSum first + gaussianSum second := by
  induction first with
  | nil => change gaussianSum second = 0 + gaussianSum second; ring1
  | cons value rest ih => simp only [List.cons_append, gaussianSum, ih]; ring1

/-- Permuting retained entries preserves the Gaussian sum of their mapped values.

Structural permutation steps keep every original value and repeated occurrence.
The two displayed adjacent values commute, and composition transports the same sums. -/
theorem gaussianSum_map_perm {Item : Type} (value : Item → Gaussian.Basic.Canonical)
    {first last : List Item} (order : List.Perm first last) :
    gaussianSum (first.map value) = gaussianSum (last.map value) := by
  induction order with
  | nil => rfl
  | cons head order ih => exact congrArg (value head + ·) ih
  | swap first last tail => change value _ + (value _ + _) = value _ + (value _ + _); ring1
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

-- Preserve this original public Gaussian sum API and its retained reduction clients.
/-- An injective reindexing of two sheets preserves the sum of their Gaussian values.

Injectivity forces the two retained target indices to be the two different sheets, so reindexing preserves the ordered
pair sum up to commutation. -/
theorem sum_two_reindex (mapping : Fin 2 → Fin 2) (injective : Function.Injective mapping)
    (values : Fin 2 → Gaussian.Basic.Canonical) : values (mapping 0) + values (mapping 1) = values 0 + values 1 := by
  have different : mapping 0 ≠ mapping 1 := fun same => (by decide : (0 : Fin 2) ≠ 1) (injective same)
  have pairSum : ∀ first second : Fin 2, first ≠ second →
      values first + values second = values 0 + values 1 := by
    intro first
    refine Data.Fin.cases_induction ?_ ?_ first
    · intro second
      refine Data.Fin.cases_induction ?_ ?_ second
      · intro distinct
        exact (distinct rfl).elim
      · intro remaining
        refine Data.Fin.cases_induction ?_ ?_ remaining
        · intro _
          rfl
        · intro empty
          exact Fin.elim0 empty
    · intro remaining
      refine Data.Fin.cases_induction ?_ ?_ remaining
      · intro second
        refine Data.Fin.cases_induction ?_ ?_ second
        · intro _
          exact Gaussian.Basic.add_comm _ _
        · intro remainingSecond
          refine Data.Fin.cases_induction ?_ ?_ remainingSecond
          · intro distinct
            exact (distinct rfl).elim
          · intro empty
            exact Fin.elim0 empty
      · intro empty
        exact Fin.elim0 empty
  exact pairSum (mapping 0) (mapping 1) different

/-- Sum the squared norms of the retained Gaussian list entries.

Each displayed Gaussian contributes its exact canonical squared norm. The original rational addition retains the
head-plus-tail recurrence and zero at the empty list. -/
@[expose] def gaussianNormSqSum : List Basic.Canonical → Fraction.Rational
  | [] => 0
  | value :: values => Basic.Canonical.normSq value + Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum values

/-- Summing mapped squared Gaussian norms agrees with the retained Gaussian norm-sum fold.

The original coordinate sum and squared-norm sum traverse the same list in order.
The pointwise norm readback identifies each head, and scalar congruence preserves the tail. -/
theorem gaussianNormSqSum_eq_coordinateSum_map {Entry : Type}
    (value : Entry → Gaussian.Basic.Canonical) (entries : List Entry) :
    FiniteSum.Rational.Squares.coordinateSum
        (entries.map (fun entry => Basic.normSq (value entry))) =
      gaussianNormSqSum (entries.map value) := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      change Basic.normSq (value entry) +
        FiniteSum.Rational.Squares.coordinateSum
          (tail.map (fun entry => Basic.normSq (value entry))) =
        Gaussian.Basic.Canonical.normSq (value entry) + gaussianNormSqSum (tail.map value)
      rw [Norm.Basic.normSq_eq_canonical]
      exact congrArg (Gaussian.Basic.Canonical.normSq (value entry) + ·) ih

/-- Concatenating Gaussian lists adds their retained squared-norm sums.

Structural induction keeps each original head contribution and the same
ordered suffix. Only scalar rational addition is reassociated. -/
theorem gaussianNormSqSum_append (first last : List Basic.Canonical) :
    gaussianNormSqSum (first ++ last) = gaussianNormSqSum first + gaussianNormSqSum last := by
  induction first with
  | nil => change gaussianNormSqSum last = 0 + gaussianNormSqSum last; ring1
  | cons first rest ih =>
      change Basic.Canonical.normSq first + gaussianNormSqSum (rest ++ last) = (Basic.Canonical.normSq first +
        gaussianNormSqSum rest) + gaussianNormSqSum last
      rw [ih]
      ring1

/-- The real coordinate of the Gaussian list sum equals the rational sum of the real-coordinate list.

The same finite list supplies both recurrences. Gaussian addition projects to rational addition, retaining each head
coordinate and the unchanged mapped tail. -/
@[simp] theorem gaussianSum_re : ∀ values : List Basic.Canonical,
    (gaussianSum values).re = FiniteSum.Rational.Squares.coordinateSum (values.map (fun z => z.re))
  | [] => rfl
  | value :: values => by
      rw [gaussianSum, Basic.add_re, gaussianSum_re, List.map_cons, FiniteSum.Rational.Squares.coordinateSum]

/-- The imaginary coordinate of the Gaussian list sum equals the rational sum of the imaginary-coordinate list.

The same finite list supplies both recurrences. Each Gaussian head contributes its retained imaginary coordinate to the
corresponding rational sum. -/
@[simp] theorem gaussianSum_im : ∀ values : List Basic.Canonical,
    (gaussianSum values).im = FiniteSum.Rational.Squares.coordinateSum (values.map (fun z => z.im))
  | [] => rfl
  | value :: values => by
      rw [gaussianSum, Basic.add_im, gaussianSum_im, List.map_cons, FiniteSum.Rational.Squares.coordinateSum]

/-- The sum of Gaussian squared norms splits into the real-coordinate square sum and imaginary-coordinate square sum.

The exact squared norm of each retained Gaussian is the sum of its two coordinate squares. Structural induction keeps
both coordinate lists and their unchanged tails. -/
theorem gaussianNormSqSum_coordinates : ∀ values : List Basic.Canonical,
    gaussianNormSqSum values =
      FiniteSum.Rational.Squares.coordinateSquareSum (values.map (fun z => z.re)) +
        FiniteSum.Rational.Squares.coordinateSquareSum (values.map (fun z => z.im))
  | [] => by
      change (0 : Fraction.Rational) = 0 + 0
      ring1
  | value :: values => by
      rw [gaussianNormSqSum, gaussianNormSqSum_coordinates]
      simp only [List.map_cons, FiniteSum.Rational.Squares.coordinateSquareSum]
      rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
      change value.re ^ 2 + value.im ^ 2 +
          (FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.re) +
            FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.im)) = _
      ring1

/-- Gaussian list-sum squared norm is at most list length times the sum of entry squared norms.

The factor is the cast of the retained list length and the other factor is the exact recursive sum of its entry squared
norms. Coordinate readback identities reduce the estimate to the two finite rational square-sum bounds. -/
theorem normSq_gaussianSum_le (values : List Basic.Canonical) :
    Basic.Canonical.normSq (gaussianSum values) ≤
      (values.length : Fraction.Rational) * gaussianNormSqSum values := by
  have realBound := FiniteSum.Rational.Squares.coordinateSum_sq_le (values.map fun z => z.re)
  have imaginaryBound := FiniteSum.Rational.Squares.coordinateSum_sq_le (values.map fun z => z.im)
  rw [Map.length_map] at realBound imaginaryBound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  change
    (gaussianSum values).re ^ 2 + (gaussianSum values).im ^ 2 ≤ _
  rw [gaussianSum_re, gaussianSum_im,
    gaussianNormSqSum_coordinates]
  calc
    FiniteSum.Rational.Squares.coordinateSum (values.map fun z => z.re) ^ 2 +
          FiniteSum.Rational.Squares.coordinateSum (values.map fun z => z.im) ^ 2 ≤
        (values.length : Fraction.Rational) *
            FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.re) +
          (values.length : Fraction.Rational) *
            FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.im) :=
      Fraction.Order.Arithmetic.add_le_add_direct realBound imaginaryBound
    _ = (values.length : Fraction.Rational) *
        (FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.re) +
          FiniteSum.Rational.Squares.coordinateSquareSum (values.map fun z => z.im)) := by ring1

end Purelib.Data.Gaussian.Norm.Sum.Basic

public section

namespace Purelib.Data.Gaussian.Norm.Sum.Basic

open Purelib.Data.Gaussian
/-- Summing pointwise Gaussian differences gives the difference of the two sums.

Structural induction retains the original entry order. The head equality is
a scalar additive identity and the tail uses the same recursive Gaussian sum. -/
public theorem gaussianSum_map_sub {Alpha : Type u} (values : List Alpha) (left right : Alpha → Basic.Canonical) :
    gaussianSum (values.map (fun value => left value - right value)) = gaussianSum (values.map left) -
      gaussianSum (values.map right) := by
  induction values with
  | nil => change (0 : Basic.Canonical) = 0 - 0; ring1
  | cons head tail ih => simp only [List.map_cons, gaussianSum, ih, -eq_self, -iff_self]; ring1

/-- The sum of two mapped Gaussian reading lists equals the sum of their pointwise sums.

Both mappings use the same retained finite list. Structural induction preserves every occurrence and combines only
scalar Gaussian additions at the current head. -/
public theorem gaussianSum_map_add {Alpha : Type u} (values : List Alpha) (first last : Alpha →
  Gaussian.Basic.Canonical) :
    gaussianSum (values.map first) + gaussianSum (values.map last) =
      gaussianSum (values.map (fun value => first value + last value)) := by
  induction values with
  | nil => change (0 : Gaussian.Basic.Canonical) + 0 = 0; ring1
  | cons head tail ih =>
      simp only [List.map_cons, gaussianSum, -eq_self, -iff_self]
      rw [← ih]
      ring1

open Purelib.Data.List

/-- Summing a retained concatenation of blocks equals summing their block sums.

The supplied finite block function retains each original block and its order.
Structural recursion follows the original flatMap spine and Gaussian sum fold. -/
theorem gaussianSum_flatMap {Item : Type u} (items : List Item)
    (values : Item → List Gaussian.Basic.Canonical) :
    gaussianSum (items.flatMap values) =
      gaussianSum (items.map (fun item => gaussianSum (values item))) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [Flatten.flatMap_cons, gaussianSum_append, ih]
      rfl

/-- A mapped Gaussian sum over retained blocks equals the sum of their mapped block sums.

Each supplied entry map is applied to the same original block entries. Both
sides preserve the block ordering, repeated occurrences and Gaussian addition. -/
theorem gaussianSum_map_flatMap {Item : Type u} {Entry : Type v}
    (items : List Item) (blocks : Item → List Entry)
    (value : Entry → Gaussian.Basic.Canonical) :
    gaussianSum ((items.flatMap blocks).map value) =
      gaussianSum (items.map (fun item => gaussianSum ((blocks item).map value))) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change gaussianSum (((blocks head) ++ tail.flatMap blocks).map value) = _
      rw [Map.map_append, gaussianSum_append]
      exact congrArg (fun total => gaussianSum ((blocks head).map value) + total) ih

end Purelib.Data.Gaussian.Norm.Sum.Basic

end

namespace Purelib.Data.Gaussian.Norm.Sum.Basic

open Purelib.Data.Gaussian
open Purelib.Data.List

/-- A pairwise-exclusive Boolean mask contributes its value exactly when an entry is selected.

The original ordered list contributes either the one retained selected value or
zero. Pairwise exclusion prevents a second contribution from the unchanged tail. -/
public theorem gaussianSum_mask_of_pairwise {Alpha : Type u} (entries : List Alpha)
    (keep : Alpha → Bool) (value : Basic.Canonical)
    (disjoint : entries.Pairwise (fun first second => keep first = true → keep second = true → False)) :
    gaussianSum (entries.map (fun entry => if keep entry then value else 0)) =
      if entries.any keep then value else 0 := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp disjoint
    rw [List.map_cons, gaussianSum, ih pair.2, List.any_cons]
    cases equal : keep head with
    | false =>
      simp only [if_neg Bool.false_ne_true, Bool.false_or, Gaussian.Basic.zero_add, -eq_self, -iff_self]
      rfl
    | true =>
      have absent : tail.any keep = false := by
        cases selected : tail.any keep with
        | false => rfl
        | true =>
          obtain ⟨other, member, accepted⟩ := Search.any_witness keep tail selected
          exact (pair.1 other member equal accepted).elim
      simp only [absent, Bool.true_or, if_neg Bool.false_ne_true, if_pos (rfl : true = true),
        Gaussian.Basic.add_zero, -eq_self, -iff_self]
      rfl

end Purelib.Data.Gaussian.Norm.Sum.Basic
