module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Subtraction
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Explicitly bounded prefix sums

Natural-indexed families retain primitive recursions with displayed counts:
the generic ring prefix reads its head first, while Gaussian and rational
coordinate prefixes append their original final entry. Pointwise certificates
relate the same finite terms, coordinates, scales and reverse index maps.
-/

namespace Purelib.Algebra.FiniteSum.Prefix

open Purelib.Algebra
open Purelib.Algebra.FiniteSum
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Nat

public section

variable {K : Type*} [CommRing K]

/-- Sum the first entries of a natural-indexed family.

Primitive recursion on the supplied count adds the head before the shifted tail in a commutative ring. -/
@[expose] def prefixSum : Nat → (Nat → K) → K
  | 0, _ => 0
  | count + 1, term =>
      term 0 + prefixSum count (fun index => term (index + 1))

/-- A prefix of length zero has sum zero. -/
@[simp] theorem prefixSum_zero (term : Nat → K) :
    prefixSum 0 term = 0 := rfl

/-- A nonempty prefix sum is its first term plus the shifted tail. -/
@[simp] theorem prefixSum_succ (count : Nat) (term : Nat → K) :
    prefixSum (count + 1) term =
      term 0 + prefixSum count (fun index => term (index + 1)) := rfl

/-- The sum of a finite prefix of ones is its length.

The natural count is cast into the coefficient ring. -/
theorem prefixSum_one (count : Nat) :
    prefixSum count (fun _ : Nat => (1 : K)) = (count : K) := by
  induction count with
  | zero =>
      change (0 : K) = ((0 : Nat) : K)
      exact Nat.cast_zero.symm
  | succ count inductionHypothesis =>
      change 1 + prefixSum count (fun _ : Nat => (1 : K)) =
        (count + 1 : Nat)
      rw [inductionHypothesis, NatCast.add, Nat.cast_one]
      ring1

/-- A finite prefix of zero values has sum zero.

The claim holds for every natural count in a commutative ring. -/
theorem prefixSum_zero_values (count : Nat) :
    prefixSum count (fun _ : Nat => (0 : K)) = 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change 0 + prefixSum count (fun _ : Nat => (0 : K)) = 0
      rw [inductionHypothesis, zero_add]

/-- Equal entries on a finite prefix give equal prefix sums.

Equality is required only at indices strictly below the supplied count. -/
theorem prefixSum_congr
    (count : Nat) (first second : Nat → K)
    (equal : ∀ index, index < count → first index = second index) :
    prefixSum count first = prefixSum count second := by
  induction count generalizing first second with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        first 0 + prefixSum count (fun index => first (index + 1)) =
          second 0 + prefixSum count (fun index => second (index + 1))
      rw [equal 0 (by omega0)]
      apply congrArg (second 0 + ·)
      apply inductionHypothesis
      intro index indexBound
      exact equal (index + 1) (by omega0)

/-- A prefix sum preserves pointwise addition.

Both natural-indexed families are read only below the same finite count. -/
theorem prefixSum_add
    (count : Nat) (first second : Nat → K) :
    prefixSum count (fun index => first index + second index) =
      prefixSum count first + prefixSum count second := by
  induction count generalizing first second with
  | zero =>
      change (0 : K) = 0 + 0
      exact (_root_.zero_add (0 : K)).symm
  | succ count inductionHypothesis =>
      change
        first 0 + second 0 +
            prefixSum count
              (fun index => first (index + 1) + second (index + 1)) =
          first 0 + prefixSum count (fun index => first (index + 1)) +
            (second 0 +
              prefixSum count (fun index => second (index + 1)))
      rw [inductionHypothesis]
      ring1

/-- Interchange two explicitly bounded prefix sums.

Both counts are natural numbers, and the rectangular family takes values in a commutative ring. -/
theorem prefixSum_swap
    (firstCount secondCount : Nat) (term : Nat → Nat → K) :
    prefixSum firstCount (fun first =>
        prefixSum secondCount (fun second => term first second)) =
      prefixSum secondCount (fun second =>
        prefixSum firstCount (fun first => term first second)) := by
  induction firstCount generalizing term with
  | zero =>
      calc
        prefixSum 0 (fun first =>
            prefixSum secondCount (fun second => term first second)) =
          0 := rfl
        _ = prefixSum secondCount (fun _ : Nat => (0 : K)) :=
          (prefixSum_zero_values secondCount).symm
        _ = prefixSum secondCount (fun second =>
            prefixSum 0 (fun first => term first second)) := rfl
  | succ firstCount inductionHypothesis =>
      change
        prefixSum secondCount (fun second => term 0 second) +
            prefixSum firstCount (fun first =>
              prefixSum secondCount (fun second =>
                term (first + 1) second)) =
          prefixSum secondCount (fun second =>
            term 0 second + prefixSum firstCount (fun first =>
              term (first + 1) second))
      rw [inductionHypothesis, ← prefixSum_add]

/-- Extract a common left factor from a prefix sum.

The factor and all finitely many entries lie in a commutative ring. -/
theorem prefixSum_mul_left
    (count : Nat) (factor : K) (term : Nat → K) :
    prefixSum count (fun index => factor * term index) =
      factor * prefixSum count term := by
  induction count generalizing term with
  | zero =>
      change (0 : K) = factor * 0
      exact (MulZeroClass.mul_zero factor).symm
  | succ count inductionHypothesis =>
      change
        factor * term 0 +
            prefixSum count
              (fun index => factor * term (index + 1)) =
          factor *
            (term 0 +
              prefixSum count (fun index => term (index + 1)))
      rw [inductionHypothesis]
      ring1

/-- A prefix sum preserves pointwise negation.

Negating the entries below the given count negates their total. -/
theorem prefixSum_neg (count : Nat) (term : Nat → K) :
    prefixSum count (fun index => -term index) =
      -prefixSum count term := by
  calc
    prefixSum count (fun index => -term index) =
        prefixSum count (fun index => (-1 : K) * term index) := by
          apply prefixSum_congr
          intro index indexBound
          ring1
    _ = (-1 : K) * prefixSum count term :=
      prefixSum_mul_left count (-1) term
    _ = -prefixSum count term := by ring1

/-- A prefix sum preserves pointwise subtraction.

Both families are evaluated below the same explicit natural count. -/
theorem prefixSum_sub
    (count : Nat) (first second : Nat → K) :
    prefixSum count (fun index => first index - second index) =
      prefixSum count first - prefixSum count second := by
  calc
    prefixSum count (fun index => first index - second index) =
        prefixSum count (fun index => first index + -second index) := by
          apply prefixSum_congr
          intro index indexBound
          ring1
    _ = prefixSum count first +
        prefixSum count (fun index => -second index) :=
      prefixSum_add count first (fun index => -second index)
    _ = prefixSum count first - prefixSum count second := by
      rw [prefixSum_neg]
      ring1

/-- Extend a prefix sum by its final entry.

The prefix of length `count + 1` is the prefix of length `count` plus the entry at index `count`. -/
theorem prefixSum_succ_last
    (count : Nat) (term : Nat → K) :
    prefixSum (count + 1) term =
      prefixSum count term + term count := by
  induction count generalizing term with
  | zero =>
      change term 0 + 0 = 0 + term 0
      exact (_root_.add_zero (term 0)).trans (_root_.zero_add (term 0)).symm
  | succ count inductionHypothesis =>
      change
        term 0 +
            prefixSum (count + 1) (fun index => term (index + 1)) =
          term 0 +
              prefixSum count (fun index => term (index + 1)) +
            term (count + 1)
      rw [inductionHypothesis]
      ring1

/-- Reversing a finite prefix preserves its sum.

The reversed family reads precisely the indices `count - 1` through zero; values outside the requested prefix are
irrelevant. -/
theorem prefixSum_reverse
    (count : Nat) (term : Nat → K) :
    prefixSum count term =
      prefixSum count (fun index => term (count - 1 - index)) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [prefixSum_succ_last]
      change
        prefixSum count term + term count =
          term count +
            prefixSum count
              (fun index => term (count - (index + 1)))
      have reversedTail :
          prefixSum count
              (fun index => term (count - (index + 1))) =
            prefixSum count
              (fun index => term (count - 1 - index)) := by
        apply prefixSum_congr
        intro index indexBound
        apply congrArg term
        exact (congrArg (fun offset => count - offset) (Nat.add_comm index 1)).trans
          (Subtraction.sub_sub count 1 index).symm
      rw [reversedTail, ← inductionHypothesis]
      ring1

/-- Group an even-length prefix into adjacent pairs.

The sum of `count + count` terms equals the sum of `count` pairs at indices `2*i` and `2*i + 1`. -/
theorem prefixSum_pairs
    (count : Nat) (term : Nat → K) :
    prefixSum (count + count) term =
      prefixSum count
        (fun index => term (index + index) + term (index + index + 1)) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [show Nat.succ count + Nat.succ count =
        (count + count + 1) + 1 by omega0]
      rw [prefixSum_succ_last, prefixSum_succ_last]
      rw [prefixSum_succ_last, inductionHypothesis]
      ring1

/-- Group an odd-length prefix into pairs and one final term.

The first `count + count` entries form adjacent pairs, followed by the entry at index `count + count`. -/
theorem prefixSum_pairs_and_last
    (count : Nat) (term : Nat → K) :
    prefixSum (count + count + 1) term =
      prefixSum count
          (fun index => term (index + index) + term (index + index + 1)) +
        term (count + count) := by
  rw [prefixSum_succ_last, prefixSum_pairs]

/-- Sum a finite prefix of canonical Gaussian values.

Primitive recursion appends the entry at the current final index, starting from zero. -/
@[expose] def sum (term : Nat → Gaussian.Basic.Canonical) : Nat → Gaussian.Basic.Canonical
  | 0 => 0
  | count + 1 => sum term count + term count

/-- The empty Gaussian prefix sum is zero. -/
@[simp] theorem sum_zero (term : Nat → Gaussian.Basic.Canonical) :
    sum term 0 = 0 := rfl

/-- Extending a Gaussian prefix adds the next entry. -/
@[simp] theorem sum_succ (term : Nat → Gaussian.Basic.Canonical) (count : Nat) :
    sum term (count + 1) = sum term count + term count := rfl

/-- Pointwise equal Gaussian families have equal prefix sums.

The equality applies at every index and therefore at every finite prefix length. -/
theorem sum_congr {left right : Nat → Gaussian.Basic.Canonical}
    (equal : ∀ index, left index = right index) : ∀ count,
    sum left count = sum right count
  | 0 => rfl
  | count + 1 => by rw [sum_succ, sum_succ,
      sum_congr equal count, equal count]

/-- Equality on the requested Gaussian prefix preserves its sum.

Only indices strictly below the supplied count need agree. -/
theorem sum_congr_lt {left right : Nat → Gaussian.Basic.Canonical} : ∀ count,
    (∀ index, index < count → left index = right index) →
      sum left count = sum right count
  | 0, equal => rfl
  | count + 1, equal => by
      rw [sum_succ, sum_succ,
        sum_congr_lt count (fun index order =>
          equal index (order.trans (Nat.lt_succ_self count))),
        equal count (Nat.lt_succ_self count)]

/-- Gaussian prefix summation preserves pointwise addition.

The two families are summed over the same finite prefix. -/
theorem sum_add (left right : Nat → Gaussian.Basic.Canonical) : ∀ count,
    sum (fun index => left index + right index) count =
      sum left count + sum right count
  | 0 => by
      apply Gaussian.Basic.ext <;>
        simp only [sum_zero, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.add_re,
          Gaussian.Basic.add_im] <;> ring1
  | count + 1 => by
      rw [sum_succ, sum_succ, sum_succ,
        sum_add left right count]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

/-- Distribute left multiplication through a Gaussian prefix sum.

The fixed canonical Gaussian factor multiplies every entry in the requested finite prefix. -/
theorem mul_sum_left (factor : Gaussian.Basic.Canonical) (term : Nat → Gaussian.Basic.Canonical) :
    ∀ count,
      factor * sum term count =
        sum (fun index => factor * term index) count
  | 0 => by
      apply Gaussian.Basic.ext <;>
        simp only [sum_zero, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.zero_re,
          Gaussian.Basic.zero_im] <;> ring1
  | count + 1 => by
      rw [sum_succ, sum_succ,
        ← mul_sum_left factor term count]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Distribute right multiplication through a Gaussian prefix sum.

Every entry in the requested finite prefix is multiplied by the same canonical Gaussian factor. -/
theorem sum_mul_right (term : Nat → Gaussian.Basic.Canonical) (factor : Gaussian.Basic.Canonical) :
    ∀ count,
      sum term count * factor =
        sum (fun index => term index * factor) count
  | 0 => by
      apply Gaussian.Basic.ext <;>
        simp only [sum_zero, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.zero_re,
          Gaussian.Basic.zero_im] <;> ring1
  | count + 1 => by
      rw [sum_succ, sum_succ,
        ← sum_mul_right term factor count]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Split a nonempty Gaussian prefix at its first entry.

The remaining prefix reads the original family at successor indices. -/
theorem sum_succ_front (term : Nat → Gaussian.Basic.Canonical) : ∀ count,
    sum term (count + 1) =
      term 0 + sum (fun index => term (index + 1)) count
  | 0 => by
      rw [sum_succ, sum_zero, sum_zero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;>
          ring1
  | count + 1 => by
      calc
        sum term (count + 1 + 1) =
            sum term (count + 1) + term (count + 1) := rfl
        _ = (term 0 + sum (fun index => term (index + 1)) count) +
            term (count + 1) := by
          rw [sum_succ_front term count]
        _ = term 0 +
            sum (fun index => term (index + 1)) (count + 1) := by
          rw [sum_succ]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

/-- Split a Gaussian prefix into consecutive finite blocks.

The second block reads entries shifted by the length of the first block. -/
theorem sum_append (term : Nat → Gaussian.Basic.Canonical) (firstCount : Nat) :
    ∀ extraCount,
      sum term (firstCount + extraCount) =
        sum term firstCount +
          sum (fun index => term (firstCount + index)) extraCount
  | 0 => by
      rw [Nat.add_zero, sum_zero,
        _root_.add_zero]
  | extraCount + 1 => by
      rw [show firstCount + (extraCount + 1) =
          firstCount + extraCount + 1 from
            (Nat.add_assoc firstCount extraCount 1).symm,
        sum_succ, sum_succ,
        sum_append term firstCount extraCount]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1

/-- Expand a product of Gaussian prefix sums as a finite double sum.

The outer sum uses the left count and the inner sum uses the right count, multiplying the corresponding entries. -/
theorem sum_product (left right : Nat → Gaussian.Basic.Canonical)
    (leftCount rightCount : Nat) :
    sum left leftCount * sum right rightCount =
      sum
        (fun leftIndex =>
          sum
            (fun rightIndex => left leftIndex * right rightIndex)
            rightCount)
        leftCount := by
  rw [sum_mul_right]
  apply sum_congr
  intro leftIndex
  exact mul_sum_left (left leftIndex) right rightCount

/-- Sum a finite prefix of rational coordinates.

Primitive recursion appends the coordinate at the final index and starts with zero. -/
@[expose] def coordinateSum (term : Nat → Fraction.Rational) : Nat → Fraction.Rational
  | 0 => 0
  | count + 1 => coordinateSum term count + term count

/-- The empty rational prefix sum is zero. -/
@[simp] theorem coordinateSum_zero (term : Nat → Fraction.Rational) :
    coordinateSum term 0 = 0 := rfl

/-- Extending a rational prefix adds the next coordinate. -/
@[simp] theorem coordinateSum_succ (term : Nat → Fraction.Rational) (count : Nat) :
    coordinateSum term (count + 1) =
      coordinateSum term count + term count := rfl

/-- Split a nonempty rational prefix at its first coordinate.

The remaining sum uses the shifted family over a prefix shorter by one. -/
theorem coordinateSum_succ_front (term : Nat → Fraction.Rational) : ∀ count,
    coordinateSum term (count + 1) =
      term 0 + coordinateSum (fun index => term (index + 1)) count
  | 0 => by
      simp only [coordinateSum_succ, coordinateSum_zero]
      ring1
  | count + 1 => by
      calc
        coordinateSum term (count + 1 + 1) =
            coordinateSum term (count + 1) + term (count + 1) := rfl
        _ = (term 0 +
              coordinateSum (fun index => term (index + 1)) count) +
            term (count + 1) := by rw [coordinateSum_succ_front term count]
        _ = term 0 +
            coordinateSum (fun index => term (index + 1)) (count + 1) := by
          rw [coordinateSum_succ]
          ring1

/-- Pointwise equal rational families have equal prefix sums.

Equality at all natural indices yields equality for each finite count. -/
theorem coordinateSum_congr {left right : Nat → Fraction.Rational}
    (equal : ∀ index, left index = right index) : ∀ count,
    coordinateSum left count = coordinateSum right count
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ,
        coordinateSum_congr equal count, equal count]

/-- Equality on a finite rational prefix preserves its sum.

Only coordinates at indices strictly below the requested count need agree. -/
theorem coordinateSum_congr_lt {left right : Nat → Fraction.Rational} : ∀ count,
    (∀ index, index < count → left index = right index) →
      coordinateSum left count = coordinateSum right count
  | 0, equal => rfl
  | count + 1, equal => by
      rw [coordinateSum_succ, coordinateSum_succ,
        coordinateSum_congr_lt count
          (fun index order => equal index (Nat.lt_succ_of_lt order)),
        equal count (Nat.lt_succ_self count)]

/-- Reversing a finite rational prefix preserves its sum.

The reversed family reads the original indices from `count - 1` down to zero. -/
theorem coordinateSum_reverse (term : Nat → Fraction.Rational) : ∀ count,
    coordinateSum term count =
      coordinateSum (fun index => term (count - 1 - index)) count
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ_front]
      change
        coordinateSum term count + term count =
          term count +
            coordinateSum
              (fun index => term (count - index.succ)) count
      have tails :
          coordinateSum (fun index => term (count - index.succ)) count =
            coordinateSum (fun index => term (count - 1 - index)) count := by
        apply coordinateSum_congr_lt
        intro index order
        rw [show count - index.succ = count - 1 - index by
          calc
            count - index.succ = count - (index + 1) := rfl
            _ = count - (1 + index) :=
              congrArg (count - ·) (Nat.add_comm index 1)
            _ = count - 1 - index := (Subtraction.sub_sub count 1 index).symm]
      rw [tails, ← coordinateSum_reverse term count]
      ring1

/-- Rational prefix summation preserves pointwise addition.

Both families are read below the same finite natural count. -/
theorem coordinateSum_add (left right : Nat → Fraction.Rational) : ∀ count,
    coordinateSum (fun index => left index + right index) count =
      coordinateSum left count + coordinateSum right count
  | 0 => by
      simp only [coordinateSum_zero]
      ring1
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ, coordinateSum_succ,
        coordinateSum_add left right count]
      ring1

/-- Distribute a rational scale factor through a prefix sum.

The factor multiplies every coordinate below the supplied count. -/
theorem coordinateSum_scale_left (factor : Fraction.Rational)
    (term : Nat → Fraction.Rational) : ∀ count,
    factor * coordinateSum term count =
      coordinateSum (fun index => factor * term index) count
  | 0 => by
      change factor * 0 = 0
      exact Fraction.Field.mul_zero_direct factor
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_succ,
        ← coordinateSum_scale_left factor term count]
      ring1

/-- A rational family that is zero everywhere has every prefix sum zero.

The pointwise zero hypothesis applies to all natural indices. -/
theorem coordinateSum_all_zero (term : Nat → Fraction.Rational)
    (allZero : ∀ index, term index = 0) : ∀ count,
    coordinateSum term count = 0
  | 0 => rfl
  | count + 1 => by
      rw [coordinateSum_succ, coordinateSum_all_zero term allZero count,
        allZero count, _root_.zero_add]

/-- A rational prefix supported at one included index sums to its value.

The supplied strict bound places the selected position inside the prefix; all other entries are zero. -/
theorem coordinateSum_single (value : Fraction.Rational) : ∀ position count,
    position < count →
      coordinateSum (fun index => if index = position then value else 0)
          count = value
  | position, 0, order => (Nat.not_lt_zero position order).elim
  | position, count + 1, order => by
      rw [coordinateSum_succ]
      by_cases final : position = count
      · subst position
        have prefixZero :
            coordinateSum
                (fun index => if index = count then value else 0) count = 0 := by
          rw [coordinateSum_congr_lt count (by
            intro index order
            rw [if_neg (Nat.ne_of_lt order)])]
          exact coordinateSum_all_zero (fun _ => (0 : Fraction.Rational))
            (fun _ => rfl) count
        rw [if_pos rfl, prefixZero,
          _root_.zero_add]
      · have earlier : position < count :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ order) final
        rw [if_neg (Ne.symm final),
          coordinateSum_single value position count earlier]
        ring1

/-- A finite prefix of nonnegative rational coordinates has nonnegative sum.

The hypothesis provides nonnegativity at every natural index. -/
theorem coordinateSum_nonnegative (term : Nat → Fraction.Rational)
    (termNonnegative : ∀ index, 0 ≤ term index) : ∀ count,
    0 ≤ coordinateSum term count
  | 0 => le_rfl
  | count + 1 =>
      add_nonneg (coordinateSum_nonnegative term termNonnegative count)
        (termNonnegative count)

end

end Purelib.Algebra.FiniteSum.Prefix
