module
import Purelib.Algebra.Ring.IntCast
import Purelib.Tactic.Ring
import Purelib.Data.List.Fold
import Purelib.Data.List.OfFn.Basic
-- Public first-entry signatures retain the original successor certificate.
public import Purelib.Data.Nat.Order
-- Public negation signatures retain the original subtraction parent certificate.
public import Purelib.Algebra.Group.Negation
-- Specialized public integer laws retain this original ring record.
public import Purelib.Algebra.Ring.Int
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
-- Clients reduce the retained sum through the original finite table body.
public import Init.Data.List.OfFn

/-!
# Ordered finite sums

A finite sum folds addition from zero over the original `List.ofFn` table.
The laws retain the same finite indices, displayed coefficient families and
commutative-ring operations; no alternate enumeration is introduced.
-/

public section

namespace Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.List
open Purelib.Algebra
open scoped Purelib.Data.Nat
attribute [local instance high] Group.Negation.subNegZeroMonoid

universe u
variable {K : Type*} [CommRing K]

/-- Sum a function on an explicit finite index type.

The values are enumerated by `List.ofFn` and accumulated from zero in their index order; the coefficient type is a
commutative ring. -/
@[expose] def sumFin {n : Nat} (values : Fin n → K) : K :=
  (List.ofFn values).foldl (fun a b => a + b) 0

/-- The finite sum of zero entries is zero.

This holds in every dimension, including the empty index type. -/
@[simp] theorem sumFin_zero {n : Nat} :
    sumFin (fun _ : Fin n => (0 : K)) = 0 := by
  unfold sumFin
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [OfFn.Basic.ofFn_succ, List.foldl_cons]
      rw [zero_add]
      exact inductionHypothesis

/-- Separate the initial accumulator from a list sum.

In a commutative ring, folding addition from an arbitrary accumulator equals that accumulator plus the fold from zero.
-/
private theorem foldl_add_eq_accumulator_add
    (values : List K) (accumulator : K) :
    values.foldl (fun a b => a + b) accumulator =
      accumulator + values.foldl (fun a b => a + b) 0 := by
  induction values generalizing accumulator with
  | nil =>
      change accumulator = accumulator + 0
      ring1
  | cons value remaining inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [List.foldl_cons, show (0 : K) + value = value by ring1]
      rw [inductionHypothesis value]
      ring1

/-- Split a nonempty finite sum into its first entry and successor tail.

The tail retains its `Fin n` indices and reads the original values through `Fin.succ`. -/
theorem sumFin_succ (values : Fin (n + 1) → K) :
    sumFin values = values 0 + sumFin (fun i : Fin n => values i.succ) := by
  unfold sumFin
  rw [OfFn.Basic.ofFn_succ, List.foldl_cons]
  rw [foldl_add_eq_accumulator_add]
  ring1

/-- Pointwise equal finite families have equal sums.

Only equality at each explicit index is required; equality of the functions themselves is unnecessary. -/
theorem sumFin_congr {n : Nat} {left right : Fin n → K}
    (equal : ∀ index, left index = right index) :
    sumFin left = sumFin right := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ, equal 0,
        inductionHypothesis (fun index => equal index.succ)]

/-- Finite summation preserves pointwise addition.

Both families use the same finite index type and take values in a commutative ring. -/
theorem sumFin_add {n : Nat} (left right : Fin n → K) :
    sumFin (fun i => left i + right i) = sumFin left + sumFin right := by
  induction n with
  | zero => exact (add_zero (0 : K)).symm
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ, sumFin_succ,
        inductionHypothesis (fun i => left i.succ) (fun i => right i.succ)]
      ring1

/-- Extract a common left factor from a finite sum.

The factor and all entries lie in the same commutative ring. -/
theorem sumFin_mul_left {n : Nat} (a : K) (values : Fin n → K) :
    sumFin (fun i => a * values i) = a * sumFin values := by
  induction n with
  | zero =>
      change (0 : K) = a * 0
      exact (mul_zero a).symm
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ,
        inductionHypothesis (fun i => values i.succ)]
      ring1

/-- Extract a common right factor from a finite sum.

The factor and all entries lie in the same commutative ring. -/
theorem sumFin_mul_right {n : Nat} (values : Fin n → K) (a : K) :
    sumFin (fun i => values i * a) = sumFin values * a := by
  calc
    sumFin (fun i => values i * a) =
        sumFin (fun i => a * values i) :=
      sumFin_congr (fun _ => mul_comm _ _)
    _ = a * sumFin values := sumFin_mul_left a values
    _ = sumFin values * a := mul_comm _ _

/-- Finite summation preserves pointwise negation.

Negating each entry negates the total in any commutative ring. -/
theorem sumFin_neg {n : Nat} (values : Fin n → K) :
    sumFin (fun i => -values i) = -sumFin values := by
  calc
    sumFin (fun i => -values i) =
        sumFin (fun i => (-1 : K) * values i) :=
      sumFin_congr (fun _ => by ring1)
    _ = (-1 : K) * sumFin values := sumFin_mul_left _ _
    _ = -sumFin values := by ring1

/-- Finite summation preserves pointwise subtraction.

The two families share one finite index type over a commutative ring. -/
theorem sumFin_sub {n : Nat} (left right : Fin n → K) :
    sumFin (fun i => left i - right i) = sumFin left - sumFin right := by
  calc
    sumFin (fun i => left i - right i) =
        sumFin (fun i => left i + -right i) :=
      sumFin_congr (fun _ => sub_eq_add_neg _ _)
    _ = sumFin left + sumFin (fun i => -right i) := sumFin_add _ _
    _ = sumFin left + -sumFin right := by rw [sumFin_neg]
    _ = sumFin left - sumFin right := (sub_eq_add_neg _ _).symm

/-- Interchange the order of two finite sums.

A rectangular family over `Fin m` and `Fin n` has the same total in either index order. -/
theorem sumFin_swap {m n : Nat}
    (values : Fin m → Fin n → K) :
    sumFin (fun i => sumFin (values i)) =
      sumFin (fun j => sumFin (fun i => values i j)) := by
  induction m with
  | zero =>
      change (0 : K) = sumFin (fun _ : Fin n => 0)
      exact sumFin_zero.symm
  | succ m inductionHypothesis =>
      rw [sumFin_succ, inductionHypothesis]
      rw [← sumFin_add]
      apply sumFin_congr
      intro j
      rw [sumFin_succ]

/-- A finite family supported at one index sums to that entry.

The selected index belongs to the supplied finite index type; every other summand is zero. -/
theorem sumFin_ite_eq {n : Nat} (target : Fin n) (values : Fin n → K) :
    sumFin (fun i => if i = target then values i else 0) = values target := by
  induction n with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rcases target with ⟨value, bound⟩
      cases value with
      | zero =>
          change sumFin (fun i : Fin (n + 1) => if i = 0 then values i else 0) = values 0
          rw [sumFin_succ, if_pos rfl]
          have tailZero : sumFin (fun i : Fin n => if i.succ = 0 then values i.succ else 0) =
              sumFin (fun _ : Fin n => (0 : K)) :=
            sumFin_congr (fun i => if_neg (fun impossible =>
              Nat.noConfusion (congrArg Fin.val impossible)))
          rw [tailZero, sumFin_zero]
          exact add_zero _
      | succ value =>
          let targetTail : Fin n := ⟨value, Nat.lt_of_succ_lt_succ bound⟩
          change sumFin (fun i : Fin (n + 1) =>
            if i = targetTail.succ then values i else 0) = values targetTail.succ
          rw [sumFin_succ, if_neg (fun impossible =>
            Nat.noConfusion (congrArg Fin.val impossible).symm)]
          have tailEqual : sumFin (fun i : Fin n =>
              if i.succ = targetTail.succ then values i.succ else 0) =
              sumFin (fun i : Fin n => if i = targetTail then values i.succ else 0) := by
            apply sumFin_congr
            intro i
            by_cases equal : i = targetTail
            · cases equal
              rw [if_pos rfl, if_pos rfl]
            · rw [if_neg equal, if_neg (fun successorEqual =>
                equal (Fin.ext (Nat.succ.inj (congrArg Fin.val successorEqual))))]
          rw [tailEqual, zero_add]
          exact ih targetTail (fun i => values i.succ)

/-- Split a finite sum at a prescribed block boundary.

The first block uses `Fin.castAdd` and the second uses `Fin.natAdd`, preserving the original positions in the family. -/
theorem sumFin_split {left right : Nat} (values : Fin (left + right) → K) :
    sumFin values = sumFin (fun index => values (Fin.castAdd right index)) +
      sumFin (fun index => values (Fin.natAdd left index)) := by
  unfold sumFin
  rw [OfFn.Basic.ofFn_add, Fold.foldl_append, foldl_add_eq_accumulator_add]
  rfl

section
/-- An integer family indexed by the empty finite type has sum zero.

The original table and additive fold have no entries, so the retained
initial integer accumulator is their exact result. -/
theorem sumFin_empty (values : Fin 0 → Int) : sumFin values = 0 := rfl

/-- A two-entry integer sum is the sum of entries zero and one.

Two applications of the original successor decomposition expose both
retained integer entries. The empty remainder contributes the integer zero. -/
theorem sumFin_two_int (values : Fin 2 -> Int) :
    sumFin values = values 0 + values 1 := by
  rw [sumFin_succ, sumFin_succ, sumFin_empty]
  change values 0 + (values 1 + 0) = values 0 + values 1
  exact congrArg (fun tail => values 0 + tail) (Int.add_zero (values 1))
end

/-- Integer casting commutes with the finite indexed sum.

The original integer family and coefficient-ring casts retain the same bounded indices and ordered summation. -/
theorem cast_sum {n : Nat} (values : Fin n → Int) :
    ((sumFin values : Int) : K) = sumFin (fun index => (values index : K)) := by
  induction n with
  | zero => exact Ring.IntCast.cast_zero
  | succ n ih => rw [sumFin_succ, sumFin_succ, Ring.IntCast.add, ih]

end Purelib.Algebra.FiniteSum.Fin
