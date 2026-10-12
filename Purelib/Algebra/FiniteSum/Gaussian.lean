module
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Fin
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Sum
import Purelib.Data.List.Fold
import Purelib.Data.List.OfFn.Basic

import Purelib.Tactic.QuotientFreeOmega

/-! Ordered finite Gaussian sums in the original structural carrier. -/

public section

namespace Purelib.Algebra.FiniteSum.Gaussian

open scoped Purelib.Data.Nat

open Purelib.Data.Gaussian.Basic
open Purelib.Data
open Purelib.Algebra
open Purelib.Data.List
open Purelib

/-- Summing a concatenated Gaussian family adds its two block sums.

The family is assembled by `Fin.addCases` over the explicit dimensions of its left and right blocks. -/
public theorem sumFin_addCases {m n : Nat}
    (left : Fin m → Canonical) (right : Fin n → Canonical) :
    FiniteSum.Fin.sumFin
        (fun index : Fin (m + n) =>
          Data.Fin.addCases left right index) =
      FiniteSum.Fin.sumFin left +
        FiniteSum.Fin.sumFin right := by
  unfold FiniteSum.Fin.sumFin
  rw [Data.List.OfFn.Basic.ofFn_add, Fold.foldl_append,
    Purelib.Data.Gaussian.Sum.foldl_add_from]
  congr 2
  · exact Data.List.OfFn.Basic.ofFn_congr
      (Data.Fin.addCases_left left right)
  · exact Data.List.OfFn.Basic.ofFn_congr
      (Data.Fin.addCases_right left right)

/-- A Gaussian family indexed by `Fin 0` has sum zero. -/
private theorem sumFin_empty_gaussian (values : Fin 0 -> Canonical) :
    FiniteSum.Fin.sumFin values = 0 := by
  calc
    FiniteSum.Fin.sumFin values =
        FiniteSum.Fin.sumFin
          (fun _ : Fin 0 => (0 : Canonical)) :=
      FiniteSum.Fin.sumFin_congr
        (fun index => Fin.elim0 index)
    _ = 0 := FiniteSum.Fin.sumFin_zero

/-- A two-entry Gaussian sum is the sum of entries zero and one. -/
theorem sumFin_two_gaussian (values : Fin 2 -> Canonical) :
    FiniteSum.Fin.sumFin values = values 0 + values 1 := by
  rw [FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Gaussian.sumFin_empty_gaussian]
  rw [show (Fin.succ 0 : Fin 2) = 1 by rfl]
  rw [Gaussian.Basic.add_zero]

/-- Gaussian conjugation commutes with a displayed finite sum.

The conjugated entries use the same retained finite indices and original Gaussian addition operations. -/
theorem conj_sumFin {n : Nat} (values : Fin n → Purelib.Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (Purelib.Algebra.FiniteSum.Fin.sumFin values) =
      Purelib.Algebra.FiniteSum.Fin.sumFin (fun index => Data.Gaussian.Basic.conj (values index)) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [Purelib.Algebra.FiniteSum.Fin.sumFin_succ, Purelib.Algebra.FiniteSum.Fin.sumFin_succ,
        Purelib.Data.Gaussian.Basic.conj_add, inductionHypothesis]

/-- Two distinct bounded coordinates retain the sum over the complete pair.

Both original entries are used once. The two possible coordinate orders differ
only by Gaussian addition's commutativity; repeated indices are excluded. -/
theorem two_sheets (value : Fin 2 → Canonical) (first last : Fin 2)
    (different : first ≠ last) : value first + value last = value 0 + value 1 := by
  revert different
  refine Data.Fin.cases_induction ?_
    (Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty)) first
  · refine Data.Fin.cases_induction ?_
      (Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty)) last
    · intro different; exact (different rfl).elim
    · intro _; rfl
  · refine Data.Fin.cases_induction ?_
      (Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty)) last
    · intro _; exact Data.Gaussian.Basic.add_comm _ _
    · intro different; exact (different rfl).elim

end Purelib.Algebra.FiniteSum.Gaussian
