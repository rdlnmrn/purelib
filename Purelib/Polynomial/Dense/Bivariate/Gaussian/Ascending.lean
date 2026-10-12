module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Fold
import Purelib.Data.List.Reverse
-- Public weighted sums retain the same defaulting finite-list coordinate owner.
public import Purelib.Data.List.GetD
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Ascending Gaussian bivariate coefficient tables

The original ascending outer table is evaluated by reversing that same list
and folding its inner polynomial evaluations. Finite power-weighted sums
retain the original indices, zero fallback and optional initial and final
zero rows; they do not construct an alternate coefficient table.
-/

public section

namespace Purelib.Polynomial.Dense.Bivariate.Gaussian.Ascending

open Purelib
open Purelib.Algebra
open Purelib.Data
open Purelib.Polynomial

/-- Evaluate the original low-to-high outer coefficient table.

The table is reversed once and evaluated by the original left Horner fold.
Every inner coefficient polynomial is evaluated at the supplied parameter,
while the supplied outer argument controls the same retained accumulator. -/
@[expose] def evalLow
    (coefficients : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (outer parameter : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  coefficients.reverse.foldl
    (fun value coefficient => value * outer + coefficient.eval parameter) 0

/-- A retained ascending head contributes its inner evaluation before the shifted tail.

Reversing the original cons appends its head after the same reversed tail.
The last Horner step therefore adds that coefficient's evaluation to the outer
argument times the unchanged tail value. -/
theorem evalLow_cons
    (coefficient : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (remaining : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (outer parameter : Gaussian.Basic.Canonical) :
    evalLow (coefficient :: remaining) outer parameter =
      coefficient.eval parameter + outer * evalLow remaining outer parameter := by
  unfold evalLow
  rewrite [Data.List.Reverse.reverse_cons, Data.List.Fold.foldl_append]
  change remaining.reverse.foldl
      (fun value coefficient => value * outer + coefficient.eval parameter) 0 * outer +
        coefficient.eval parameter = coefficient.eval parameter + outer *
      remaining.reverse.foldl
        (fun value coefficient => value * outer + coefficient.eval parameter) 0
  exact (add_comm _ _).trans (congrArg (coefficient.eval parameter + ·) (mul_comm _ _))

set_option backward.match.sparseCases false in
/-- A finite coefficient-power sum reads the original ascending table with optional zero rows.

Each in-range row reads its retained natural coordinate with the zero polynomial
as fallback. Extra rows contribute zero, and structural recursion separates the
original first coefficient from the unchanged successor rows. -/
private theorem sumPrefix_evalLow (outer parameter : Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
      (extra : Nat),
      FiniteSum.Fin.sumFin
        (fun row : Fin (coefficients.length + extra) =>
          if (row : Nat) < coefficients.length then
            (Data.List.getD coefficients (row : Nat) 0).eval parameter * outer ^ (row : Nat)
          else 0) = evalLow coefficients outer parameter
  | [], extra => by
      calc
        FiniteSum.Fin.sumFin
            (fun row : Fin (0 + extra) =>
              if (row : Nat) < 0 then
                (Data.List.getD [] (row : Nat) 0 :
                  Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial).eval parameter *
                    outer ^ (row : Nat)
              else 0) =
            FiniteSum.Fin.sumFin
              (fun _ : Fin (0 + extra) => (0 : Gaussian.Basic.Canonical)) := by
          apply FiniteSum.Fin.sumFin_congr
          intro row
          rewrite [if_neg (Nat.not_lt_zero (row : Nat))]
          exact Eq.refl _
        _ = 0 := FiniteSum.Fin.sumFin_zero
  | coefficient :: remaining, extra => by
      rewrite [show (coefficient :: remaining).length + extra =
          (remaining.length + extra) + 1 from Nat.succ_add remaining.length extra]
      rewrite [FiniteSum.Fin.sumFin_succ]
      have headInside : (0 : Nat) < (coefficient :: remaining).length :=
        Nat.zero_lt_succ remaining.length
      rewrite [Fin.val_zero, if_pos headInside]
      change coefficient.eval parameter * outer ^ 0 +
          FiniteSum.Fin.sumFin
            (fun row : Fin (remaining.length + extra) =>
              if (row.succ : Nat) < remaining.length + 1 then
                (Data.List.getD (coefficient :: remaining) (row.succ : Nat) 0).eval parameter *
                  outer ^ (row.succ : Nat)
              else 0) = evalLow (coefficient :: remaining) outer parameter
      rewrite [pow_zero, mul_one]
      have tailIdentity :
          FiniteSum.Fin.sumFin
            (fun row : Fin (remaining.length + extra) =>
              if (row.succ : Nat) < remaining.length + 1 then
                (Data.List.getD (coefficient :: remaining) (row.succ : Nat) 0).eval parameter *
                  outer ^ (row.succ : Nat)
              else 0) =
          FiniteSum.Fin.sumFin
            (fun row : Fin (remaining.length + extra) =>
              (if (row : Nat) < remaining.length then
                (Data.List.getD remaining (row : Nat) 0).eval parameter * outer ^ (row : Nat)
              else 0) * outer) := by
        apply FiniteSum.Fin.sumFin_congr
        intro row
        by_cases inside : (row : Nat) < remaining.length
        · have shifted : (row.succ : Nat) < remaining.length + 1 :=
            Nat.succ_lt_succ inside
          rewrite [if_pos inside, if_pos shifted]
          change (Data.List.getD remaining (row : Nat) 0).eval parameter *
              outer ^ ((row : Nat) + 1) =
            (Data.List.getD remaining (row : Nat) 0).eval parameter *
              outer ^ (row : Nat) * outer
          rewrite [pow_succ]
          exact (mul_assoc _ _ _).symm
        · have shifted : ¬(row.succ : Nat) < remaining.length + 1 :=
            fun retained => inside (Nat.lt_of_succ_lt_succ retained)
          rewrite [if_neg inside, if_neg shifted, zero_mul]
          exact Eq.refl _
      rewrite [tailIdentity, FiniteSum.Fin.sumFin_mul_right,
        sumPrefix_evalLow outer parameter remaining extra, evalLow_cons]
      exact congrArg (coefficient.eval parameter + ·) (mul_comm _ _)

set_option backward.match.sparseCases false in
/-- Shifting a finite coefficient-power sum multiplies the original ascending value by that power.

The displayed offset inserts initial zero rows, and the supplied suffix inserts
final zero rows. Each contributing row reads the same original coefficient
coordinate after subtracting the offset; no coefficient or power is recomputed
through a replacement table. -/
theorem sumShifted_evalLow (outer parameter : Gaussian.Basic.Canonical) :
    ∀ (offset : Nat)
      (coefficients : List Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
      (suffix : Nat),
      FiniteSum.Fin.sumFin
        (fun row : Fin (offset + coefficients.length + suffix) =>
          if offset ≤ (row : Nat) ∧ (row : Nat) < offset + coefficients.length then
            (Data.List.getD coefficients ((row : Nat) - offset) 0).eval parameter *
              outer ^ (row : Nat)
          else 0) = outer ^ offset * evalLow coefficients outer parameter
  | 0, coefficients, suffix => by
      rewrite [Nat.zero_add, pow_zero, one_mul]
      calc
        FiniteSum.Fin.sumFin
            (fun row : Fin (coefficients.length + suffix) =>
              if 0 ≤ (row : Nat) ∧ (row : Nat) < coefficients.length then
                (Data.List.getD coefficients ((row : Nat) - 0) 0).eval parameter *
                  outer ^ (row : Nat)
              else 0) =
            FiniteSum.Fin.sumFin
              (fun row : Fin (coefficients.length + suffix) =>
                if (row : Nat) < coefficients.length then
                  (Data.List.getD coefficients (row : Nat) 0).eval parameter *
                    outer ^ (row : Nat)
                else 0) := by
          apply FiniteSum.Fin.sumFin_congr
          intro row
          by_cases inside : (row : Nat) < coefficients.length
          · rewrite [if_pos ⟨Nat.zero_le _, inside⟩, if_pos inside, Nat.sub_zero]
            exact Eq.refl _
          · rewrite [if_neg (fun condition => inside condition.2), if_neg inside]
            exact Eq.refl _
        _ = evalLow coefficients outer parameter := sumPrefix_evalLow outer parameter coefficients suffix
  | offset + 1, coefficients, suffix => by
      rewrite [show (offset + 1) + coefficients.length + suffix =
          (offset + coefficients.length + suffix) + 1 by
        exact (congrArg (· + suffix) (Nat.succ_add offset coefficients.length)).trans
          (Nat.succ_add (offset + coefficients.length) suffix)]
      rewrite [FiniteSum.Fin.sumFin_succ]
      rewrite [if_neg (fun condition => Nat.not_succ_le_zero offset condition.1), zero_add]
      have upperIdentity : offset + 1 + coefficients.length =
          Nat.succ (offset + coefficients.length) := Nat.succ_add _ _
      have tailIdentity :
          FiniteSum.Fin.sumFin
            (fun row : Fin (offset + coefficients.length + suffix) =>
              if offset + 1 ≤ (row.succ : Nat) ∧
                  (row.succ : Nat) < offset + 1 + coefficients.length then
                (Data.List.getD coefficients ((row.succ : Nat) - (offset + 1)) 0).eval parameter *
                  outer ^ (row.succ : Nat)
              else 0) =
          FiniteSum.Fin.sumFin
            (fun row : Fin (offset + coefficients.length + suffix) =>
              (if offset ≤ (row : Nat) ∧ (row : Nat) < offset + coefficients.length then
                (Data.List.getD coefficients ((row : Nat) - offset) 0).eval parameter *
                  outer ^ (row : Nat)
              else 0) * outer) := by
        apply FiniteSum.Fin.sumFin_congr
        intro row
        by_cases inside : offset ≤ (row : Nat) ∧ (row : Nat) < offset + coefficients.length
        · have shifted : offset + 1 ≤ (row.succ : Nat) ∧
              (row.succ : Nat) < offset + 1 + coefficients.length := by
            rewrite [upperIdentity]
            exact ⟨Nat.succ_le_succ inside.1, Nat.succ_lt_succ inside.2⟩
          rewrite [if_pos inside, if_pos shifted]
          rewrite [Fin.val_succ, Nat.succ_sub_succ]
          change (Data.List.getD coefficients ((row : Nat) - offset) 0).eval parameter *
              outer ^ ((row : Nat) + 1) =
            (Data.List.getD coefficients ((row : Nat) - offset) 0).eval parameter *
              outer ^ (row : Nat) * outer
          rewrite [pow_succ]
          exact (mul_assoc _ _ _).symm
        · have shifted : ¬(offset + 1 ≤ (row.succ : Nat) ∧
              (row.succ : Nat) < offset + 1 + coefficients.length) := by
            intro retained
            rewrite [upperIdentity] at retained
            exact inside ⟨Nat.le_of_succ_le_succ retained.1,
              Nat.lt_of_succ_lt_succ retained.2⟩
          rewrite [if_neg inside, if_neg shifted, zero_mul]
          exact Eq.refl _
      rewrite [tailIdentity, FiniteSum.Fin.sumFin_mul_right,
        sumShifted_evalLow outer parameter offset coefficients suffix, pow_succ]
      ring1

end Purelib.Polynomial.Dense.Bivariate.Gaussian.Ascending
