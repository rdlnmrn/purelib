module

public import Purelib.Polynomial.Recurrence.Mode
public import Purelib.Polynomial.Dense.Division.Synthetic
public import Purelib.Polynomial.Dense.Companion.Execution
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Original coefficient rows on generalized modes

A finite descending coefficient table acts on the original binomial mode at
one finite starting index. Original synthetic reconstruction separates its
first-order difference and retained remainder without scalar division.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode

open Purelib.Polynomial.Dense.Division
open Purelib.Data
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin

variable {K : Type*} [CommRing K]

/-- Apply a finite descending coefficient row to one original generalized mode.

Each coefficient multiplies the original mode reading at its displayed degree
plus the supplied finite starting index. The source table is not normalized.
-/
@[expose] def coefficientRow (coefficients : List K) (root : K) (order start : Nat) : K :=
  match coefficients with
  | [] => 0
  | leading :: remaining =>
      leading * entry root order (start + remaining.length) + coefficientRow remaining root order start

/-- The empty coefficient row acts as zero at every finite index. -/
theorem coefficientRow_nil (root : K) (order start : Nat) : coefficientRow [] root order start = 0 := rfl

/-- The original order-zero startup row is the original descending Horner evaluation. -/
theorem coefficientRow_eval (coefficients : List K) (root : K) :
    coefficientRow coefficients root 0 0 = Dense.Basic.DensePolynomial.evalCoeffs root coefficients := by
  induction coefficients with
  | nil => rfl
  | cons leading remaining previous =>
      rw [coefficientRow, Dense.Basic.DensePolynomial.evalCoeffs_cons_expansion,
        entry_zero_order, Nat.zero_add, previous]

/-- Scaling every original coefficient scales its same complete generalized-mode row. -/
theorem coefficientRow_map_mul (coefficients : List K) (scalar root : K) (order start : Nat) :
    coefficientRow (coefficients.map (scalar * ·)) root order start =
      scalar * coefficientRow coefficients root order start := by
  induction coefficients with
  | nil => exact (mul_zero scalar).symm
  | cons leading remaining previous =>
      rw [List.map_cons, coefficientRow, coefficientRow, List.Map.length_map, previous]
      ring0

/-- Concatenated descending rows retain the right-table degree offset on the same original mode. -/
theorem coefficientRow_append (first second : List K) (root : K) (order start : Nat) :
    coefficientRow (first ++ second) root order start =
      coefficientRow first root order (start + second.length) + coefficientRow second root order start := by
  induction first with
  | nil => exact (zero_add _).symm
  | cons leading remaining previous =>
      change leading * entry root order (start + (remaining ++ second).length) +
          coefficientRow (remaining ++ second) root order start =
        (leading * entry root order (start + second.length + remaining.length) +
          coefficientRow remaining root order (start + second.length)) + coefficientRow second root order start
      rw [Append.length_append, previous]
      have position : start + (remaining.length + second.length) =
          start + second.length + remaining.length := by omega0
      rw [position]
      ring0

/-- An ascending retained source table gives the exact original finite coefficient sum on modes. -/
theorem coefficientRow_reverse (coefficients : List K) (root : K) (order start : Nat) :
    coefficientRow coefficients.reverse root order start =
      sumFin (fun index : Fin coefficients.length =>
        getD coefficients index.val 0 * entry root order (start + index.val)) := by
  induction coefficients generalizing start with
  | nil => rfl
  | cons leading remaining previous =>
      rw [Reverse.reverse_cons, coefficientRow_append]
      change coefficientRow remaining.reverse root order (start + 1) +
          (leading * entry root order (start + 0) + 0) = _
      rw [previous, Nat.add_zero, add_zero, sumFin_succ]
      change sumFin (fun index : Fin remaining.length =>
          getD remaining index.val 0 * entry root order (start + 1 + index.val)) +
          leading * entry root order start =
        leading * entry root order (start + 0) + sumFin (fun index : Fin remaining.length =>
          getD remaining index.val 0 * entry root order (start + (index.val + 1)))
      rw [Nat.add_zero]
      have shifted : sumFin (fun index : Fin remaining.length =>
          getD remaining index.val 0 * entry root order (start + 1 + index.val)) =
          sumFin (fun index : Fin remaining.length =>
            getD remaining index.val 0 * entry root order (start + (index.val + 1))) := by
        apply sumFin_congr
        intro index
        have position : start + 1 + index.val = start + (index.val + 1) := by omega0
        rw [position]
      rw [shifted, Nat.add_zero, add_comm]

/-- Changing the original leading slot subtracts its exact mode contribution. -/
theorem coefficientRow_head_sub (leading adjustment : K) (remaining : List K) (root : K)
    (order start : Nat) :
    coefficientRow ((leading - adjustment) :: remaining) root order start =
      coefficientRow (leading :: remaining) root order start -
        adjustment * entry root order (start + remaining.length) := by
  rw [coefficientRow, coefficientRow]
  ring0

/-- An order-zero mode coefficient row has the same first-order root-difference law. -/
theorem coefficientRow_difference_zero (coefficients : List K) (root center : K) (start : Nat) :
    coefficientRow coefficients root 0 (start + 1) - center * coefficientRow coefficients root 0 start =
      (root - center) * coefficientRow coefficients root 0 start := by
  induction coefficients with
  | nil => change 0 - center * 0 = (root - center) * 0; ring0
  | cons leading remaining previous =>
      have position : start + 1 + remaining.length = (start + remaining.length) + 1 := by omega0
      change (leading * entry root 0 (start + 1 + remaining.length) +
          coefficientRow remaining root 0 (start + 1)) -
          center * (leading * entry root 0 (start + remaining.length) +
            coefficientRow remaining root 0 start) =
        (root - center) * (leading * entry root 0 (start + remaining.length) +
          coefficientRow remaining root 0 start)
      rw [position]
      calc
        _ = leading * (entry root 0 (start + remaining.length + 1) -
              center * entry root 0 (start + remaining.length)) +
            (coefficientRow remaining root 0 (start + 1) -
              center * coefficientRow remaining root 0 start) := by ring0
        _ = _ := by rw [entry_difference_zero, previous]; ring0

/-- Higher mode rows retain their same original preceding-order contribution under a difference. -/
theorem coefficientRow_difference_succ (coefficients : List K) (root center : K) (order start : Nat) :
    coefficientRow coefficients root (order + 1) (start + 1) -
      center * coefficientRow coefficients root (order + 1) start =
      (root - center) * coefficientRow coefficients root (order + 1) start +
        coefficientRow coefficients root order start := by
  induction coefficients with
  | nil => change 0 - center * 0 = (root - center) * 0 + 0; ring0
  | cons leading remaining previous =>
      have position : start + 1 + remaining.length = (start + remaining.length) + 1 := by omega0
      change (leading * entry root (order + 1) (start + 1 + remaining.length) +
          coefficientRow remaining root (order + 1) (start + 1)) -
          center * (leading * entry root (order + 1) (start + remaining.length) +
            coefficientRow remaining root (order + 1) start) =
        (root - center) * (leading * entry root (order + 1) (start + remaining.length) +
          coefficientRow remaining root (order + 1) start) +
            (leading * entry root order (start + remaining.length) + coefficientRow remaining root order start)
      rw [position]
      calc
        _ = leading * (entry root (order + 1) (start + remaining.length + 1) -
              center * entry root (order + 1) (start + remaining.length)) +
            (coefficientRow remaining root (order + 1) (start + 1) -
              center * coefficientRow remaining root (order + 1) start) := by ring0
        _ = _ := by rw [entry_difference_succ, previous]; ring0

/-- Original synthetic reassembly acts by the same first-order difference plus its retained remainder.

The literal coefficient reconstruction is used at every displayed slot.
The identity holds over a commutative ring without coefficient cancellation.
-/
theorem coefficientRow_reassemble (center : K) (quotient : List K) (remainder root : K)
    (order start : Nat) :
    coefficientRow (Synthetic.reassemble center quotient remainder) root order start =
      coefficientRow quotient root order (start + 1) -
        center * coefficientRow quotient root order start + remainder * entry root order start := by
  induction quotient with
  | nil =>
      change remainder * entry root order (start + 0) + 0 = 0 - center * 0 + remainder * entry root order start
      rw [Nat.add_zero]
      ring0
  | cons leading remaining previous =>
      have length := Synthetic.reassemble_length center remaining remainder
      cases shape : Synthetic.reassemble center remaining remainder with
      | nil => exact False.elim (Synthetic.reassemble_nonempty center remaining remainder shape)
      | cons next tail =>
          rw [shape] at previous length
          have tailLength : tail.length = remaining.length := Nat.succ.inj length
          rw [Synthetic.reassemble, shape]
          change leading * entry root order (start + (tail.length + 1)) +
              coefficientRow ((next - leading * center) :: tail) root order start =
            (leading * entry root order (start + 1 + remaining.length) +
              coefficientRow remaining root order (start + 1)) -
              center * (leading * entry root order (start + remaining.length) +
                coefficientRow remaining root order start) + remainder * entry root order start
          rw [coefficientRow_head_sub, previous, tailLength]
          have position : start + 1 + remaining.length = start + (remaining.length + 1) := by omega0
          rw [position]
          ring0

/-- At its own root, a synthetic linear factor removes the next generalized-mode order. -/
theorem coefficientRow_reassemble_same (root : K) (quotient : List K) (remainder : K)
    (order start : Nat) :
    coefficientRow (Synthetic.reassemble root quotient remainder) root (order + 1) start =
      coefficientRow quotient root order start + remainder * entry root (order + 1) start := by
  rw [coefficientRow_reassemble, coefficientRow_difference_succ, sub_self, zero_mul, zero_add]

/-- At order zero the same original synthetic factor leaves only its retained remainder contribution. -/
theorem coefficientRow_reassemble_zero (root : K) (quotient : List K) (remainder : K) (start : Nat) :
    coefficientRow (Synthetic.reassemble root quotient remainder) root 0 start =
      remainder * entry root 0 start := by
  rw [coefficientRow_reassemble, coefficientRow_difference_zero, sub_self, zero_mul, zero_add]

/-- At order zero the original retained synthetic result contributes only its same remainder. -/
theorem coefficientRow_synthetic_zero {polynomial : Dense.Basic.DensePolynomial K} {root : K}
    (result : Synthetic.Result polynomial root) (nonempty : polynomial.coeffs ≠ []) (start : Nat) :
    coefficientRow polynomial.coeffs root 0 start = result.remainder * entry root 0 start :=
  (congrArg (fun coefficients => coefficientRow coefficients root 0 start)
    (result.reassemble_eq nonempty).symm).trans
      (coefficientRow_reassemble_zero root result.quotient.coeffs result.remainder start)

/-- The original retained synthetic result lowers one generalized-mode order with its same remainder. -/
theorem coefficientRow_synthetic {polynomial : Dense.Basic.DensePolynomial K} {root : K}
    (result : Synthetic.Result polynomial root) (nonempty : polynomial.coeffs ≠ []) (order start : Nat) :
    coefficientRow polynomial.coeffs root (order + 1) start =
      coefficientRow result.quotient.coeffs root order start + result.remainder * entry root (order + 1) start :=
  (congrArg (fun coefficients => coefficientRow coefficients root (order + 1) start)
    (result.reassemble_eq nonempty).symm).trans
      (coefficientRow_reassemble_same root result.quotient.coeffs result.remainder order start)

/-- A zero retained synthetic remainder removes the same original linear factor from the mode row. -/
theorem coefficientRow_synthetic_vanish {polynomial : Dense.Basic.DensePolynomial K} {root : K}
    (result : Synthetic.Result polynomial root) (nonempty : polynomial.coeffs ≠ [])
    (zero : result.remainder = 0) (order start : Nat) :
    coefficientRow polynomial.coeffs root (order + 1) start =
      coefficientRow result.quotient.coeffs root order start := by
  rw [coefficientRow_synthetic result nonempty, zero, zero_mul, add_zero]

/-- The original companion's source table acts by its same leading and cached lower coefficient rows. -/
theorem coefficientRow_companion [DecidableEq K] {polynomial : Dense.Basic.DensePolynomial K}
    (companion : Dense.Companion polynomial) (root : K) (order start : Nat) :
    coefficientRow polynomial.normalize.coeffs root order start =
      polynomial.leadingCoeff * entry root order (start + polynomial.natDegree) +
        sumFin (fun column : Fin polynomial.natDegree =>
          getD companion.coefficients column.val 0 * entry root order (start + column.val)) := by
  have lower := coefficientRow_reverse companion.coefficients root order start
  have originalLower : coefficientRow companion.coefficients.reverse root order start =
      sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * entry root order (start + column.val)) :=
    companion.count_eq ▸ lower
  rw [companion.source_eq]
  change polynomial.leadingCoeff * entry root order (start + companion.coefficients.reverse.length) +
    coefficientRow companion.coefficients.reverse root order start = _
  rw [Reverse.length_reverse, companion.count_eq, originalLower]

/-- Original mode windows satisfy every complete original companion row certified by their finite coefficient action. -/
theorem window_satisfies [DecidableEq K] {polynomial : Dense.Basic.DensePolynomial K}
    (companion : Dense.Companion polynomial) (root : K) (order count : Nat)
    (equations : ∀ start, start + polynomial.natDegree < count →
      coefficientRow polynomial.normalize.coeffs root order start = 0) :
    companion.Satisfies (window root order count) := by
  intro start bound
  have original := equations start bound
  rw [coefficientRow_companion companion] at original
  have lower : sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 *
          window root order count ⟨start + column.val, Nat.lt_trans (Nat.add_lt_add_left column.isLt start) bound⟩) =
      sumFin (fun column : Fin polynomial.natDegree =>
        getD companion.coefficients column.val 0 * entry root order (start + column.val)) := by
    apply sumFin_congr
    intro column
    rw [window_at]
  rw [lower, window_at]
  exact (add_comm _ _).trans original

end Purelib.Polynomial.Recurrence.Mode
