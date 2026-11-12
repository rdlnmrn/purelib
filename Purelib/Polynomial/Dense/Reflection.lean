module

public import Purelib.Algebra.Monogenic.Algebra
public import Purelib.Algebra.Monogenic.Cyclic.Shift
public import Purelib.Polynomial.Dense.Map.Basic
import Purelib.Data.List.GetD
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Nat.Order

/-!
# Formal coefficient reflection in finite shift algebras

The same original polynomial is mapped coefficientwise into the original
cyclic matrix algebra and evaluated by its original Horner scan. Reading one
distinguished column returns each original ascending coefficient slot. A
finite dimension computed from two original table lengths therefore reflects
equality of their normalized original descending tables, over any commutative ring.
-/

public section

namespace Purelib.Polynomial.Dense

open Purelib.Data.List
open Purelib.Algebra.Monogenic
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Matrix
open Basic (DensePolynomial)

variable {K : Type*}

namespace Basic.DensePolynomial

variable [Zero K]

/-- Equal original reversed coefficient readings determine the original normalized descending tables.

Padding the two reversed tables by repeated zeros produces equal-length
original lists with the same readings. Their reversals differ only by zero
prefixes, which the original normalization removes.
-/
theorem normalize_eq_of_reverse_coefficients [DecidableEq K] (left right : DensePolynomial K)
    (readings : ∀ index, getD left.coeffs.reverse index 0 = getD right.coeffs.reverse index 0) :
    left.normalize = right.normalize := by
  have padded : left.coeffs.reverse ++ List.replicate right.coeffs.length 0 =
      right.coeffs.reverse ++ List.replicate left.coeffs.length 0 := by
    apply eq_of_getD 0
    · rw [Append.length_append, Append.length_append, Reverse.length_reverse, Reverse.length_reverse,
        Replicate.length_replicate, Replicate.length_replicate]
      exact Nat.add_comm _ _
    · intro index
      rw [getD_append_replicate, getD_append_replicate]
      exact readings index
  have reversed := congrArg List.reverse padded
  rw [Reverse.reverse_append, Reverse.reverse_append, Reverse.reverse_replicate, Reverse.reverse_replicate,
    Reverse.reverse_reverse, Reverse.reverse_reverse] at reversed
  have scanned := congrArg (fun values : List K => values.dropWhile (· = 0)) reversed
  have zeroSelected : decide ((0 : K) = 0) = true := decide_eq_true rfl
  rw [DropWhile.replicate_append (fun coefficient : K => decide (coefficient = 0))
      (0 : K) zeroSelected,
    DropWhile.replicate_append (fun coefficient : K => decide (coefficient = 0))
      (0 : K) zeroSelected] at scanned
  exact DensePolynomial.ext scanned

end Basic.DensePolynomial

namespace Reflection

variable [CommRing K]

/-- A shift algebra evaluation's distinguished column reads the same original ascending coefficient slot.

The cyclic owner and its original zero coordinate are retained. Finite powers
beyond the matrix dimension vanish automatically; no completed sequence,
polynomial quotient or infinite set of evaluation points is used.
-/
theorem coefficient_readback {dimension : Nat} (cyclic : Cyclic (Shift.matrix K dimension))
    (origin : cyclic.origin.val = 0) (polynomial : DensePolynomial K) (row : Fin dimension) :
    ((Map.map (Cyclic.Element.scalar cyclic) polynomial).eval (Cyclic.Element.root cyclic)).matrix
        row cyclic.origin = getD polynomial.coeffs.reverse row.val 0 := by
  let root := Cyclic.Element.root cyclic
  have expansion := Map.evalCoeffs_reverse_sum (Cyclic.Element.scalar cyclic)
    (Cyclic.Element.scalar_zero cyclic) root polynomial.coeffs.reverse
  rw [Reverse.reverse_reverse] at expansion
  change (DensePolynomial.evalCoeffs root
    (polynomial.coeffs.map (Cyclic.Element.scalar cyclic))).matrix row cyclic.origin = _
  rw [expansion, Cyclic.Element.sumFin_apply]
  by_cases bounded : row.val < polynomial.coeffs.reverse.length
  · let selected : Fin polynomial.coeffs.reverse.length := ⟨row.val, bounded⟩
    calc
      _ = sumFin (fun index => if index = selected then
          getD polynomial.coeffs.reverse index.val 0 else 0) := by
        apply sumFin_congr
        intro index
        rw [Cyclic.Element.scalar_mul_apply, Cyclic.Element.pow_matrix]
        change getD polynomial.coeffs.reverse index.val 0 *
          Arithmetic.power (Shift.matrix K dimension) index.val row cyclic.origin = _
        rw [Shift.power_apply, origin, Nat.zero_add]
        by_cases same : index = selected
        · rw [if_pos same, if_pos (congrArg Fin.val same).symm, mul_one]
        · rw [if_neg same, if_neg (fun equal => same (Fin.ext equal.symm)), mul_zero]
      _ = getD polynomial.coeffs.reverse selected.val 0 :=
        sumFin_ite_eq selected (fun index => getD polynomial.coeffs.reverse index.val 0)
      _ = _ := rfl
  · calc
      _ = sumFin (fun _ : Fin polynomial.coeffs.reverse.length => (0 : K)) := by
        apply sumFin_congr
        intro index
        rw [Cyclic.Element.scalar_mul_apply, Cyclic.Element.pow_matrix]
        change getD polynomial.coeffs.reverse index.val 0 *
          Arithmetic.power (Shift.matrix K dimension) index.val row cyclic.origin = _
        rw [Shift.power_apply, origin, Nat.zero_add]
        have different : row.val ≠ index.val := fun same => bounded (same ▸ index.isLt)
        rw [if_neg different, mul_zero]
      _ = 0 := sumFin_zero
      _ = _ := (getD_eq_default_of_length_le _ _ _ (Nat.le_of_not_lt bounded)).symm

/-- Equality of original evaluations in the one finite shift algebra computed from both source lengths.

The positive dimension is one more than the larger original coefficient
length. Its same cyclic power table supplies the common algebra, original
scalar embedding and root in both retained evaluation expressions.
-/
@[expose] def Agreement (left right : DensePolynomial K) : Prop :=
  let dimension := Nat.max left.coeffs.length right.coeffs.length + 1
  let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
  (Map.map (Cyclic.Element.scalar cyclic) left).eval (Cyclic.Element.root cyclic) =
    (Map.map (Cyclic.Element.scalar cyclic) right).eval (Cyclic.Element.root cyclic)

/-- Equal evaluations at the computed finite formal shift imply equality of original normalized coefficient tables.

Both dimensions and the shift algebra are constructed from the actual source
lists. This reflects formal coefficient equality even for finite coefficient
rings, zero divisors and the zero ring; no field, root count or supplied basis
is assumed.
-/
theorem normalize_eq [DecidableEq K] (left right : DensePolynomial K) (agreement : Agreement left right) :
    left.normalize = right.normalize := by
  let dimension := Nat.max left.coeffs.length right.coeffs.length + 1
  let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
  have same : (Map.map (Cyclic.Element.scalar cyclic) left).eval (Cyclic.Element.root cyclic) =
      (Map.map (Cyclic.Element.scalar cyclic) right).eval (Cyclic.Element.root cyclic) := agreement
  apply DensePolynomial.normalize_eq_of_reverse_coefficients
  intro index
  by_cases bounded : index < dimension
  · let row : Fin dimension := ⟨index, bounded⟩
    exact (coefficient_readback cyclic rfl left row).symm.trans
      ((matrix_eq_at (congrArg Cyclic.Element.matrix same) row cyclic.origin).trans
        (coefficient_readback cyclic rfl right row))
  · have leftBound : left.coeffs.reverse.length ≤ index := by
      rw [Reverse.length_reverse]
      exact Nat.le_trans (Purelib.Data.Nat.Order.le_max_left left.coeffs.length right.coeffs.length)
        (Nat.le_trans (Nat.le_succ _) (Nat.le_of_not_lt bounded))
    have rightBound : right.coeffs.reverse.length ≤ index := by
      rw [Reverse.length_reverse]
      exact Nat.le_trans (Purelib.Data.Nat.Order.le_max_right left.coeffs.length right.coeffs.length)
        (Nat.le_trans (Nat.le_succ _) (Nat.le_of_not_lt bounded))
    rw [getD_eq_default_of_length_le _ _ _ leftBound, getD_eq_default_of_length_le _ _ _ rightBound]

end Reflection

end Purelib.Polynomial.Dense

end
