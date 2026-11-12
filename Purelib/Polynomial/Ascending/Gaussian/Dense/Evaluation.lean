module

public import Purelib.Data.Vector.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.List.Reverse
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Polynomial.Ascending.Gaussian.Coefficient
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Fold
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite antiderivatives of dense Gaussian polynomials

Connect the existing low-to-high polynomial integrator to the dense
high-to-low polynomial algebra.  The derivative identity is proved by finite
Horner induction.  The existing finite Taylor estimate then bounds local
primitive increments, without analytic limits or infinite series.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_mul_left sumFin_congr)

/-- Convert an ascending Gaussian coefficient table to the descending dense representation by reversal. -/
def toDense (polynomial :
  CoefficientPolynomial) : (DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨polynomial.coefficients.reverse⟩

/-- Reversing the coefficient representation preserves the Gaussian polynomial value. -/
theorem toDense_eval (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (toDense polynomial).eval point = Evaluation.eval polynomial
      point := open Purelib in by
  unfold toDense DensePolynomial.eval
    DensePolynomial.evalCoeffs
  rw [Data.List.Fold.foldl_reverse]
  unfold Evaluation.eval Evaluation.evalCoeffs
  induction polynomial.coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldr_cons, inductionHypothesis]
      ring1

/-- Convert the original descending dense table to ascending order without normalization. -/
def fromDense (polynomial : DensePolynomial Gaussian.Basic.Canonical) : CoefficientPolynomial :=
  ⟨polynomial.coeffs.reverse⟩

/-- Converting the same dense table to ascending order and back preserves every original coefficient. -/
theorem toDense_fromDense (polynomial : DensePolynomial Gaussian.Basic.Canonical) :
    toDense (fromDense polynomial) = polynomial :=
  DensePolynomial.ext (Reverse.reverse_reverse polynomial.coeffs)

/-- Converting the same ascending table to dense order and back preserves every original coefficient. -/
theorem fromDense_toDense (polynomial : CoefficientPolynomial) : fromDense (toDense polynomial) = polynomial :=
  congrArg CoefficientPolynomial.mk (Reverse.reverse_reverse polynomial.coefficients)

/-- The retained inverse representation conversion preserves evaluation at the same Gaussian point. -/
theorem fromDense_eval (polynomial : DensePolynomial Gaussian.Basic.Canonical)
    (point : Gaussian.Basic.Canonical) : Evaluation.eval (fromDense polynomial) point = polynomial.eval point := by
  have same := toDense_eval (fromDense polynomial) point
  rewrite [toDense_fromDense] at same
  exact same.symm

/-- Compute the value and derivative of an ascending Gaussian table in one finite Horner fold.

The first state component is the value and the second is the derivative value at the same supplied point. -/
public def jet (coefficients : List
  Gaussian.Basic.Canonical) (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical :=
  coefficients.foldr (fun coefficient state =>
    (state.1 * point + coefficient, state.2 * point + state.1)) (0, 0)

/-- The empty table has value-and-derivative state `(0, 0)`. -/
public theorem jet_nil (point : Gaussian.Basic.Canonical)
  : jet [] point = (0, 0) := rfl

/-- Extend the Gaussian Horner state by one coefficient.

The value becomes the tail value times the point plus the coefficient; the derivative becomes the tail derivative times
the point plus the tail value. -/
public theorem jet_cons (coefficient :
  Gaussian.Basic.Canonical) (remaining : List Gaussian.Basic.Canonical) (point : Gaussian.Basic.Canonical) :
    jet (coefficient :: remaining) point =
      ((jet remaining point).1 * point + coefficient,
        (jet remaining point).2 * point + (jet
          remaining point).1) := rfl

/-- The derivative value in the descending dense representation is the second component of the ascending Horner state.
-/
public theorem toDense_derivative_eval (polynomial :
  CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative (toDense polynomial)).eval point =
      (jet polynomial.coefficients point).2 := open Purelib in by
  unfold Dense.Gaussian.GCD.derivative
  rw [Dense.Derivative.eval_derivative]
  unfold Dense.Derivative.evalDerivativeCoeffs toDense
  rw [Data.List.Fold.foldl_reverse]
  rfl

/-- Materialize the same structural vector entries as an ascending finite coefficient table.

The traversal consumes the original stored heads and tails in order. It does
not build a second function-indexed container or discard retained zero entries.
-/
def fromVector : {count : Nat} → Data.Vector Gaussian.Basic.Canonical count → CoefficientPolynomial
  | _, .nil => ⟨[]⟩
  | _, .cons head tail => ⟨head :: (fromVector tail).coefficients⟩

/-- The coefficient table retains exactly the original structural vector length. -/
theorem fromVector_length {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count) :
    (fromVector values).coefficients.length = count := by
  induction values with
  | nil => rfl
  | cons head tail previous => exact congrArg Nat.succ previous

/-- Reading one bounded coefficient consumes the actual original vector entry. -/
theorem coefficient_fromVector {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count)
    (index : Fin count) : Coefficient.coefficient (fromVector values) index.val = values index := by
  induction values with
  | nil => exact Fin.elim0 index
  | @cons count head tail previous =>
      cases index with
      | mk index bound =>
          cases index with
          | zero => rfl
          | succ index => exact previous ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- The dense vector polynomial is the finite sum of its actual stored monomial coefficients. -/
theorem fromVector_eval_sum {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count)
    (point : Gaussian.Basic.Canonical) :
    (toDense (fromVector values)).eval point =
      sumFin (fun index => values index * point ^ index.val) := by
  induction values with
  | nil => rfl
  | @cons count head tail previous =>
      rewrite [toDense_eval]
      change head + point * Gaussian.Evaluation.eval (fromVector tail) point = _
      rewrite [← toDense_eval, previous, sumFin_succ]
      change head + point * sumFin (fun index => tail index * point ^ index.val) =
        head * point ^ 0 + sumFin
          (fun index => tail index * point ^ (index.val + 1))
      rewrite [pow_zero, Gaussian.Basic.mul_one]
      apply congrArg (fun value : Gaussian.Basic.Canonical => head + value)
      exact (sumFin_mul_left point _).symm.trans
        (sumFin_congr (fun index => by rewrite [pow_succ]; ring1))

/-- Read a bounded coefficient prefix into the original structural vector representation. -/
def toVector (count : Nat) (polynomial : CoefficientPolynomial) : Data.Vector Gaussian.Basic.Canonical count :=
  Data.Vector.Basic.vectorOfFn fun index => Coefficient.coefficient polynomial index.val

/-- Bounded coefficient readback returns the original zero-extended entry. -/
theorem toVector_apply (count : Nat) (polynomial : CoefficientPolynomial) (index : Fin count) :
    toVector count polynomial index = Coefficient.coefficient polynomial index.val :=
  Data.Vector.Basic.vectorOfFn_apply _ index

/-- Vector materialization and complete coefficient readback preserve the original stored vector. -/
theorem toVector_fromVector {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count) :
    toVector count (fromVector values) = values := by
  apply Data.Vector.Basic.vector_ext
  intro index
  exact (toVector_apply _ _ index).trans (coefficient_fromVector values index)

/-- A long enough bounded prefix retains every zero-extended coefficient of the supplied finite table. -/
theorem fromVector_toVector_coefficientwise (count : Nat) (polynomial : CoefficientPolynomial)
    (bound : polynomial.coefficients.length ≤ count) :
    Coefficient.CoefficientwiseEqual (fromVector (toVector count polynomial)) polynomial := by
  intro degree
  by_cases inside : degree < count
  · let index : Fin count := ⟨degree, inside⟩
    exact (coefficient_fromVector (toVector count polynomial) index).trans (toVector_apply _ _ index)
  · have outside : count ≤ degree := Nat.le_of_not_gt inside
    exact (Coefficient.coefficientList_eq_zero_of_length_le _ degree
      (by rewrite [fromVector_length]; exact outside)).trans
        (Coefficient.coefficientList_eq_zero_of_length_le _ degree (bound.trans outside)).symm

/-- Dense readback of a structural coefficient vector has at most its original number of slots. -/
theorem fromVector_degreeCount_le {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count) :
    (toDense (fromVector values)).degreeCount ≤ count := by
  apply (DensePolynomial.degreeCount_le_coeffs_length _).trans_eq
  change (fromVector values).coefficients.reverse.length = count
  rewrite [Reverse.length_reverse, fromVector_length]
  rfl

/-- Equal normalized dense readbacks identify the complete original structural coefficient vectors.

Both physical tables have the original same length. The original dense trim
comparison recovers every stored coefficient before the vector readback laws
identify the structural vectors.
-/
theorem fromVector_normalized_injective {count : Nat} {left right : Data.Vector Gaussian.Basic.Canonical count}
    (same : (toDense (fromVector left)).normalize = (toDense (fromVector right)).normalize) : left = right := by
  have length : (toDense (fromVector left)).coeffs.length = (toDense (fromVector right)).coeffs.length := by
    change (fromVector left).coefficients.reverse.length = (fromVector right).coefficients.reverse.length
    rewrite [Reverse.length_reverse, Reverse.length_reverse,
      fromVector_length, fromVector_length]
    rfl
  have denseSame := Dense.Extensionality.eq_of_normalize_eq_of_length_eq same length
  have ascendingSame : fromVector left = fromVector right := by
    have reverseSame := congrArg fromDense denseSame
    rewrite [fromDense_toDense, fromDense_toDense] at reverseSame
    exact reverseSame
  apply Data.Vector.Basic.vector_ext
  intro index
  exact (coefficient_fromVector left index).symm.trans
    ((congrArg (fun p : CoefficientPolynomial => Coefficient.coefficient p index.val) ascendingSame).trans
      (coefficient_fromVector right index))

/-- A zero dense readback has zero at every original zero-extended ascending coefficient. -/
theorem coefficient_zero_of_toDense_isZero (polynomial : CoefficientPolynomial)
    (zero : (toDense polynomial).isZero = true) (degree : Nat) : Coefficient.coefficient polynomial degree = 0 := by
  apply Coefficient.coefficientList_zero_of_all
  intro entry member
  exact Dense.Extensionality.coefficient_mem_eq_zero_of_isZero (toDense polynomial) zero entry
    ((Reverse.mem_reverse polynomial.coefficients).mpr member)

/-- Equal finite Horner values determine the original zero-extended coefficient tables through bounded probes.

The Gaussian coefficient-count probe construction certifies the original
polynomial difference as zero. Its exact coefficient readback then identifies
each supplied entry, including trailing zero padding; no infinite-carrier
argument or unguarded rational-function equality is used.
-/
theorem coefficientwise_of_eval_eq (left right : CoefficientPolynomial)
    (equal : ∀ point, Gaussian.Evaluation.eval left point =
      Gaussian.Evaluation.eval right point) : Coefficient.CoefficientwiseEqual left right := by
  let difference := Gaussian.Arithmetic.add left (Gaussian.Arithmetic.scale (-1) right)
  have zero : (toDense difference).isZero = true := by
    apply Dense.Gaussian.Extensionality.isZero_of_eval_eq_zero
    intro point
    rewrite [toDense_eval, Gaussian.Evaluation.eval_add,
      Gaussian.Evaluation.eval_scale, equal point]
    ring1
  intro degree
  have scalar := coefficient_zero_of_toDense_isZero difference zero degree
  change Coefficient.coefficient (Gaussian.Arithmetic.add left
    (Gaussian.Arithmetic.scale (-1) right)) degree = 0 at scalar
  rewrite [Gaussian.Arithmetic.coefficient_add, Gaussian.Arithmetic.coefficient_scale] at scalar
  calc
    Coefficient.coefficient left degree =
        (Coefficient.coefficient left degree + (-1) * Coefficient.coefficient right degree) +
          Coefficient.coefficient right degree := by ring1
    _ = _ := by rewrite [scalar, Gaussian.Basic.zero_add]; rfl

/-- Equality at nonzero Gaussian coordinates determines the original finite coefficient tables.

Multiplication by the local indeterminate adds the missing zero-coordinate
identity. The same bounded coefficient probes certify the shifted tables;
reading each successor coefficient recovers every original entry.
-/
theorem coefficientwise_of_eval_eq_at_nonzero (left right : CoefficientPolynomial)
    (equal : ∀ point, point ≠ 0 → Gaussian.Evaluation.eval left point =
      Gaussian.Evaluation.eval right point) : Coefficient.CoefficientwiseEqual left right := by
  have shifted := coefficientwise_of_eval_eq (Gaussian.Arithmetic.shift left)
    (Gaussian.Arithmetic.shift right) (fun point => by
      rewrite [Gaussian.Evaluation.eval_shift, Gaussian.Evaluation.eval_shift]
      by_cases zero : point = 0
      · cases zero
        rewrite [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_mul]
        rfl
      · rewrite [equal point zero]
        rfl)
  intro degree
  exact (Gaussian.Arithmetic.coefficient_shift_succ left degree).symm.trans
    ((shifted (degree + 1)).trans (Gaussian.Arithmetic.coefficient_shift_succ right degree))

/-- A zero dense vector polynomial has zero at every actual bounded vector entry. -/
theorem fromVector_zero {count : Nat} (values : Data.Vector Gaussian.Basic.Canonical count)
    (zero : (toDense (fromVector values)).isZero = true) (index : Fin count) : values index = 0 :=
  (coefficient_fromVector values index).symm.trans
    (coefficient_zero_of_toDense_isZero (fromVector values) zero index.val)

/-- A bounded prefix of the original normalized dense table reconstructs exactly that same normalized polynomial.

The coefficient bound determines sufficient zero padding. Pointwise finite
coefficient equality gives Horner equality, and the existing finite Gaussian
probe interface identifies the normalized dense records.
-/
theorem toVector_fromDense_normalized (count : Nat) (polynomial : DensePolynomial Gaussian.Basic.Canonical)
    (bound : polynomial.degreeCount ≤ count) :
    (toDense (fromVector (toVector count (fromDense polynomial.normalize)))).normalize = polynomial.normalize := by
  have length : (fromDense polynomial.normalize).coefficients.length ≤ count := by
    change polynomial.normalize.coeffs.reverse.length ≤ count
    rewrite [Reverse.length_reverse]
    exact bound
  apply Dense.Gaussian.Extensionality.gaussian_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (DensePolynomial.normalize_normalize _)
  intro point
  rewrite [DensePolynomial.eval_normalize, toDense_eval]
  exact (Gaussian.Evaluation.eval_eq_of_coefficientwise
    (fromVector_toVector_coefficientwise count (fromDense polynomial.normalize) length) point).trans
      (fromDense_eval polynomial.normalize point)

/-- A bounded original dense polynomial is the finite prefix of its normalized ascending coefficients.

The same retained coefficient bound pads the original table to the displayed
count. Its original vector readback reconstructs the normalized dense record;
ordered finite summation then evaluates precisely those coefficient entries.
-/
theorem eval_normalized_prefix (polynomial : DensePolynomial Gaussian.Basic.Canonical) (count : Nat)
    (bound : polynomial.degreeCount ≤ count) (point : Gaussian.Basic.Canonical) :
    polynomial.eval point = Purelib.Algebra.FiniteSum.Prefix.prefixSum count
      (fun degree => Coefficient.coefficient (fromDense polynomial.normalize) degree * point ^ degree) := by
  let values := toVector count (fromDense polynomial.normalize)
  have scalar := congrArg (fun value : DensePolynomial Gaussian.Basic.Canonical => value.eval point)
    (toVector_fromDense_normalized count polynomial bound)
  rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_normalize] at scalar
  calc
    polynomial.eval point = (toDense (fromVector values)).eval point := scalar.symm
    _ = sumFin (fun index => values index * point ^ index.val) := fromVector_eval_sum values point
    _ = sumFin (fun index : Fin count =>
        Coefficient.coefficient (fromDense polynomial.normalize) index.val * point ^ index.val) :=
      sumFin_congr (fun index => congrArg (fun coefficient => coefficient * point ^ index.val)
        (toVector_apply count (fromDense polynomial.normalize) index))
    _ = _ := Purelib.Algebra.FiniteSum.Prefix.sumFin_eq_prefixSum
      (K := Gaussian.Basic.Canonical) count
      (fun degree => Coefficient.coefficient (fromDense polynomial.normalize) degree * point ^ degree)

end Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation

end
