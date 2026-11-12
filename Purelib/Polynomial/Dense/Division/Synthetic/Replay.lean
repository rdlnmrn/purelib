module

public import Purelib.Polynomial.Dense.Division.Synthetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked restoration of original synthetic division

A supplied descending quotient and scalar remainder reconstruct every original
coefficient. Structural inversion of the original synthetic recurrence proves
complete original-result agreement without executing that division on reload.
-/

namespace Purelib.Polynomial.Dense.Division.Synthetic.Replay

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*} [CommRing K]

/-- Reassembly inverts the complete original accumulator scan over a commutative ring. -/
private theorem syntheticAux_reassemble (root : K) (quotient : List K) (remainder : K) :
    syntheticAux root ((reassemble root quotient remainder).headD 0)
      (reassemble root quotient remainder).tail = (quotient, remainder) := by
  induction quotient with
  | nil => rfl
  | cons leading remaining previous =>
    change
      (leading :: (syntheticAux root
        (leading * root + ((reassemble root remaining remainder).headD 0 - leading * root))
        (reassemble root remaining remainder).tail).1,
      (syntheticAux root
        (leading * root + ((reassemble root remaining remainder).headD 0 - leading * root))
        (reassemble root remaining remainder).tail).2) = (leading :: remaining, remainder)
    have next : leading * root + ((reassemble root remaining remainder).headD 0 - leading * root) =
        (reassemble root remaining remainder).headD 0 := by ring0
    rewrite [next, previous]
    rfl

/-- Dividing a reassembled table recovers its same original complete quotient and remainder data. -/
private theorem divide_reassemble (root : K) (quotient : List K) (remainder : K) :
    ((divide (⟨reassemble root quotient remainder⟩ : DensePolynomial K) root).quotient.coeffs,
      (divide (⟨reassemble root quotient remainder⟩ : DensePolynomial K) root).remainder) = (quotient, remainder) := by
  cases quotient with
  | nil => rfl
  | cons leading remaining =>
    exact syntheticAux_reassemble root (leading :: remaining) remainder

set_option genInjectivity false in
/-- Supplied data for one original descending synthetic division. -/
public structure Witness (K : Type*) where
  /-- The supplied complete quotient coefficient table. -/ quotient : DensePolynomial K
  /-- The supplied scalar Horner remainder. -/ remainder : K

constructive_injectivity Witness

set_option genInjectivity false in
/-- A specific failed condition of the supplied original synthetic data.

The failure retains its original source, root and supplied witness. Empty
sources must have an empty quotient and zero remainder; nonempty sources must
reconstruct their original coefficient table literally.
-/
public inductive Invalid (polynomial : DensePolynomial K) (root : K) (witness : Witness K) where
  /-- The supplied quotient has the wrong original slot count. -/
  | length (failed : witness.quotient.coeffs.length ≠ polynomial.coeffs.length - 1)
  /-- An empty original source has been assigned a nonzero remainder. -/
  | emptyRemainder (empty : polynomial.coeffs = []) (failed : witness.remainder ≠ 0)
  /-- The retained reconstructed original table differs from the supplied source. -/
  | reconstruction (actual : List K) (actual_eq : actual = reassemble root witness.quotient.coeffs witness.remainder)
      (failed : actual ≠ polynomial.coeffs)

constructive_injectivity Invalid

/-- Exact original-result and supplied-data ownership of a restored synthetic result. -/
@[expose] public def Accepted (polynomial : DensePolynomial K) (root : K) (witness : Witness K)
    (result : Result polynomial root) : Prop :=
  result = divide polynomial root ∧ result.quotient = witness.quotient ∧ result.remainder = witness.remainder

/-- Complete original synthetic results agree whenever both retained numerical fields agree. -/
private theorem result_eq {polynomial : DensePolynomial K} {root : K}
    (left right : Result polynomial root) (quotient : left.quotient = right.quotient)
    (remainder : left.remainder = right.remainder) : left = right := by
  cases left
  cases right
  cases quotient
  cases remainder
  rfl

/-- Build the same original result from supplied fields and their exact original-data agreement. -/
@[expose] public def ofData {polynomial : DensePolynomial K} {root : K} (witness : Witness K)
    (quotientEq : witness.quotient = (divide polynomial root).quotient)
    (remainderEq : witness.remainder = (divide polynomial root).remainder) :
    {result : Result polynomial root // Accepted polynomial root witness result} :=
  let original := divide polynomial root
  let result : Result polynomial root :=
    { quotient := witness.quotient
      remainder := witness.remainder
      quotient_length := quotientEq.symm ▸ original.quotient_length
      coefficient_reconstruction := by
        rewrite [quotientEq, remainderEq]
        exact original.coefficient_reconstruction
      remainder_eval := remainderEq.trans original.remainder_eval
      eval_eq := by
        intro point
        rewrite [quotientEq, remainderEq]
        exact original.eval_eq point }
  ⟨result, by exact ⟨result_eq result original quotientEq remainderEq, rfl, rfl⟩⟩

/-- Check supplied synthetic data and retain either its complete original result or its specific violated condition.

The executable procedure checks the original slot count and literal
reassembled coefficients. The original division occurs only in erased
correctness statements, and is not rerun to check the supplied witness.
-/
@[expose] public def check [DecidableEq K] (polynomial : DensePolynomial K) (root : K) (witness : Witness K) :
    Except (Invalid polynomial root witness)
      {result : Result polynomial root // Accepted polynomial root witness result} :=
  if lengthEq : witness.quotient.coeffs.length = polynomial.coeffs.length - 1 then
    if empty : polynomial.coeffs = [] then
      if zero : witness.remainder = 0 then
        have quotientEmpty : witness.quotient.coeffs = [] := by
          have lengthZero := lengthEq
          rewrite [empty] at lengthZero
          cases values : witness.quotient.coeffs with
          | nil => rfl
          | cons leading remaining =>
            rewrite [values] at lengthZero
            exact False.elim (Nat.noConfusion lengthZero)
        have quotientEq : witness.quotient = (divide polynomial root).quotient := by
          cases polynomial with
          | mk coefficients =>
            cases empty
            cases witness with
            | mk quotient remainder =>
              cases quotient with
              | mk quotientCoeffs => cases quotientEmpty; rfl
        have remainderEq : witness.remainder = (divide polynomial root).remainder := by
          cases polynomial with
          | mk coefficients => cases empty; exact zero
        .ok (ofData witness quotientEq remainderEq)
      else .error (.emptyRemainder empty zero)
    else
      let actual := reassemble root witness.quotient.coeffs witness.remainder
      if same : actual = polynomial.coeffs then
        have polynomialEq : (⟨actual⟩ : DensePolynomial K) = polynomial := by
          cases polynomial
          exact congrArg DensePolynomial.mk same
        have data : ((divide polynomial root).quotient.coeffs, (divide polynomial root).remainder) =
            (witness.quotient.coeffs, witness.remainder) := by
          have original := divide_reassemble root witness.quotient.coeffs witness.remainder
          rewrite [polynomialEq] at original
          exact original
        have quotientEq : witness.quotient = (divide polynomial root).quotient := by
          have coeffs := (congrArg Prod.fst data).symm
          exact DensePolynomial.ext coeffs
        have remainderEq := (congrArg Prod.snd data).symm
        .ok (ofData witness quotientEq remainderEq)
      else .error (.reconstruction actual rfl same)
  else .error (.length lengthEq)

end Purelib.Polynomial.Dense.Division.Synthetic.Replay
