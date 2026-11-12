module

import Purelib.Polynomial.Dense.Division.Synthetic.Replay
import Purelib.Data.Gaussian.Field

/-!
# Original synthetic coefficient restoration regressions

Complete results are restored for an empty table, a constant and a cubic.
Independent bad-slot, empty-remainder and reconstruction failures retain their
specific failed conditions. No field or integral-domain assumption is needed.
-/

namespace TestPurelib.Polynomial.Dense.Division.Synthetic.Replay

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Division.Synthetic
open Purelib.Polynomial.Dense.Division.Synthetic.Replay

/-- Empty-source restoration retains the original empty quotient and zero remainder. -/
private theorem empty_restored :
    match check (⟨[]⟩ : DensePolynomial Canonical) 3 ⟨⟨[]⟩, 0⟩ with
    | .ok restored => restored.val.quotient.coeffs = [] ∧ restored.val.remainder = 0
    | .error _ => False := by
  change ([] : List Canonical) = [] ∧ (0 : Canonical) = 0
  exact ⟨rfl, rfl⟩

/-- Constant restoration retains the original scalar with no quotient slots. -/
private theorem constant_restored :
    match check (⟨[7]⟩ : DensePolynomial Canonical) 3 ⟨⟨[]⟩, 7⟩ with
    | .ok restored => restored.val.quotient.coeffs = [] ∧ restored.val.remainder = 7
    | .error _ => False := by
  change ([] : List Canonical) = [] ∧ (7 : Canonical) = 7
  exact ⟨rfl, rfl⟩

/-- The original cubic restores its same complete quotient and Horner scalar from literal reconstruction. -/
private theorem cubic_restored :
    match check (⟨[1, 2, 3, 4]⟩ : DensePolynomial Canonical) 2 ⟨⟨[1, 4, 11]⟩, 26⟩ with
    | .ok restored => restored.val.quotient.coeffs = [1, 4, 11] ∧ restored.val.remainder = 26
    | .error _ => False := by
  change ([1, 4, 11] : List Canonical) = [1, 4, 11] ∧ (26 : Canonical) = 26
  exact ⟨rfl, rfl⟩

/-- A wrong original quotient slot count produces its specific certified invalidity. -/
private theorem slots_rejected :
    match check (⟨[1, 2, 3]⟩ : DensePolynomial Canonical) 2 ⟨⟨[1]⟩, 11⟩ with
    | .error (.length _) => True
    | _ => False := by change True; exact True.intro

/-- An empty original source cannot accept a spurious nonzero scalar remainder. -/
private theorem empty_remainder_rejected :
    match check (⟨[]⟩ : DensePolynomial Canonical) 2 ⟨⟨[]⟩, 1⟩ with
    | .error (.emptyRemainder _ _) => True
    | _ => False := by change True; exact True.intro

/-- A numerically changed original coefficient is rejected with its retained reconstruction. -/
private theorem reconstruction_rejected :
    match check (⟨[1, 2, 3, 4]⟩ : DensePolynomial Canonical) 2 ⟨⟨[1, 4, 11]⟩, 25⟩ with
    | .error (.reconstruction _ _ _) => True
    | _ => False := by change True; exact True.intro

/-- Every restored result has complete original-procedure and supplied-data ownership over any commutative ring. -/
private theorem accepted_complete {K : Type*} [CommRing K]
    {polynomial : DensePolynomial K} {root : K} {witness : Witness K}
    (restored : {result : Result polynomial root // Accepted polynomial root witness result}) :
    restored.val = divide polynomial root ∧ restored.val.quotient = witness.quotient ∧
      restored.val.remainder = witness.remainder := restored.property

end TestPurelib.Polynomial.Dense.Division.Synthetic.Replay
