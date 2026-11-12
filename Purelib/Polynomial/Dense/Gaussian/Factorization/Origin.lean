module

public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Reverse
import Purelib.Data.List.Fold
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Retained coordinate-power factorization at the origin -/

namespace Purelib.Polynomial.Dense.Gaussian.Factorization.Origin

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

set_option genInjectivity false in
/-- The exact retained prefix scan of one ascending coefficient table. -/
private structure Prefix (coefficients : List Canonical) where
  /-- The computed number of initial zero coefficients. -/ order : Nat
  /-- The actual remaining ascending coefficient table. -/ remaining : List Canonical
  /-- These retained tables reconstruct the original ordered coefficients. -/
  same : coefficients = List.replicate order 0 ++ remaining
  /-- The scan ends at the original empty table or its first nonzero coefficient. -/
  final : remaining = [] ∨ remaining.headD 0 ≠ 0

/-- Remove exactly the original ascending zero prefix by structural recursion. -/
private def scan : (coefficients : List Canonical) → Prefix coefficients
  | [] => ⟨0, [], rfl, Or.inl rfl⟩
  | coefficient :: remaining =>
      if zero : coefficient = 0 then
        let tail := scan remaining
        ⟨tail.order + 1, tail.remaining, by
          change coefficient :: remaining = 0 :: (List.replicate tail.order 0 ++ tail.remaining)
          rw [zero]
          exact congrArg (List.cons (0 : Canonical)) tail.same, tail.final⟩
      else ⟨0, coefficient :: remaining, rfl, Or.inr zero⟩

/-- Evaluation at zero reads the first coefficient of the original reversed table. -/
private theorem reversed_origin (coefficients : List Canonical) :
    DensePolynomial.evalCoeffs 0 coefficients.reverse = coefficients.headD 0 := by
  cases coefficients with
  | nil => rfl
  | cons coefficient remaining =>
      rw [Reverse.reverse_cons]
      unfold DensePolynomial.evalCoeffs
      rw [Fold.foldl_append, List.foldl_cons, List.foldl_nil,
        Gaussian.Basic.mul_zero, Gaussian.Basic.zero_add]
      rfl

public section

set_option genInjectivity false in
/-- The original polynomial's coordinate power and retained nonzero-origin cofactor.

Its exact normalized coefficient table is reconstructed by appending the
computed zero suffix to that same retained cofactor table. No root set or
successful division producer is supplied to this finite construction.
-/
structure Decomposition (polynomial : CoefficientPolynomial) where
  /-- The computed multiplicity of the coordinate in the original normalized table. -/ order : Nat
  /-- The retained original cofactor after removing only that same zero suffix. -/ cofactor : CoefficientPolynomial
  /-- Both retained tables reconstruct the exact original normalized coefficients. -/
  coefficients_eq : polynomial.normalize.coeffs = cofactor.coeffs ++ List.replicate order 0
  /-- The retained cofactor's exact origin evaluation is nonzero. -/ originNonzero : cofactor.eval 0 ≠ 0

constructive_injectivity Decomposition

/-- Compute the coordinate-power factorization of any original nonzero Gaussian polynomial.

The normalized table is reversed once, and a finite prefix scan retains its
actual zero count and remainder. Nonzero leading data excludes an empty
remainder, whose first original coefficient is the cofactor's constant term.
-/
def prepare (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) :
    Decomposition polynomial := by
  let retained := scan polynomial.normalize.coeffs.reverse
  let cofactor : CoefficientPolynomial := ⟨retained.remaining.reverse⟩
  have coefficients : polynomial.normalize.coeffs = cofactor.coeffs ++ List.replicate retained.order 0 := by
    have reversed := congrArg List.reverse retained.same
    rw [Reverse.reverse_reverse, Reverse.reverse_append, Reverse.reverse_replicate] at reversed
    exact reversed
  have remainingNonempty : retained.remaining ≠ [] := by
    intro empty
    have allZero := coefficients
    change polynomial.normalize.coeffs = retained.remaining.reverse ++ List.replicate retained.order 0 at allZero
    rw [empty, List.reverse_nil, List.nil_append] at allZero
    have leadingZero : polynomial.leadingCoeff = 0 := by
      change polynomial.normalize.coeffs.headD 0 = 0
      rw [allZero]
      cases retained.order <;> rfl
    exact DensePolynomial.leadingCoeff_ne_zero nonzero leadingZero
  have originNonzero : cofactor.eval 0 ≠ 0 := by
    have final := retained.final
    cases final with
    | inl empty => exact (remainingNonempty empty).elim
    | inr nonzero =>
        change DensePolynomial.evalCoeffs 0 retained.remaining.reverse ≠ 0
        rw [reversed_origin]
        exact nonzero
  exact ⟨retained.order, cofactor, coefficients, originNonzero⟩

/-- The retained coordinate power and cofactor give the original polynomial's exact evaluation at every point. -/
theorem Decomposition.eval {polynomial : CoefficientPolynomial} (factorization : Decomposition polynomial)
    (point : Canonical) :
    polynomial.eval point = factorization.cofactor.eval point * point ^ factorization.order := by
  rw [← DensePolynomial.eval_normalize polynomial point]
  change DensePolynomial.evalCoeffs point polynomial.normalize.coeffs = _
  rw [factorization.coefficients_eq, DensePolynomial.evalCoeffs_append_replicate_zero]
  rfl

end

end Purelib.Polynomial.Dense.Gaussian.Factorization.Origin
