module

public import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

section
/-!
# Exact roots of finite dense linear polynomials

Degree-one polynomials over the explicit Gaussian field have an exact
Gaussian-rational root.  The construction below inspects only the normalized
two-element coefficient list and carries its evaluation certificate.
-/

@[expose] public section

namespace Purelib.Polynomial.Dense.Gaussian.Roots.Linear

set_option genInjectivity false in
/-- Finite coefficient data and the exact rational root of a degree-one
dense polynomial. -/
structure RootData (p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The nonzero leading coefficient in the normalized linear table. -/ leading : Gaussian.Basic.Canonical
  /-- The constant coefficient in the normalized linear table. -/ trailing : Gaussian.Basic.Canonical
  /-- The normalized polynomial has exactly the two retained coefficients. -/ normalizedCoeffs : p.normalize.coeffs =
    [leading, trailing]
  /-- The retained leading coefficient is nonzero. -/ leadingNonzero : leading ≠ 0
  /-- The computed exact Gaussian rational root. -/ point : Gaussian.Basic.Canonical
  /-- The root is minus the constant coefficient times the inverse leading coefficient. -/ point_eq : point = -(trailing
    * leading⁻¹)
  /-- The original polynomial vanishes at the retained point. -/ root : p.eval point = 0

constructive_injectivity RootData

/-- Compute the exact root from the normalized two-coefficient list. -/
def rootData {p :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degree :
  p.natDegree = 1) :
    RootData p := open Purelib.Algebra.Field in by
  have positive : 0 < p.natDegree := by
    rw [degree]
    decide
  have nonzero := Dense.Gaussian.Degree.Linear.isZero_false_of_natDegree_pos positive
  have count := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  rw [degree] at count
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change 1 + 1 = p.normalize.coeffs.length at count
      rw [coefficients] at count
      simp only [List.length_nil] at count
      exact False.elim ((by decide : (2 : Nat) ≠ 0) count)
  | cons leading tail =>
      cases tail with
      | nil =>
          change 1 + 1 = p.normalize.coeffs.length at count
          rw [coefficients] at count
          simp only [List.length_cons, List.length_nil] at count
          exact False.elim ((by decide : (2 : Nat) ≠ 1) count)
      | cons trailing rest =>
        cases rest with
        | nil =>
          have leadingNonzero : leading ≠ 0 := by
            have canonical := DensePolynomial.leadingCoeff_ne_zero nonzero
            change p.normalize.coeffs.headD 0 ≠ 0 at canonical
            rw [coefficients] at canonical
            simpa only [List.headD_cons] using canonical
          let point := -(trailing * leading⁻¹)
          have root : p.eval point = 0 := by
            rw [← DensePolynomial.eval_normalize p point]
            change DensePolynomial.evalCoeffs point p.normalize.coeffs = 0
            rw [coefficients]
            simp only [DensePolynomial.evalCoeffs, List.foldl_cons, List.foldl_nil,
              zero_mul, zero_add]
            dsimp only [point]
            have cancel : leading * leading⁻¹ = 1 :=
              ExplicitField.mul_inv_cancel leading leadingNonzero
            calc
              leading * -(trailing * leading⁻¹) + trailing =
                  -(leading * (trailing * leading⁻¹)) + trailing := by
                    rw [mul_neg]
              _ = -((leading * leading⁻¹) * trailing) + trailing := by
                    rw [Gaussian.Basic.mul_assoc,
                      Gaussian.Basic.mul_comm trailing,
                      ← Gaussian.Basic.mul_assoc]
              _ = -(1 * trailing) + trailing := by rw [cancel]
              _ = 0 := by
                rw [one_mul, neg_add_cancel]
          exact
            { leading := leading
              trailing := trailing
              normalizedCoeffs := coefficients
              leadingNonzero := leadingNonzero
              point := point
              point_eq := rfl
              root := root }
        | cons next remaining =>
          change 1 + 1 = p.normalize.coeffs.length at count
          have strict : 2 < p.normalize.coeffs.length := by
            rw [coefficients]
            simp only [List.length_cons]
            exact Nat.succ_lt_succ
              (Nat.succ_lt_succ (Nat.zero_lt_succ remaining.length))
          exact False.elim ((Nat.ne_of_lt strict) count)

end Purelib.Polynomial.Dense.Gaussian.Roots.Linear

end
