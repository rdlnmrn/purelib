import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ConstructivePolynomial

/-!
# Exact roots of finite dense linear polynomials

Degree-one polynomials over the explicit Gaussian field have an exact
Gaussian-rational root.  The construction below inspects only the normalized
two-element coefficient list and carries its evaluation certificate.
-/

namespace RFAP.Linear

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

/-- Finite coefficient data and the exact rational root of a degree-one
dense polynomial. -/
structure RootData (p : GaussianPolynomial) where
  leading : Gaussian
  trailing : Gaussian
  normalizedCoeffs : p.normalize.coeffs = [leading, trailing]
  leadingNonzero : leading ≠ 0
  point : Gaussian
  point_eq : point = -(trailing * leading⁻¹)
  root : p.eval point = 0

/-- A positive natural degree makes the normalized coefficient list
nonempty, without appealing to a carrier-level existence theorem. -/
theorem isZero_false_of_natDegree_pos
    {p : GaussianPolynomial} (positive : 0 < p.natDegree) :
    p.isZero = false := by
  cases zeroTest : p.isZero with
  | false => rfl
  | true =>
      have countZero : p.degreeCount = 0 :=
        degreeCount_eq_zero_of_isZero zeroTest
      have degreeZero : p.natDegree = 0 := by
        simp only [natDegree, countZero, Nat.zero_sub]
      rw [degreeZero] at positive
      exact (Nat.not_lt_zero 0 positive).elim

/-- Compute the exact root from the normalized two-coefficient list. -/
def rootData {p : GaussianPolynomial} (degree : p.natDegree = 1) :
    RootData p := by
  have positive : 0 < p.natDegree := by
    rw [degree]
    decide
  have nonzero := isZero_false_of_natDegree_pos positive
  have count := natDegree_add_one_eq_degreeCount nonzero
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
            have canonical := leadingCoeff_ne_zero nonzero
            change p.normalize.coeffs.headD 0 ≠ 0 at canonical
            rw [coefficients] at canonical
            simpa only [List.headD_cons] using canonical
          let point := -(trailing * leading⁻¹)
          have root : p.eval point = 0 := by
            rw [← eval_normalize p point]
            change evalCoeffs point p.normalize.coeffs = 0
            rw [coefficients]
            simp only [evalCoeffs, List.foldl_cons, List.foldl_nil,
              zero_mul, zero_add]
            dsimp only [point]
            have cancel : leading * leading⁻¹ = 1 :=
              RFAP.ExplicitField.mul_inv_cancel leading leadingNonzero
            calc
              leading * -(trailing * leading⁻¹) + trailing =
                  -(leading * (trailing * leading⁻¹)) + trailing := by
                    rw [mul_neg]
              _ = -((leading * leading⁻¹) * trailing) + trailing := by
                    rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
                      RFAP.ConstructiveGaussian.Gaussian.mul_comm trailing,
                      ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
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

end RFAP.Linear
