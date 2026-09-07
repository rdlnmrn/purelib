import FTA.LocalExtraction

/-!
# Constructive removal of an exact Gaussian zero factor

Dense Gaussian polynomials store coefficients from highest to lowest degree.
When the constant term vanishes, dropping the final normalized coefficient
therefore gives the exact quotient by `Z`.  This file proves the evaluation,
degree, derivative, and squarefreeness facts needed to treat zero as a
distinguished terminal root before running the nonzero CCL controller on the
remaining factor.
-/

namespace FTA
namespace GaussianZeroDeflation

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.GaussianDerivative
open FTA.LocalExtraction

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

/-- Exact dense quotient by `Z`, obtained by deleting the normalized
constant coefficient. -/
def quotient (p : GaussianPolynomial) : GaussianPolynomial :=
  ⟨p.normalize.coeffs.dropLast⟩

private theorem eval_zero_eq_getLast
    (p : GaussianPolynomial) (nonempty : p.normalize.coeffs ≠ []) :
    p.eval 0 = p.normalize.coeffs.getLast nonempty := by
  have split := List.dropLast_append_getLast nonempty
  calc
    p.eval 0 = evalCoeffs 0 p.normalize.coeffs := by
      exact (eval_normalize p 0).symm
    _ = evalCoeffs 0
        (p.normalize.coeffs.dropLast ++
          [p.normalize.coeffs.getLast nonempty]) := by
      exact congrArg (evalCoeffs 0) split.symm
    _ = p.normalize.coeffs.getLast nonempty := by
      simp [DensePolynomial.evalCoeffs, List.foldl_append]

theorem normalized_coeffs_eq_quotient_append_zero
    {p : GaussianPolynomial} (nonempty : p.normalize.coeffs ≠ [])
    (zero : p.eval 0 = 0) :
    p.normalize.coeffs = (quotient p).coeffs ++ [0] := by
  rw [quotient]
  conv_lhs => rw [← List.dropLast_append_getLast nonempty]
  rw [← eval_zero_eq_getLast p nonempty, zero]

/-- Pointwise factorization `p(z) = q(z)z`. -/
theorem eval_eq_quotient_mul
    {p : GaussianPolynomial} (nonempty : p.normalize.coeffs ≠ [])
    (zero : p.eval 0 = 0) (z : QI) :
    p.eval z = (quotient p).eval z * z := by
  have coefficients := normalized_coeffs_eq_quotient_append_zero nonempty zero
  calc
    p.eval z = evalCoeffs z p.normalize.coeffs := by
      exact (eval_normalize p z).symm
    _ = evalCoeffs z ((quotient p).coeffs ++ [0]) := by
      exact congrArg (evalCoeffs z) coefficients
    _ = (quotient p).eval z * z := by
      simp [DensePolynomial.eval, DensePolynomial.evalCoeffs,
        List.foldl_append]

theorem eval_eq_quotient_mul_of_nonzero
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) (z : QI) :
    p.eval z = (quotient p).eval z * z := by
  apply eval_eq_quotient_mul (zero := zero)
  simpa [DensePolynomial.isZero] using nonzero

theorem quotient_root_is_root
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) {z : QI}
    (root : (quotient p).eval z = 0) : p.eval z = 0 := by
  rw [eval_eq_quotient_mul_of_nonzero nonzero zero z, root, zero_mul]

/-- Sparse specification of the exact zero-factor decomposition. -/
theorem toPolynomial_eq_quotient_mul_X
    {p : GaussianPolynomial} (nonempty : p.normalize.coeffs ≠ [])
    (zero : p.eval 0 = 0) :
    p.toPolynomial = (quotient p).toPolynomial * Polynomial.X := by
  rw [← toPolynomial_normalize p, toPolynomial_eq_foldl_horner,
    normalized_coeffs_eq_quotient_append_zero nonempty zero,
    List.foldl_append, ← toPolynomial_eq_foldl_horner (quotient p)]
  simp

theorem quotient_isZero_false
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) :
    (quotient p).isZero = false := by
  have nonempty : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using nonzero
  have pPolynomialNonzero : p.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false nonzero
  have quotientPolynomialNonzero : (quotient p).toPolynomial ≠ 0 := by
    intro quotientZero
    apply pPolynomialNonzero
    rw [toPolynomial_eq_quotient_mul_X nonempty zero, quotientZero]
    simp
  cases quotientZero : (quotient p).isZero with
  | false => rfl
  | true =>
      exact (quotientPolynomialNonzero
        ((toPolynomial_eq_zero_iff_isZero (quotient p)).2 quotientZero)).elim

/-- Removing the exact zero factor lowers the natural degree by one. -/
theorem quotient_natDegree_add_one
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) :
    (quotient p).natDegree + 1 = p.natDegree := by
  have nonempty : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using nonzero
  have quotientNonzero := quotient_isZero_false nonzero zero
  have quotientPolynomialNonzero : (quotient p).toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false quotientNonzero
  have degrees := congrArg Polynomial.natDegree
    (toPolynomial_eq_quotient_mul_X nonempty zero)
  rw [Polynomial.natDegree_mul_X quotientPolynomialNonzero,
    natDegree_toPolynomial nonzero,
    natDegree_toPolynomial quotientNonzero] at degrees
  exact degrees.symm

theorem quotient_natDegree_pos
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (zero : p.eval 0 = 0) (degree : 1 < p.natDegree) :
    0 < (quotient p).natDegree := by
  have degreeEq := quotient_natDegree_add_one nonzero zero
  omega

/-- Product-rule form of the dense derivative after exact zero deflation. -/
theorem eval_derivative_eq
    {p : GaussianPolynomial} (nonempty : p.normalize.coeffs ≠ [])
    (zero : p.eval 0 = 0) (z : QI) :
    (derivative p).eval z =
      (quotient p).eval z + z * (derivative (quotient p)).eval z := by
  calc
    (derivative p).eval z =
        Polynomial.eval z p.toPolynomial.derivative :=
      eval_derivative p z
    _ = Polynomial.eval z
        ((quotient p).toPolynomial * Polynomial.X).derivative := by
      rw [toPolynomial_eq_quotient_mul_X nonempty zero]
    _ = (quotient p).eval z +
        z * (derivative (quotient p)).eval z := by
      rw [Polynomial.derivative_mul, Polynomial.derivative_X,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_one, eval_toPolynomial,
        ← eval_derivative]
      ring

/-- A squarefree polynomial with an exact zero factor has a squarefree
quotient.  If `U p + V p' = 1`, then
`(UZ + V)q + (VZ)q' = 1`. -/
def quotientSquarefreeCertificate
    {p : GaussianPolynomial} (certificate : GaussianSquarefreeCertificate p)
    (nonzero : p.isZero = false) (zero : p.eval 0 = 0) :
    GaussianSquarefreeCertificate (quotient p) where
  left := shift 1 certificate.left + certificate.right
  right := shift 1 certificate.right
  identity := by
    have nonempty : p.normalize.coeffs ≠ [] := by
      simpa [DensePolynomial.isZero] using nonzero
    have hfactor := toPolynomial_eq_quotient_mul_X nonempty zero
    have hderivative : (derivative p).toPolynomial =
        (quotient p).toPolynomial +
          Polynomial.X * (derivative (quotient p)).toPolynomial := by
      calc
        (derivative p).toPolynomial = p.toPolynomial.derivative :=
          toPolynomial_derivative p
        _ = ((quotient p).toPolynomial * Polynomial.X).derivative := by
          rw [hfactor]
        _ = (quotient p).toPolynomial +
            Polynomial.X * (derivative (quotient p)).toPolynomial := by
          rw [Polynomial.derivative_mul, Polynomial.derivative_X,
            ← toPolynomial_derivative]
          ring
    rw [toPolynomial_add, toPolynomial_shift, toPolynomial_shift, pow_one]
    calc
      (certificate.left.toPolynomial * Polynomial.X +
            certificate.right.toPolynomial) * (quotient p).toPolynomial +
          certificate.right.toPolynomial * Polynomial.X *
            (derivative (quotient p)).toPolynomial =
          certificate.left.toPolynomial * p.toPolynomial +
            certificate.right.toPolynomial * (derivative p).toPolynomial := by
        rw [hfactor, hderivative]
        ring
      _ = 1 := certificate.identity

/-- Squarefreeness rules out a second zero factor in the quotient. -/
theorem quotient_eval_zero_ne_zero
    {p : GaussianPolynomial} (certificate : GaussianSquarefreeCertificate p)
    (nonzero : p.isZero = false) (zero : p.eval 0 = 0) :
    (quotient p).eval 0 ≠ 0 := by
  have nonempty : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using nonzero
  intro quotientZero
  have derivativeZero : (derivative p).eval 0 = 0 := by
    rw [eval_derivative_eq nonempty zero 0, quotientZero]
    simp
  have bezout := certificate.bezout 0
  rw [zero, derivativeZero] at bezout
  simp only [mul_zero, add_zero] at bezout
  have impossible := congrArg CCL.GaussianRat.re bezout
  norm_num at impossible

end GaussianZeroDeflation
end FTA
