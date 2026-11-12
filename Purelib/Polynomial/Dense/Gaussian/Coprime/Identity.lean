module

public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Polynomial.Dense.Gaussian.Extensionality

/-!
# Original Gaussian Bezout identities in coefficient algebras

The retained original cofactors give a literal coefficient identity by the
original finite Gaussian probe theorem. Injective coefficient maps transport
that same identity to arbitrary commutative rings, including rings with zero
divisors. A root of one input therefore supplies an explicit unit value of
the other input without a field assumption on the target.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Basic.CoprimeCertificate

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense
open Purelib.Data.Gaussian.Basic (Canonical)

variable {first second : GCD.CoefficientPolynomial}

/-- The retained original Gaussian cofactors give the literal normalized coefficient unit identity. -/
theorem polynomial_identity (certificate : CoprimeCertificate first second) :
    DensePolynomial.constant 1 = certificate.left * first + certificate.right * second := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq
  · exact DensePolynomial.normalize_constant_of_ne (by decide +kernel : (1 : Canonical) ≠ 0)
  · exact DensePolynomial.normalize_add _ _
  · intro point
    rewrite [DensePolynomial.eval_constant, DensePolynomial.eval_add,
      DensePolynomial.eval_mul, DensePolynomial.eval_mul]
    exact certificate.identity point

variable {L : Type*} [CommRing L] [DecidableEq L]

/-- The same coefficient identity holds at every target point after an injective ring coefficient map. -/
theorem mapped_identity (certificate : CoprimeCertificate first second)
    (function : Canonical → L) (mapZero : function 0 = 0) (injective : Function.Injective function)
    (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right) (point : L) :
    1 = (Map.map function certificate.left).eval point * (Map.map function first).eval point +
      (Map.map function certificate.right).eval point * (Map.map function second).eval point := by
  have mapped := congrArg (Map.map function) certificate.polynomial_identity
  rewrite [Map.map_constant, mapOne, Map.map_add function mapZero injective mapAdd,
    Map.map_mul function mapZero injective mapAdd mapMul,
    Map.map_mul function mapZero injective mapAdd mapMul] at mapped
  have evaluated := congrArg (fun polynomial : DensePolynomial L => polynomial.eval point) mapped
  rewrite [DensePolynomial.eval_constant, DensePolynomial.eval_add,
    DensePolynomial.eval_mul, DensePolynomial.eval_mul] at evaluated
  exact evaluated

/-- At a root of the first mapped input, the cached right cofactor explicitly inverts the second input value. -/
theorem right_unit (certificate : CoprimeCertificate first second)
    (function : Canonical → L) (mapZero : function 0 = 0) (injective : Function.Injective function)
    (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right) (point : L)
    (vanishes : (Map.map function first).eval point = 0) :
    (Map.map function second).eval point * (Map.map function certificate.right).eval point = 1 := by
  have retained := certificate.mapped_identity function mapZero injective mapOne mapAdd mapMul point
  rewrite [vanishes, mul_zero, zero_add] at retained
  exact (mul_comm _ _).trans retained.symm

end Purelib.Polynomial.Dense.Gaussian.Coprime.Basic.CoprimeCertificate

end
