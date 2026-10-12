module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.GCD
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.GroupWithZero.NeZero
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coprimality certificates from the retained Euclidean unit

A nonzero original scalar certifies that the completed Gaussian Euclidean gcd
is its constant polynomial. Rescaling the same completed left and right Bezout
coefficients yields the retained unit identity at each supplied Gaussian point.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Basic

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data

set_option genInjectivity false in
/-- A finite certificate that two dense Gaussian polynomials are coprime.

The original nonzero unit and exact common-factor equality refer to the same completed Euclidean result on the two
original inputs. No coefficient or common-factor selection is replaced. -/
public structure CoprimeCertificate (p q : GCD.CoefficientPolynomial) where
  /-- The nonzero scalar returned as the computed gcd. -/ unit : GCD.Scalar
  /-- The retained gcd scalar is nonzero. -/ unit_ne_zero : unit ≠ 0
  /-- Executable extended Euclid returns exactly the retained constant polynomial. -/ gcd_eq_constant : (GCD.extendedGCD
    p q).gcd = DensePolynomial.constant unit

constructive_injectivity CoprimeCertificate

namespace CoprimeCertificate

/-- Scale the computed left Bezout coefficient by the inverse retained gcd unit.

The original Euclidean left coefficient and retained nonzero unit determine this exact scaled polynomial. The same
source inputs and scalar inverse are retained. -/
@[expose] public def left {p q : GCD.CoefficientPolynomial} (certificate : CoprimeCertificate p q) :
    (DensePolynomial GCD.Scalar) :=
  DensePolynomial.scale certificate.unit⁻¹ (GCD.extendedGCD p q).left

/-- Scale the computed right Bezout coefficient by the inverse retained gcd unit.

The original Euclidean right coefficient and retained nonzero unit determine this exact scaled polynomial. The same
source inputs and scalar inverse are retained. -/
@[expose] public def right {p q : GCD.CoefficientPolynomial} (certificate : CoprimeCertificate p q) :
    (DensePolynomial GCD.Scalar) :=
  DensePolynomial.scale certificate.unit⁻¹ (GCD.extendedGCD p q).right

/-- The normalized finite Bézout identity.

The retained nonzero unit rescales the completed original Euclidean identity. Both original ordered coefficient
polynomials evaluate at the same supplied Gaussian point. -/
public theorem identity {p q : GCD.CoefficientPolynomial}
    (certificate : CoprimeCertificate p q) (z : GCD.Scalar) :
    1 = certificate.left.eval z * p.eval z +
      certificate.right.eval z * q.eval z := by
  have raw := (GCD.extendedGCD p q).identity z
  rw [certificate.gcd_eq_constant, DensePolynomial.eval_constant] at raw
  calc
    1 = certificate.unit⁻¹ * certificate.unit := by
      rw [Gaussian.Basic.mul_comm]
      exact (ExplicitField.mul_inv_cancel certificate.unit
        certificate.unit_ne_zero).symm
    _ = certificate.unit⁻¹ *
        ((GCD.extendedGCD p q).left.eval z * p.eval z +
          (GCD.extendedGCD p q).right.eval z * q.eval z) := by
      rw [raw]
    _ = certificate.left.eval z * p.eval z +
        certificate.right.eval z * q.eval z := by
      simp only [left, right, DensePolynomial.eval_scale]
      exact (Gaussian.Basic.left_distrib
        certificate.unit⁻¹
        ((GCD.extendedGCD p q).left.eval z * p.eval z)
        ((GCD.extendedGCD p q).right.eval z * q.eval z)).trans
        (congrArg₂ (· + ·)
          (Gaussian.Basic.mul_assoc _ _ _).symm
          (Gaussian.Basic.mul_assoc _ _ _).symm)

/-- A retained coprimality certificate excludes a common Gaussian zero.

A zero value of the left input forces a nonzero value of the right input through the same retained unit identity. The
decision uses only the supplied scalar equality and original coefficient certificates. -/
public theorem eval_ne_zero {p q : GCD.CoefficientPolynomial}
    (certificate : CoprimeCertificate p q) (z : GCD.Scalar) :
    p.eval z ≠ 0 ∨ q.eval z ≠ 0 := by
  by_cases hp : p.eval z = 0
  · apply Or.inr
    intro hq
    have h := certificate.identity z
    simp only [hp, hq, mul_zero, zero_add] at h
    exact one_ne_zero h
  · exact Or.inl hp

end CoprimeCertificate

end Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
