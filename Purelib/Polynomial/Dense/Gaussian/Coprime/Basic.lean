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

The original completed Euclidean result and both scaled coefficient polynomials
are stored once. Their canonical result equality and scalar-unit readbacks refer
to the same original inputs. -/
public structure CoprimeCertificate (p q : GCD.CoefficientPolynomial) where
  /-- The retained original completed Euclidean computation. -/
  result : Purelib.Polynomial.Dense.GCD.BezoutResult p q
  /-- The stored result is the original public algorithm's actual output. -/
  result_eq : result = GCD.extendedGCD p q
  /-- The nonzero scalar returned as the computed gcd. -/ unit : GCD.Scalar
  /-- The retained gcd scalar is nonzero. -/ unit_ne_zero : unit ≠ 0
  /-- The original canonical Euclidean gcd is the retained constant polynomial. -/
  gcd_eq_constant : (GCD.extendedGCD p q).gcd = DensePolynomial.constant unit
  /-- The cached original left coefficient scaled by the retained unit inverse. -/
  left : DensePolynomial GCD.Scalar
  /-- The left coefficient consumes the same stored Euclidean result. -/
  left_eq : left = DensePolynomial.scale unit⁻¹ result.left
  /-- The cached original right coefficient scaled by the retained unit inverse. -/
  right : DensePolynomial GCD.Scalar
  /-- The right coefficient consumes the same stored Euclidean result. -/
  right_eq : right = DensePolynomial.scale unit⁻¹ result.right

constructive_injectivity CoprimeCertificate

namespace CoprimeCertificate

/-- The retained Euclidean result has the certificate's original constant gcd. -/
public theorem result_gcd_eq_constant {p q : GCD.CoefficientPolynomial}
    (certificate : CoprimeCertificate p q) :
    certificate.result.gcd = DensePolynomial.constant certificate.unit :=
  (congrArg (fun result : Purelib.Polynomial.Dense.GCD.BezoutResult p q => result.gcd)
    certificate.result_eq).trans certificate.gcd_eq_constant

/-- The same original polynomial inputs determine the complete retained canonical Euclidean certificate.

Both result equations identify the actual extended-Euclid cache. Its constant
gcd determines the displayed unit by evaluation at zero, and the retained
scaling equations then determine both coefficient caches. Arbitrary Bezout
witnesses are not identified by this claim.
-/
public theorem eq_of_inputs {p q : GCD.CoefficientPolynomial}
    (left right : CoprimeCertificate p q) : left = right := by
  cases left with
  | mk result resultEq unit unitNonzero gcdEq leftCoefficient leftEq rightCoefficient rightEq =>
      cases right with
      | mk otherResult otherResultEq otherUnit otherUnitNonzero otherGcdEq
          otherLeft otherLeftEq otherRight otherRightEq =>
          cases resultEq
          cases otherResultEq
          have unitEq : unit = otherUnit :=
            (DensePolynomial.eval_constant unit 0).symm.trans
              ((congrArg (fun polynomial => polynomial.eval 0) (gcdEq.symm.trans otherGcdEq)).trans
                (DensePolynomial.eval_constant otherUnit 0))
          cases unitEq
          cases leftEq
          cases otherLeftEq
          cases rightEq
          cases otherRightEq
          rfl

/-- The normalized finite Bézout identity.

The retained nonzero unit rescales the completed original Euclidean identity. Both original ordered coefficient
polynomials evaluate at the same supplied Gaussian point. -/
public theorem identity {p q : GCD.CoefficientPolynomial}
    (certificate : CoprimeCertificate p q) (z : GCD.Scalar) :
    1 = certificate.left.eval z * p.eval z +
      certificate.right.eval z * q.eval z := by
  have raw := certificate.result.identity z
  rw [certificate.result_gcd_eq_constant, DensePolynomial.eval_constant] at raw
  calc
    1 = certificate.unit⁻¹ * certificate.unit := by
      rw [Gaussian.Basic.mul_comm]
      exact (ExplicitField.mul_inv_cancel certificate.unit
        certificate.unit_ne_zero).symm
    _ = certificate.unit⁻¹ *
        (certificate.result.left.eval z * p.eval z +
          certificate.result.right.eval z * q.eval z) := by
      rw [raw]
    _ = certificate.left.eval z * p.eval z +
        certificate.right.eval z * q.eval z := by
      rewrite [certificate.left_eq, certificate.right_eq, DensePolynomial.eval_scale, DensePolynomial.eval_scale]
      exact (Gaussian.Basic.left_distrib
        certificate.unit⁻¹
        (certificate.result.left.eval z * p.eval z)
        (certificate.result.right.eval z * q.eval z)).trans
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
