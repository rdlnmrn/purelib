module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Reciprocal
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Transport

import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Mathlib.Algebra.Group.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

@[expose] public section

/-!
# Admissibility of the actual finite reciprocal radicand

The exact polynomial already used in the reciprocal sample transport is a
squarefree hyperelliptic input of the same genus. An affine zero at the origin
changes the reciprocal degree from even to odd; it is not excluded by a new
assumption. The original degree parity separately determines whether the
reciprocal origin is regular or a simple branch.

This supplies the input to existing finite branch and local-cell machinery.
The reciprocal patch, overlap gluing, and global area comparison remain
separate geometric obligations.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve HyperellipticDegreeShape)
open Purelib.Polynomial.Dense.Basic.DensePolynomial

variable {genus : Nat}

/-- The exact reciprocal radicand is nonzero because reversal and the retained origin shift preserve nonvanishing. -/
theorem polynomial_nonzero (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    (HyperellipticReciprocal.polynomial curve).isZero = false :=
  Reciprocal.shifted_nonzero _
    (Reciprocal.reversed_nonzero curve.nonzero) _

/-- Squarefreeness is constructed for the exact existing reciprocal polynomial, not supplied by the caller or inferred
from a failed search. -/
def polynomialSquarefree (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial
      curve) := by
  let reverseFree := Reciprocal.reversedSquarefree curve.polynomial curve.nonzero curve.squarefree
  have reverseNonzero := Reciprocal.reversed_nonzero curve.nonzero
  cases shape : curve.degreeShape with
  | odd _ =>
      unfold Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder
      rw [shape]
      exact Coordinate.shiftOneSquarefree _ reverseNonzero reverseFree (HyperellipticReciprocal.origin_factor curve).1
  | even _ =>
      unfold Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder
      rw [shape]
      exact Transport.ofSameValues _ _
        (Reciprocal.shifted_nonzero _ reverseNonzero 0) reverseFree
        (by intro point; rw [eval_shift, pow_zero, Data.Gaussian.Basic.mul_one])

/-- The reciprocal degree is odd exactly in the affine simple-zero case; otherwise it is even. Both are the same
intrinsic genus. -/
def polynomialDegreeShape (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Hyperelliptic.Basic.HyperellipticDegreeShape (HyperellipticReciprocal.polynomial curve) genus := by
  have shifted : (HyperellipticReciprocal.polynomial curve).natDegree =
      (HyperellipticReciprocal.reversed curve.polynomial).natDegree + HyperellipticReciprocal.originOrder curve :=
    Reciprocal.shifted_degree _ (Reciprocal.reversed_nonzero curve.nonzero) _
  have balance := HyperellipticReciprocal.degree_balance curve
  if originZero : curve.polynomial.eval 0 = 0 then
    have derivativeNonzero : (GCD.derivative curve.polynomial).eval 0 ≠ 0 := by
      exact (curve.squarefree.eval_ne_zero 0).resolve_left (fun regular => regular originZero)
    have reversedDegree := Reciprocal.reversed_degree_simple
      curve.polynomial curve.nonzero originZero derivativeNonzero
    apply HyperellipticDegreeShape.odd
    change (HyperellipticReciprocal.reversed curve.polynomial).natDegree + 1 = curve.polynomial.natDegree
      at reversedDegree
    omega
  else
    have reversedDegree := Reciprocal.reversed_degree_regular
      curve.polynomial curve.nonzero originZero
    apply HyperellipticDegreeShape.even
    change (HyperellipticReciprocal.reversed curve.polynomial).natDegree = curve.polynomial.natDegree at reversedDegree
    omega

/-- The finite reciprocal chart is an admissible input to the same constructive curve machinery, with no extra affine
coefficient assumption. -/
def reciprocalCurve (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : Hyperelliptic.Basic.HyperellipticCurve
  genus where
  polynomial := HyperellipticReciprocal.polynomial curve
  nonzero := polynomial_nonzero curve
  squarefree := polynomialSquarefree curve
  degreeShape := polynomialDegreeShape curve

/-- The reconstructed reciprocal curve retains exactly the original reciprocal chart polynomial. -/
theorem reciprocalCurve_polynomial (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    (reciprocalCurve curve).polynomial =
      HyperellipticReciprocal.polynomial curve := rfl

/-- For origin order zero, the reciprocal radicand at zero is the original leading coefficient. -/
theorem origin_regular (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (regular :
  HyperellipticReciprocal.originOrder curve = 0) :
    (reciprocalCurve curve).polynomial.eval 0 =
      curve.polynomial.leadingCoeff := by
  rw [reciprocalCurve_polynomial,
    HyperellipticReciprocal.polynomial_eval, regular, pow_zero,
    Data.Gaussian.Basic.mul_one, Reciprocal.reversed_origin]

/-- For origin order one, the reciprocal origin is a simple root whose derivative is the original leading coefficient.
-/
theorem origin_simple (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (branch :
  HyperellipticReciprocal.originOrder curve = 1) :
    (reciprocalCurve curve).polynomial.eval 0 = 0 ∧
      (GCD.derivative (reciprocalCurve
        curve).polynomial).eval 0 = curve.polynomial.leadingCoeff := by
  constructor
  · rw [reciprocalCurve_polynomial,
      HyperellipticReciprocal.polynomial_eval, branch, pow_one,
      Data.Gaussian.Basic.mul_zero]
  · change (Derivative.derivative (DensePolynomial.shift (HyperellipticReciprocal.originOrder curve)
      (HyperellipticReciprocal.reversed curve.polynomial))).eval 0 = _
    rw [branch, Derivative.eval_derivative_shift_one,
      Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.zero_add,
      Reciprocal.reversed_origin]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
