module

import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Indexed rational eliminants for axis-parallel coordinate lines

The retained vertical and horizontal rational polynomials have nonzero and
bounded-degree certificates. Their pointwise nonzero evaluations produce
finite Bézout data for the same Gaussian source polynomial and coordinate line.
The certificate retains the original polynomial and supplied degree bound.
-/

open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Elimination.Axis.Certificate

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

namespace AxisSafeCuts

@[expose] public section

set_option genInjectivity false in
/-- Retained vertical and horizontal eliminants with indexed finite Bézout certificates.

Each original rational eliminant is nonzero with degree at most the supplied
bound. Its nonzero evaluation at a displayed coordinate returns the retained
Bézout certificate for the corresponding source-polynomial axis line. -/
structure AxisEliminationCertificate
    (p : CoefficientPolynomial) (degreeBound : Nat) where
  /-- The retained rational eliminant for vertical coordinate lines. -/ vertical :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The retained rational eliminant for horizontal coordinate lines. -/ horizontal :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The vertical eliminant is nonzero. -/ vertical_nonzero : vertical.isZero = false
  /-- The horizontal eliminant is nonzero. -/ horizontal_nonzero : horizontal.isZero = false
  /-- The vertical eliminant degree fits the retained search bound. -/ vertical_degree : vertical.natDegree ≤
    degreeBound
  /-- The horizontal eliminant degree fits the retained search bound. -/ horizontal_degree : horizontal.natDegree ≤
    degreeBound
  /-- A nonzero vertical-eliminant value supplies an exact Bezout certificate for that line's two coordinate
    polynomials. -/ vertical_coprime : ∀ x : Fraction.Rational, vertical.eval x ≠ 0 →
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p x)
      (Dense.Gaussian.Path.Axis.verticalPathImag p x)
  /-- A nonzero horizontal-eliminant value supplies an exact Bezout certificate for that line's two coordinate
    polynomials. -/ horizontal_coprime : ∀ y : Fraction.Rational, horizontal.eval y ≠ 0 →
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.horizontalPathReal p y)
      (Dense.Gaussian.Path.Axis.horizontalPathImag p y)

constructive_injectivity AxisEliminationCertificate

/-- Replace both scalar eliminants by their certified cached values.

The supplied cached degree is certified equal to the original bound. Both
original coprimality callbacks remain attached to the same source polynomial;
only their nonzero premises follow the supplied scalar readback equality.
-/
def AxisEliminationCertificate.withEliminants
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (original : AxisEliminationCertificate p degreeBound)
    (saved : {value : Dense.Rational.Basic.CoordinatePolynomial ×
        Dense.Rational.Basic.CoordinatePolynomial × Nat //
      value = (original.vertical, original.horizontal, degreeBound)}) :
    AxisEliminationCertificate p saved.val.2.2 where
  vertical := saved.val.1
  horizontal := saved.val.2.1
  vertical_nonzero := by
    rewrite [congrArg Prod.fst saved.property]
    exact original.vertical_nonzero
  horizontal_nonzero := by
    rewrite [congrArg (fun entry => entry.2.1) saved.property]
    exact original.horizontal_nonzero
  vertical_degree := by
    have bound : saved.val.2.2 = degreeBound := congrArg (fun entry => entry.2.2) saved.property
    rewrite [bound, congrArg Prod.fst saved.property]
    exact original.vertical_degree
  horizontal_degree := by
    have bound : saved.val.2.2 = degreeBound := congrArg (fun entry => entry.2.2) saved.property
    rewrite [bound, congrArg (fun entry => entry.2.1) saved.property]
    exact original.horizontal_degree
  vertical_coprime x safe := original.vertical_coprime x (by
    have same : saved.val.1 = original.vertical := congrArg Prod.fst saved.property
    exact same ▸ safe)
  horizontal_coprime y safe := original.horizontal_coprime y (by
    have same : saved.val.2.1 = original.horizontal := congrArg (fun entry => entry.2.1) saved.property
    exact same ▸ safe)

/-- Certified eliminant replacement preserves the complete original certificate.

Equality retains the executable callbacks as well as both scalar polynomials.
-/
theorem AxisEliminationCertificate.withEliminants_eq
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (original : AxisEliminationCertificate p degreeBound)
    (saved : {value : Dense.Rational.Basic.CoordinatePolynomial ×
        Dense.Rational.Basic.CoordinatePolynomial × Nat //
      value = (original.vertical, original.horizontal, degreeBound)}) :
    ((show saved.val.2.2 = degreeBound from congrArg (fun entry => entry.2.2) saved.property) ▸
      original.withEliminants saved) = original := by
  rcases saved with ⟨value, same⟩
  cases same
  cases original
  rfl

end

public section

namespace AxisEliminationCertificate

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian

/-- An exact Gaussian root makes the retained vertical eliminant vanish at its real coordinate.

A nonzero eliminant value would supply the same original vertical-line
Bézout certificate. Both line-coordinate evaluations vanish at the supplied
root, contradicting that finite unit identity.
-/
theorem vertical_eval_eq_zero_of_root
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) (point : Canonical) (root : p.eval point = 0) :
    certificate.vertical.eval point.re = 0 := by
  have realZero : (Path.Axis.verticalPathReal p point.re).eval point.im = 0 := by
    unfold Path.Axis.verticalPathReal
    rewrite [Path.Components.eval_pathReal, Affine.Axis.line_vertical]
    change (p.eval point).re = 0
    exact congrArg (fun value : Canonical => value.re) root
  have imaginaryZero : (Path.Axis.verticalPathImag p point.re).eval point.im = 0 := by
    unfold Path.Axis.verticalPathImag
    rewrite [Path.Components.eval_pathImag, Affine.Axis.line_vertical]
    change (p.eval point).im = 0
    exact congrArg (fun value : Canonical => value.im) root
  by_cases zero : certificate.vertical.eval point.re = 0
  · exact zero
  · rcases (certificate.vertical_coprime point.re zero).eval_ne_zero point.im with real | imaginary
    · exact (real realZero).elim
    · exact (imaginary imaginaryZero).elim

/-- An exact Gaussian root makes the retained horizontal eliminant vanish at its imaginary coordinate.

The original horizontal-line certificate excludes two simultaneous zero
coordinate evaluations whenever its retained eliminant is nonzero. The
supplied root therefore forces that same eliminant value to be zero.
-/
theorem horizontal_eval_eq_zero_of_root
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) (point : Canonical) (root : p.eval point = 0) :
    certificate.horizontal.eval point.im = 0 := by
  have realZero : (Path.Axis.horizontalPathReal p point.im).eval point.re = 0 := by
    unfold Path.Axis.horizontalPathReal
    rewrite [Path.Components.eval_pathReal, Affine.Axis.line_horizontal]
    change (p.eval point).re = 0
    exact congrArg (fun value : Canonical => value.re) root
  have imaginaryZero : (Path.Axis.horizontalPathImag p point.im).eval point.re = 0 := by
    unfold Path.Axis.horizontalPathImag
    rewrite [Path.Components.eval_pathImag, Affine.Axis.line_horizontal]
    change (p.eval point).im = 0
    exact congrArg (fun value : Canonical => value.im) root
  by_cases zero : certificate.horizontal.eval point.im = 0
  · exact zero
  · rcases (certificate.horizontal_coprime point.im zero).eval_ne_zero point.re with real | imaginary
    · exact (real realZero).elim
    · exact (imaginary imaginaryZero).elim

end AxisEliminationCertificate

/-- Read the maximum actual degree from the two retained eliminant polynomials. -/
@[expose] def AxisEliminationCertificate.degree
    {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) : Nat :=
  max certificate.vertical.natDegree certificate.horizontal.natDegree

/-- Transport only the degree-bound index of the same complete elimination certificate. -/
@[expose] def AxisEliminationCertificate.castDegree
    {p : CoefficientPolynomial} {left right : Nat}
    (same : left = right) (certificate : AxisEliminationCertificate p left) : AxisEliminationCertificate p right := by
  cases same
  exact certificate

/-- Inverse degree transport retains the complete original elimination certificate. -/
theorem AxisEliminationCertificate.castDegree_inverse
    {p : CoefficientPolynomial} {left right : Nat}
    (same : left = right) (certificate : AxisEliminationCertificate p left) :
    (certificate.castDegree same).castDegree same.symm = certificate := by
  cases same
  rfl

end

end AxisSafeCuts

end Purelib.Polynomial.Elimination.Axis.Certificate
