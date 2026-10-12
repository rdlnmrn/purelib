module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Basic
public import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.BoundaryFactorization (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational (Factorization)
open Purelib.Polynomial.Dense.Rational.Bezout.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Rational.Squarefree (SquarefreeCertificate)

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational.Bezout

/-- Every displayed nonzero left factor of a squarefree coordinate
polynomial is squarefree.  The certificate is obtained by rearranging the
finite Bézout identity and the explicit derivative product rule. -/
def leftFactorSquarefree
    {p left right : CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate left := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * Dense.Derivative.derivative right
  let derivativeCoefficient := squarefree.right * right
  exact
    { left := leftCoefficient
      right := derivativeCoefficient
      identity := by
        intro point
        have valueIdentity := Factorization.eval_factorization factorization point
        have derivativeIdentity :=
          Factorization.eval_derivative_factorization factorization point
        have original := squarefree.identity point
        rw [valueIdentity, derivativeIdentity] at original
        rw [Dense.Derivative.eval_derivative_mul] at original
        dsimp only [leftCoefficient, derivativeCoefficient]
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
        calc
          1 = squarefree.left.eval point *
                (left.eval point * right.eval point) +
              squarefree.right.eval point *
                ((Dense.Derivative.derivative left).eval point *
                    right.eval point +
                  left.eval point *
                    (Dense.Derivative.derivative right).eval point) :=
            original
          _ = (squarefree.left.eval point * right.eval point +
                squarefree.right.eval point *
                  (Dense.Derivative.derivative right).eval point) *
                  left.eval point +
              (squarefree.right.eval point * right.eval point) *
                (Dense.Derivative.derivative left).eval point := by
            ring1 }

/-- The two nonzero displayed factors of a squarefree coordinate polynomial
are coprime. -/
def factorsCoprime
    {p left right : CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate left right := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * Dense.Derivative.derivative right
  let rightCoefficient :=
    squarefree.right * Dense.Derivative.derivative left
  exact
    { left := leftCoefficient
      right := rightCoefficient
      identity := by
        intro point
        have valueIdentity := Factorization.eval_factorization factorization point
        have derivativeIdentity :=
          Factorization.eval_derivative_factorization factorization point
        have original := squarefree.identity point
        rw [valueIdentity, derivativeIdentity] at original
        rw [Dense.Derivative.eval_derivative_mul] at original
        dsimp only [leftCoefficient, rightCoefficient]
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
        calc
          1 = squarefree.left.eval point *
                (left.eval point * right.eval point) +
              squarefree.right.eval point *
                ((Dense.Derivative.derivative left).eval point *
                    right.eval point +
                  left.eval point *
                    (Dense.Derivative.derivative right).eval point) :=
            original
          _ = (squarefree.left.eval point * right.eval point +
                squarefree.right.eval point *
                  (Dense.Derivative.derivative right).eval point) *
                  left.eval point +
              (squarefree.right.eval point *
                  (Dense.Derivative.derivative left).eval point) *
                right.eval point := by
            ring1 }

/-- Coprimality with a second polynomial descends to a displayed nonzero
left factor. -/
def coprimeLeftFactor
    {p q left right : CoefficientPolynomial}
    (coprime : CoprimeCertificate p q)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate left q := by
  let leftCoefficient := coprime.left * right
  exact
    { left := leftCoefficient
      right := coprime.right
      identity := by
        intro point
        have original := coprime.identity point
        rw [Factorization.eval_factorization factorization point] at original
        dsimp only [leftCoefficient]
        simp only [DensePolynomial.eval_mul]
        calc
          1 = coprime.left.eval point *
                (left.eval point * right.eval point) +
              coprime.right.eval point * q.eval point := original
          _ = (coprime.left.eval point * right.eval point) *
                left.eval point +
              coprime.right.eval point * q.eval point := by ring1 }

/-- Coprimality with a second polynomial descends to a displayed nonzero
right factor. -/
def coprimeRightFactor
    {p q left right : CoefficientPolynomial}
    (coprime : CoprimeCertificate p q)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    CoprimeCertificate right q :=
  coprimeLeftFactor coprime rightNonzero
    (Factorization.factorization_swap factorization)

/-- Every displayed nonzero right factor of a squarefree coordinate
polynomial is squarefree. -/
def rightFactorSquarefree
    {p left right : CoefficientPolynomial}
    (squarefree : SquarefreeCertificate p)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate right :=
  leftFactorSquarefree squarefree rightNonzero
    (Factorization.factorization_swap factorization)

/-- If one polynomial is coprime to each of two displayed factors, it is
coprime to their product. -/
def coprimeWithProduct
    {p left right product : CoefficientPolynomial}
    (leftCoprime :
      CoprimeCertificate p left)
    (rightCoprime :
      CoprimeCertificate p right)
    (factorization : Factorization product left right) :
    CoprimeCertificate p product := by
  let pCoefficient :=
    leftCoprime.left * rightCoprime.left * p +
      leftCoprime.left * rightCoprime.right * right +
      leftCoprime.right * rightCoprime.left * left
  let productCoefficient := leftCoprime.right * rightCoprime.right
  exact
    { left := pCoefficient
      right := productCoefficient
      identity := by
        intro point
        have leftIdentity := leftCoprime.identity point
        have rightIdentity := rightCoprime.identity point
        have productIdentity := Factorization.eval_factorization factorization point
        dsimp only [pCoefficient, productCoefficient]
        simp only [DensePolynomial.eval_add, DensePolynomial.eval_mul]
        calc
          1 = 1 * 1 := by ring1
          _ = (leftCoprime.left.eval point * p.eval point +
                leftCoprime.right.eval point * left.eval point) *
              (rightCoprime.left.eval point * p.eval point +
                rightCoprime.right.eval point * right.eval point) := by
            rw [← leftIdentity, ← rightIdentity]
          _ = ((leftCoprime.left.eval point *
                    rightCoprime.left.eval point * p.eval point +
                  leftCoprime.left.eval point *
                    rightCoprime.right.eval point * right.eval point) +
                leftCoprime.right.eval point *
                  rightCoprime.left.eval point * left.eval point) *
                p.eval point +
              (leftCoprime.right.eval point *
                  rightCoprime.right.eval point) *
                (left.eval point * right.eval point) := by ring1
          _ = ((leftCoprime.left.eval point *
                    rightCoprime.left.eval point * p.eval point +
                  leftCoprime.left.eval point *
                    rightCoprime.right.eval point * right.eval point) +
                leftCoprime.right.eval point *
                  rightCoprime.left.eval point * left.eval point) *
                p.eval point +
              (leftCoprime.right.eval point *
                  rightCoprime.right.eval point) * product.eval point := by
            rw [productIdentity] }
end Purelib.Polynomial.Dense.Rational.Bezout

end
