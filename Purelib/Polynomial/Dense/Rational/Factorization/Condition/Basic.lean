module

import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Dense.Rational.Bezout.Factor
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Dense.Rational.Factorization

set_option genInjectivity false in
/-- How one squarefree factor meets one displayed condition polynomial.
The equality branch retains the explicit finite cofactor identity, from which
root equality and quantitative near-root bounds can both be recovered; the
apart branch retains explicit finite Bézout separation. -/
inductive ConditionRelation (condition : BoundaryFactorization.CoefficientPolynomial) (factor :
  Dense.Rational.Squarefree.Factor) where
  /-- Retain an exact cofactor proving that the squarefree factor divides the condition polynomial. -/ | equality
    (cofactor : BoundaryFactorization.CoefficientPolynomial)
      (factorization : Factorization condition factor.polynomial cofactor)
  /-- Retain a finite Bezout certificate separating the squarefree factor from the condition polynomial. -/ | apart
    (coprime :
      Dense.Rational.Bezout.Basic.CoprimeCertificate
        factor.polynomial condition)

constructive_injectivity ConditionRelation

set_option genInjectivity false in
/-- One squarefree piece produced by splitting a source factor against a
condition.  Its displayed cofactor lets earlier condition certificates descend
through later splits. -/
structure ConditionPiece (source : Dense.Rational.Squarefree.Factor) (condition :
  BoundaryFactorization.CoefficientPolynomial) where
  /-- The squarefree factor retained by this piece. -/ factor : Dense.Rational.Squarefree.Factor
  /-- The displayed cofactor complementing this piece inside the original source factor. -/ cofactor :
    BoundaryFactorization.CoefficientPolynomial
  /-- The piece and retained cofactor multiply to the source polynomial. -/ factorization :
    Factorization source.polynomial factor.polynomial cofactor
  /-- The retained divisibility or Bezout separation relation to the displayed condition. -/ relation :
    Dense.Rational.Factorization.ConditionRelation condition factor

constructive_injectivity ConditionPiece

set_option genInjectivity false in
/-- Finite root-exact partition of one squarefree factor against one
condition polynomial.  Executable gcd yields at most two pieces. -/
structure ConditionPartition (factor : Dense.Rational.Squarefree.Factor) (condition :
  BoundaryFactorization.CoefficientPolynomial) where
  /-- The finite list of certified pieces of the original factor. -/ pieces : List
    (Dense.Rational.Factorization.ConditionPiece factor condition)
  /-- At least one certified piece is retained. -/ nonempty : pieces ≠ []
  /-- A rational point is a root of the source exactly when it is a root of a retained piece. -/ rootCoverage : ∀ point
    : Fraction.Rational,
    factor.polynomial.eval point = 0 ↔
      ∃ piece ∈ pieces, piece.factor.polynomial.eval point = 0

constructive_injectivity ConditionPartition

/-- A relation already known for the source factor descends through any
later displayed factor piece. -/
def ConditionRelation.descend
    {source : Dense.Rational.Squarefree.Factor} {condition nextCondition : BoundaryFactorization.CoefficientPolynomial}
  (relation : Dense.Rational.Factorization.ConditionRelation condition source)
  (piece : Dense.Rational.Factorization.ConditionPiece source nextCondition) :
  Dense.Rational.Factorization.ConditionRelation condition piece.factor := by
  cases relation with
  | equality cofactor factorization =>
      exact .equality (piece.cofactor * cofactor) (by
        apply Dense.Rational.Factorization.factorizationOfEvals
        intro point
        rw [Dense.Rational.Factorization.eval_factorization factorization point,
          Dense.Rational.Factorization.eval_factorization piece.factorization point,
            Dense.Basic.DensePolynomial.eval_mul]
        ring1)
  | apart coprime =>
      exact .apart
        (Dense.Rational.Bezout.coprimeLeftFactor coprime piece.factor.nonzero piece.factorization)
end Purelib.Polynomial.Dense.Rational.Factorization

end

end
