module

import Purelib.Polynomial.Multivariate.PowerReduction
import Purelib.Polynomial.Multivariate.Gaussian.PowerReduction
import Purelib.Polynomial.Multivariate.Sparse
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

/-!
# Arbitrary-degree reduction of retained polynomial coefficients

Quadratic and cubic equations invoke the same indexed reduction. Mixed-variable
checks preserve an unrelated opaque coordinate, and operational certificates
quantify over an arbitrary original generator carrying the supplied equation.
-/

namespace TestPurelib.Polynomial.MultivariatePowerReduction

open Purelib.Polynomial.Multivariate
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

/-- The degree-one monomial of the retained single generator. -/
private def x : Sparse Canonical 1 := Sparse.atom 0

/-- The difference-of-squares polynomial at its original generator. -/
private def differenceOfSquares : Sparse Canonical 1 :=
  Sparse.mul (Sparse.add x (Sparse.constant 1)) (Sparse.sub x (Sparse.constant 1))

example : (differenceOfSquares.reduceAt 0 2 2).terms =
    (Sparse.constant (1 : Canonical) : Sparse Canonical 1).terms := by
  decide

example : ((Sparse.sub (Sparse.pow x 3) (Sparse.constant 2)).reduceAt 0 3 2).terms = [] := by decide

example : ((Sparse.pow x 7).reduceAt 0 3 2).terms = (Sparse.mul (Sparse.constant 4) x).terms := by decide

example : ((Sparse.mul (Sparse.pow (Sparse.atom 0 : Sparse Canonical 2) 2) (Sparse.atom 1)).reduceAt 0 2 2).terms =
    (Sparse.mul (Sparse.constant 2) (Sparse.atom 1) : Sparse Canonical 2).terms := by decide

example (polynomial : Sparse Canonical 3) : Terms.ExponentBelow 1 3 (polynomial.reduceAt 1 3 2).terms :=
  polynomial.reduceAt_exponentBelow 1 3 2 (by decide)

example (generator : CoherentNamed) (relation : PowerIdentity generator 2 2) :
    RationalSidecar (differenceOfSquares.denote (fun _ => generator)) :=
  let source : Gaussian.Normalized (fun _ : Fin 1 => generator)
      (differenceOfSquares.denote (fun _ => generator)) :=
    Gaussian.Normalized.ofForm (fun _ => generator) differenceOfSquares
      (Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.refl _)
  let reduced := source.reduceAt 0 2 2 relation
  reduced.rational 1 (by
    change (differenceOfSquares.reduceAt 0 2 2).terms = _
    decide)

end TestPurelib.Polynomial.MultivariatePowerReduction
