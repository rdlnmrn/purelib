module

import Purelib.Polynomial.Multivariate.Gaussian.PowerCoordinates.Pair
import Purelib.Polynomial.Multivariate.Gaussian.PowerReduction
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic

/-!
# General power coordinates and the original quadratic pair readback

Degree-three success and degree/support failures exercise the same finite
inspection. Pair checks read actual cached real coefficients; nonreal
coefficients remain explicit unresolved conditions rather than a numerical
claim about an opaque generator.
-/

namespace TestPurelib.Polynomial.MultivariatePowerCoordinates

open Purelib.Polynomial.Multivariate
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The original variable at the first position of a one-variable polynomial. -/
private def x : Sparse Canonical 1 := Sparse.atom 0

/-- The original degree-two coefficient list with constant, linear and quadratic terms. -/
private def quadratic : Sparse Canonical 1 :=
  Sparse.add (Sparse.add (Sparse.pow x 2) (Sparse.mul (Sparse.constant 3) x)) (Sparse.constant 5)

/-- Read success from the actual retained power-inspection outcome. -/
private def accepted {arity degree : Nat} {polynomial : Sparse Canonical arity} {index : Fin arity}
    (check : Sparse.PowerCheck polynomial index degree) : Bool :=
  match check.outcome with
  | .coordinates _ => true
  | .unresolved _ _ => false

example : accepted (quadratic.inspectPowers 0 3) = true := by decide
example : accepted (quadratic.inspectPowers 0 2) = false := by decide
example : accepted ((Sparse.mul (Sparse.atom 0) (Sparse.atom 1) : Sparse Canonical 2).inspectPowers 0 3) = false := by
  decide
example : accepted ((Sparse.zero : Sparse Canonical 1).inspectPowers 0 0) = true := by decide
example : accepted ((Sparse.constant 1 : Sparse Canonical 1).inspectPowers 0 0) = false := by decide

example : (quadratic.inspectPowers 0 3).polynomial = quadratic := rfl
example : (quadratic.inspectPowers 0 3).degree = 3 := rfl

/-- A cached arbitrary original generator polynomial with its reflexive source comparison. -/
private def retained (generator : CoherentNamed) (polynomial : Sparse Canonical 1) :
    Gaussian.Normalized (fun _ : Fin 1 => generator) (polynomial.denote (fun _ => generator)) :=
  Gaussian.Normalized.ofForm (fun _ => generator) polynomial (NamedEquivalent.refl _)

/-- The actual coordinate values returned by the pair checker, retaining failure as absence of this reading. -/
private def pairReading {parameter : Rational} : Option (Purelib.Algebra.Quadratic.Pair Rational parameter) →
    Option (Rational × Rational)
  | some value => some (value.re, value.im)
  | none => none

example (generator : CoherentNamed) :
    pairReading
      ((retained generator (Sparse.add (Sparse.constant 1) (Sparse.mul (Sparse.constant 2) x))).inspectPair
        0 2).value? =
      some (1, 2) := by
  rewrite [Gaussian.Normalized.inspectPair_value]
  change pairReading (Gaussian.Normalized.pairValue
    (Sparse.add (Sparse.constant 1) (Sparse.mul (Sparse.constant 2) x)) 0 2) = some (1, 2)
  cbv

example (generator : CoherentNamed) :
    pairReading ((retained generator (Sparse.constant (⟨0, 1⟩ : Canonical))).inspectPair 0 2).value? = none := by
  rewrite [Gaussian.Normalized.inspectPair_value]
  change pairReading (Gaussian.Normalized.pairValue (Sparse.constant (⟨0, 1⟩ : Canonical)) 0 2) = none
  cbv

end TestPurelib.Polynomial.MultivariatePowerCoordinates
