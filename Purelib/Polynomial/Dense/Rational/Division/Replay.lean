module

import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Division

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Replay of the original finite signed remainder chain

Saved quotients and remainders are untrusted witnesses. Coefficient identities
and strict degree descent identify each remainder with the original division
result, without executing long division during reload. The extra dependency
proves uniqueness on an explicit finite rational grid; it uses no infinite
root set or choice-derived witnesses.
-/

namespace Purelib.Polynomial.Dense.Rational.Division.Replay

open Purelib.Polynomial.Dense.Basic.DensePolynomial

set_option genInjectivity false in
/-- A supplied quotient and remainder for one rational polynomial division.

The record contains data only; the replay checker verifies normalization, strict remainder degree and the exact
coefficient identity. -/
structure Witness where
  /-- The supplied quotient polynomial. -/ quotient : Dense.Rational.Basic.CoordinatePolynomial
  /-- The supplied remainder polynomial. -/ remainder : Dense.Rational.Basic.CoordinatePolynomial

constructive_injectivity Witness

set_option genInjectivity false in
/-- A specific failed condition of a supplied division witness.

Each branch retains evidence of a normalization, degree or coefficient-identity failure for the original inputs and
witness. -/
inductive Invalid (p q : Dense.Rational.Basic.CoordinatePolynomial) (witness : Dense.Rational.Division.Replay.Witness)
  where
  /-- The supplied remainder is not normalized. -/ | normalization (failed : witness.remainder.normalize ≠
    witness.remainder)
  /-- The remainder coefficient count is not strictly below the divisor count. -/ | degree (failed : ¬
    witness.remainder.degreeCount < q.degreeCount)
  /-- The retained reconstructed polynomial differs from the normalized dividend. -/ | identity (actual :
    Dense.Rational.Basic.CoordinatePolynomial)
      (actual_eq : actual = witness.remainder + q * witness.quotient)
      (failed : actual ≠ p.normalize)

constructive_injectivity Invalid

set_option genInjectivity false in
/-- Retain the supplied data and the equality to the original remainder.
The quotient identity remains available independently of that equality. -/
structure Step (p q : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- The exact supplied or generated quotient and remainder. -/ witness : Dense.Rational.Division.Replay.Witness
  /-- The retained remainder equals the original long-division remainder. -/ equation : witness.remainder =
    (Dense.Basic.DensePolynomial.divMod p q).remainder
  /-- The retained remainder and quotient reconstruct the dividend at every rational point. -/ identity : ∀ point :
    Fraction.Rational,
    witness.remainder.eval point + q.eval point * witness.quotient.eval point = p.eval point

constructive_injectivity Step

/-- Check a supplied division witness without rerunning long division.

For a nonzero divisor, return either a specific failed condition or the retained witness certified to have the original
division remainder and evaluation identity. -/
def check (p q : Dense.Rational.Basic.CoordinatePolynomial) (nonzero : q.isZero = false) (witness :
  Dense.Rational.Division.Replay.Witness) :
    Except (Dense.Rational.Division.Replay.Invalid p q witness) (Dense.Rational.Division.Replay.Step p q) :=
  if normalized : witness.remainder.normalize = witness.remainder then
    if small : witness.remainder.degreeCount < q.degreeCount then
      let actual := witness.remainder + q * witness.quotient
      if same : actual = p.normalize then
        have identity : ∀ point : Fraction.Rational,
            witness.remainder.eval point + q.eval point * witness.quotient.eval point =
              p.eval point := by
          intro point
          have values := congrArg (fun polynomial : Dense.Rational.Basic.CoordinatePolynomial => polynomial.eval point)
            same
          simpa only [actual, Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_mul,
            Dense.Basic.DensePolynomial.eval_normalize] using values
        .ok ⟨witness, Dense.Rational.Division.remainder_unique p q
          witness.quotient witness.remainder nonzero normalized small identity, identity⟩
      else .error (.identity actual rfl same)
    else .error (.degree small)
  else .error (.normalization normalized)

/-- Fresh generation executes one division only. Its result is ready to save
before the next member is requested. -/
def generate (p q : Dense.Rational.Basic.CoordinatePolynomial) : Dense.Rational.Division.Replay.Step p q :=
  let result := Dense.Basic.DensePolynomial.divMod p q
  ⟨⟨result.quotient, result.remainder⟩, rfl, Dense.Basic.DensePolynomial.divMod_eval_equation p q⟩
end Purelib.Polynomial.Dense.Rational.Division.Replay

end

end
