module
import Purelib.Data.Bool.Decide
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Substitution.Affine
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic

/-!
# Exact affine reparameterization of the finite Cauchy index

Affine substitution maps the actual signed Euclidean chain coefficient by
coefficient.  The endpoint evaluation lists therefore agree exactly.  The
result includes negative slopes, reversed intervals, zero coordinate
polynomials, common polynomial factors, and endpoint zeros.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Affine

open Purelib.Data.Rat
open Purelib.Polynomial

public section

open Purelib.Polynomial.Dense.Rational.Substitution.Affine (subst subst_isZero subst_degreeCount subst_remainder
  subst_neg subst_eval)

/-- Invertible affine substitution commutes with the fuelled signed remainder chain.

For every fixed fuel value, the substituted chain is the entrywise substitution of the original chain. -/
theorem signedRemainderChainFuel_affine (origin slope : Fraction.Rational) (nonzero : slope ≠ 0) :
    ∀ (fuel : Nat) (first second : Dense.Rational.Basic.CoordinatePolynomial),
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel (subst first origin slope) (subst second
        origin slope) =
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel first second).map (fun polynomial =>
          subst polynomial origin slope)
  | 0, _, _ => rfl
  | fuel + 1, first, second => by
      rewrite [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_succ,
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_succ,
        Dense.Rational.Substitution.Affine.subst_isZero second origin slope nonzero]
      by_cases secondZero : second.isZero = true
      · rewrite [if_pos secondZero, if_pos secondZero]
        exact Eq.refl _
      · rewrite [if_neg secondZero, if_neg secondZero]
        dsimp only
        rewrite [Dense.Rational.Substitution.Affine.subst_remainder first second origin slope nonzero,
          Dense.Rational.Substitution.Affine.subst_isZero
            (Dense.Basic.DensePolynomial.divMod first second).remainder origin slope nonzero]
        by_cases remainderZero :
            (Dense.Basic.DensePolynomial.divMod first second).remainder.isZero = true
        · rewrite [if_pos remainderZero, if_pos remainderZero]
          exact Eq.refl _
        · rewrite [if_neg remainderZero, if_neg remainderZero]
          change subst first origin slope ::
              Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel
                (subst second origin slope)
                (-subst (Dense.Basic.DensePolynomial.divMod first second).remainder origin slope) =
            subst first origin slope ::
              (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel second
                (-(Dense.Basic.DensePolynomial.divMod first second).remainder)).map
                  (fun polynomial => subst polynomial origin slope)
          rewrite [← Dense.Rational.Substitution.Affine.subst_neg]
          exact congrArg (List.cons (subst first origin slope))
            (signedRemainderChainFuel_affine origin slope nonzero fuel second
              (-(Dense.Basic.DensePolynomial.divMod first second).remainder))

/-- Invertible affine substitution acts entrywise on the signed remainder chain.

A nonzero slope preserves the degree-based fuel and each signed division remainder. -/
theorem signedRemainderChain_affine (first second : Dense.Rational.Basic.CoordinatePolynomial)
    (origin slope : Fraction.Rational) (nonzero : slope ≠ 0) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (subst first origin slope) (subst second origin
      slope) =
      (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain first second).map (fun polynomial => subst
        polynomial origin slope) := by
  unfold Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF
  rewrite [Dense.Rational.Substitution.Affine.subst_degreeCount second origin slope nonzero]
  exact Dense.Rational.SignedRemainder.Affine.signedRemainderChainFuel_affine origin slope nonzero _ first second
end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Affine
