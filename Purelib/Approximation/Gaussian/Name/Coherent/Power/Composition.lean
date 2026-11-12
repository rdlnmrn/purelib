module

public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Mathlib.Algebra.Group.Defs

/-!
# Composition and exact readback of finite coherent powers

Finite exponent products compose the actual coherent power constructors.
Exact coefficients retain their finite operational comparison to the exact
name of the corresponding scalar power.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Power

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The degree-two power compares to the product of the two original generator channels. -/
def namedPower_two (value : CoherentNamed) :
    NamedEquivalent (namedPower value 2).name (CoherentNamed.mul value value).name :=
  Product.Congruence.coherentMul_respects (namedPower value 1) value value value
    (namedPower_one value) (NamedEquivalent.refl _)

/-- Multiplication of finite exponents composes the powers of the original coherent channel. -/
def namedPower_mul (value : CoherentNamed) (first : Nat) : (second : Nat) →
    NamedEquivalent (namedPower value (first * second)).name (namedPower (namedPower value first) second).name
  | 0 => by
      rewrite [Nat.mul_zero]
      exact NamedEquivalent.refl _
  | second + 1 => by
      rewrite [Nat.mul_succ]
      exact NamedEquivalent.trans (namedPower_add value (first * second) first)
        (Product.Congruence.coherentMul_respects (namedPower value (first * second))
          (namedPower (namedPower value first) second) (namedPower value first) (namedPower value first)
          (namedPower_mul value first second) (NamedEquivalent.refl _))

/-- A finite power of an exact coefficient compares to its exact scalar power. -/
def namedPower_exact (value : Canonical) : (exponent : Nat) →
    NamedEquivalent (namedPower (Coherence.exact value) exponent).name (Coherence.exact (value ^ exponent)).name
  | 0 => by
      rewrite [pow_zero]
      exact NamedEquivalent.refl _
  | exponent + 1 => by
      rewrite [pow_succ]
      exact NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects (namedPower (Coherence.exact value) exponent)
          (Coherence.exact (value ^ exponent)) (Coherence.exact value) (Coherence.exact value)
          (namedPower_exact value exponent) (NamedEquivalent.refl _))
        (Exact.Arithmetic.exact_mul (value ^ exponent) value)

/-- A finite power of an original product compares to the product of the same two original factor powers.

The recursive comparison retains both input channels. Operational product
interchange accounts for their independently refined multiplication trees.
-/
def namedPower_product (first second : CoherentNamed) : (exponent : Nat) →
    NamedEquivalent (namedPower (first.mul second) exponent).name
      ((namedPower first exponent).mul (namedPower second exponent)).name
  | 0 => (Exact.Arithmetic.exact_mul 1 1).symm
  | exponent + 1 =>
      (Product.Congruence.coherentMul_respects
        (namedPower (first.mul second) exponent)
        ((namedPower first exponent).mul (namedPower second exponent))
        (first.mul second) (first.mul second) (namedPower_product first second exponent)
        (NamedEquivalent.refl _)).trans
          (Product.Laws.coherentMul_interchange (namedPower first exponent) (namedPower second exponent) first second)

end Purelib.Approximation.Gaussian.Name.Coherent.Power

end
