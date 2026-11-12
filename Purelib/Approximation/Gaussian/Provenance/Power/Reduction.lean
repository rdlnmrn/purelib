module

public import Purelib.Approximation.Gaussian.Provenance.Power
public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Composition
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Nat.Division

/-!
# Operational quotient and remainder reduction of retained powers

The original generator remains fixed. Its supplied finite-power equation
reduces any natural exponent to an exact coefficient factor and a remainder
power, with a comparison valid at arbitrary original starting indices.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity

open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Reduce any exponent using the retained original generator's finite-power equation. -/
def reduce {generator : CoherentNamed} {degree : Nat} {parameter : Canonical}
    (identity : PowerIdentity generator degree parameter) (exponent : Nat) :
    NamedEquivalent (Coherent.Power.namedPower generator exponent).name
      (CoherentNamed.mul (Coherence.exact (parameter ^ (exponent / degree)))
        (Coherent.Power.namedPower generator (exponent % degree))).name := by
  let quotient := exponent / degree
  let remainder := exponent % degree
  have source_eq : Coherent.Power.namedPower generator (degree * quotient + remainder) =
      Coherent.Power.namedPower generator exponent :=
    congrArg (Coherent.Power.namedPower generator)
      ((Nat.add_comm _ _).trans (Purelib.Data.Nat.Division.mod_add_div exponent degree))
  let block := Coherent.Power.namedPower generator degree
  have wholePowers : NamedEquivalent (Coherent.Power.namedPower generator (degree * quotient)).name
      (Coherence.exact (parameter ^ quotient)).name :=
    NamedEquivalent.trans (Coherent.Power.namedPower_mul generator degree quotient)
      (NamedEquivalent.trans
        (Coherent.Power.namedPower_respects block (Coherence.exact parameter) identity quotient)
        (Coherent.Power.namedPower_exact parameter quotient))
  have comparison := NamedEquivalent.trans
    (Coherent.Power.namedPower_add generator (degree * quotient) remainder)
    (Product.Congruence.coherentMul_respects (Coherent.Power.namedPower generator (degree * quotient))
      (Coherence.exact (parameter ^ quotient)) (Coherent.Power.namedPower generator remainder)
      (Coherent.Power.namedPower generator remainder) wholePowers (NamedEquivalent.refl _))
  exact source_eq ▸ comparison

end Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity

end
