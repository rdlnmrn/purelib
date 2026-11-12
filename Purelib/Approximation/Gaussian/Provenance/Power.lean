module

public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Gaussian.Basic

/-!
# Retained equations for arbitrary finite powers

An equation compares a finite power of the original coherent generator with
an exact Gaussian coefficient. It is operational evidence at that generator,
not an equation asserted for each of its approximate readings.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Power

open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The retained original generator's finite power compares to the displayed exact Gaussian coefficient. -/
abbrev PowerIdentity (generator : CoherentNamed) (degree : Nat) (parameter : Canonical) :=
  NamedEquivalent (Coherent.Power.namedPower generator degree).name (Coherence.exact parameter).name

namespace PowerIdentity

/-- A retained product-square certificate gives the degree-two invocation of the general finite-power equation. -/
def ofSquare {generator : CoherentNamed} {parameter : Canonical}
    (square : NamedEquivalent (CoherentNamed.mul generator generator).name (Coherence.exact parameter).name) :
    PowerIdentity generator 2 parameter :=
  NamedEquivalent.trans
    (Product.Congruence.coherentMul_respects (Coherent.Power.namedPower generator 1) generator generator generator
      (Coherent.Power.namedPower_one generator) (NamedEquivalent.refl _)) square

/-- Transport an equation to an explicitly compared original generator without changing its degree or coefficient. -/
def transport {first second : CoherentNamed} {degree : Nat} {parameter : Canonical}
    (identity : PowerIdentity first degree parameter) (equivalent : NamedEquivalent second.name first.name) :
    PowerIdentity second degree parameter :=
  NamedEquivalent.trans (Coherent.Power.namedPower_respects second first equivalent degree) identity

/-- Multiply a retained finite-power equation by an additional power of the same original generator. -/
def shift {generator : CoherentNamed} {degree : Nat} {parameter : Canonical}
    (identity : PowerIdentity generator degree parameter) (exponent : Nat) :
    NamedEquivalent (Coherent.Power.namedPower generator (degree + exponent)).name
      (CoherentNamed.mul (Coherence.exact parameter) (Coherent.Power.namedPower generator exponent)).name :=
  NamedEquivalent.trans (Coherent.Power.namedPower_add generator degree exponent)
    (Product.Congruence.coherentMul_respects (Coherent.Power.namedPower generator degree)
      (Coherence.exact parameter) (Coherent.Power.namedPower generator exponent)
      (Coherent.Power.namedPower generator exponent) identity (NamedEquivalent.refl _))

end PowerIdentity

end Purelib.Approximation.Gaussian.Provenance.Power

end
