module

public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Polynomial.Power.Gaussian
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Data.Nat.Subtraction
import Purelib.Data.List.Replicate

/-!
# Operational evaluation of power-polynomial coefficient tables

The original high-to-low Horner process retains its initial step, zero block
and parameter constant. Finite congruence compares that same numerical channel
with the original input's retained natural power minus the exact parameter.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

open Purelib
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

/-- A retained finite input power followed by zero Horner coefficients is its original power at the sum of exponents. -/
private def horner_power_zeros (input : CoherentNamed) (exponent : Nat) : (count : Nat) →
    NamedEquivalent (horner input (Name.Coherent.Power.namedPower input exponent) (List.replicate count 0)).name
      (Name.Coherent.Power.namedPower input (exponent + count)).name
  | 0 => by
      rewrite [Nat.add_zero]
      exact NamedEquivalent.refl _
  | count + 1 => by
      let product := CoherentNamed.mul (Name.Coherent.Power.namedPower input exponent) input
      have step := horner_respects input input
        (CoherentNamed.add product (CoherentNamed.Coherence.exact 0)) product
        (NamedEquivalent.refl _) (Arithmetic.Add.coherentAdd_zero_right product) (List.replicate count 0)
      have remaining := horner_power_zeros input (exponent + 1) count
      have sum : (exponent + 1) + count = exponent + (count + 1) :=
        (Nat.add_assoc exponent 1 count).trans (congrArg (fun total => exponent + total) (Nat.add_comm 1 count))
      rewrite [sum] at remaining
      exact step.trans remaining

/-- The original power-polynomial Horner channel agrees with the original input power minus its exact parameter.

The displayed positive degree is arbitrary. Initial zero/one arithmetic and
the exact retained zero-coefficient block supply the comparison without
changing the input channel or claiming any finite sample is an exact root.
-/
def polynomialEval_rootPolynomial (parameter : Canonical) (degree : RootDegree) (input : CoherentNamed) :
    NamedEquivalent (polynomialEval (Polynomial.Power.Gaussian.rootPolynomial parameter degree) input).name
      (CoherentNamed.add (Name.Coherent.Power.namedPower input degree.value)
        (CoherentNamed.Coherence.exact (-parameter))).name := by
  let initial := CoherentNamed.add (CoherentNamed.mul (CoherentNamed.Coherence.exact 0) input)
    (CoherentNamed.Coherence.exact 1)
  have initialEquivalent : NamedEquivalent initial.name (CoherentNamed.Coherence.exact 1).name :=
    (Sum.Congruence.coherentAdd_respects
      (CoherentNamed.mul (CoherentNamed.Coherence.exact 0) input) (CoherentNamed.Coherence.exact 0)
      (CoherentNamed.Coherence.exact 1) (CoherentNamed.Coherence.exact 1)
      (Arithmetic.Mul.coherentMul_zero_left input) (NamedEquivalent.refl _)).trans
        (Arithmetic.Add.coherentAdd_zero_left (CoherentNamed.Coherence.exact 1))
  have zeros := horner_respects input input initial (CoherentNamed.Coherence.exact 1)
    (NamedEquivalent.refl _) initialEquivalent (List.replicate (degree.value - 1) 0)
  have powers := horner_power_zeros input 0 (degree.value - 1)
  rewrite [Nat.zero_add] at powers
  have middle := zeros.trans powers
  have predecessor : degree.value - 1 + 1 = degree.value :=
    (Nat.add_comm _ _).trans (Purelib.Data.Nat.Subtraction.add_sub_of_le degree.positive)
  change NamedEquivalent (horner input initial (List.replicate (degree.value - 1) 0 ++ [-parameter])).name _
  rewrite [horner_append]
  have products := Product.Congruence.coherentMul_respects
    (horner input initial (List.replicate (degree.value - 1) 0))
    (Name.Coherent.Power.namedPower input (degree.value - 1)) input input middle (NamedEquivalent.refl _)
  have result := Sum.Congruence.coherentAdd_respects
    (CoherentNamed.mul (horner input initial (List.replicate (degree.value - 1) 0)) input)
    (Name.Coherent.Power.namedPower input (degree.value - 1 + 1))
    (CoherentNamed.Coherence.exact (-parameter)) (CoherentNamed.Coherence.exact (-parameter)) products
    (NamedEquivalent.refl _)
  rewrite [predecessor] at result
  exact result

end Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

end
