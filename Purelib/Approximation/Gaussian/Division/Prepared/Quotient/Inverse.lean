module

public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws

/-!
# Actual prepared reciprocals agree with retained inverse channels

A product-to-unit certificate at the original input and candidate inverse
transports to the same retained apart denominator. Operational cancellation
then compares the actual prepared division program with that original inverse.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- An original product-to-unit certificate identifies the actual reciprocal through its retained preparation. -/
def reciprocal_equivalent_of_product {channel : CoherentNamed} (prepared : Prepared channel)
    (inverse : CoherentNamed)
    (identity : NamedEquivalent (CoherentNamed.mul channel inverse).name (Coherence.exact 1).name) :
    NamedEquivalent (prepared.quotient (Coherence.exact 1)).name inverse.name := by
  let output := prepared.quotient (Coherence.exact 1)
  have candidateProduct : NamedEquivalent (CoherentNamed.mul prepared.denominator inverse).name
      (Coherence.exact 1).name :=
    NamedEquivalent.trans
      (Congruence.coherentMul_respects prepared.denominator channel inverse inverse
        (NamedEquivalent.symm prepared.equivalent) (NamedEquivalent.refl _)) identity
  have actualProduct : NamedEquivalent (CoherentNamed.mul prepared.denominator output).name
      (Coherence.exact 1).name :=
    NamedEquivalent.trans (Laws.coherentMul_comm prepared.denominator output)
      (Cancellation.reciprocal_mul_cancel prepared.denominator prepared.apart)
  exact NamedEquivalent.symm
    (Cancellation.coherentMul_cancel_left prepared.denominator inverse output prepared.apart
      (NamedEquivalent.trans candidateProduct (NamedEquivalent.symm actualProduct)))

end Purelib.Approximation.Gaussian.Division.Prepared

end
