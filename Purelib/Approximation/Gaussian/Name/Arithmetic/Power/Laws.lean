module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square.Congruence

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

namespace Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Laws

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Square

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

open Purelib.Approximation

/-- A fixed finite number of repeated squarings commutes with coherent multiplication.

This is the algebraic lift needed after a common dyadic range exponent has reduced both exponential inputs to the local
chart. -/
@[expose] def squareIterate_mul_equivalent : (exponent : Nat) →
    (left right : Coherent.CoherentNamed) →
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Power.squareIterate
          exponent left.name)
        (Power.squareIterate
          exponent right.name))
      (Power.squareIterate exponent
        (Named.mul
          left.name right.name))
  | 0, left, right =>
      NamedEquivalent.refl
        (Named.mul
          left.name right.name)
  | exponent + 1, left, right => by
      let previousLeft : Coherent.CoherentNamed :=
        { name := Power.squareIterate
            exponent left.name
          coherent := Coherent.squareIterateCoherent exponent left.name left.coherent }
      let previousRight : Coherent.CoherentNamed :=
        { name := Power.squareIterate
            exponent right.name
          coherent := Coherent.squareIterateCoherent exponent right.name right.coherent }
      let product :=
        CoherentNamed.mul left right
      let previousProduct : Coherent.CoherentNamed :=
        { name := Power.squareIterate
            exponent product.name
          coherent := Coherent.squareIterateCoherent exponent product.name
            product.coherent }
      let previousFactors :=
        CoherentNamed.mul
          previousLeft previousRight
      exact NamedEquivalent.trans
        (Laws.coherentMul_squares_interchange previousLeft previousRight)
        (Congruence.coherentSquare_respects previousFactors previousProduct
          (Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Laws.squareIterate_mul_equivalent exponent left right))

end

end Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Laws
