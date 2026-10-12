module
public import Purelib.Approximation.ElementaryFunction.Exponential.Operational.Inverse
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Approximation.Gaussian.Name.Coherent.Power

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Exponential.Laws

open Purelib.Approximation.ElementaryFunction.Exponential.Operational
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

open Purelib.Approximation

/-- If two coherent names have operationally equivalent exponentials, then the exponential of their finite CCL
difference is operationally exact one. -/
@[expose] def exp_difference_unit (left right : CoherentNamed)
    (exponentials : Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named right.name)
      (Exponential.Progressive.Range.Name.named left.name)) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Difference.difference left right).name)
      (Named.exact 1) := by
  let negativeLeft :=
    CoherentNamed.neg left
  let rightExp := Exponential.Progressive.Range.Coherent.exp right.name
  let leftExp := Exponential.Progressive.Range.Coherent.exp left.name
  let negativeLeftExp :=
    Exponential.Progressive.Range.Coherent.exp negativeLeft.name
  have products : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        rightExp.name negativeLeftExp.name)
      (Named.mul
        leftExp.name negativeLeftExp.name) :=
    Congruence.coherentMul_respects rightExp leftExp negativeLeftExp negativeLeftExp
      exponentials
      (NamedEquivalent.refl
        negativeLeftExp.name)
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      (by
        simpa only [Difference.difference, negativeLeft, rightExp, negativeLeftExp,
          Coherent.CoherentNamed.add,
          CoherentNamed.neg,
          Exponential.Progressive.Range.Coherent.exp] using
          Exponential.Progressive.Range.Addition.automaticExp_add right negativeLeft))
    (NamedEquivalent.trans products
      (Inverse.automaticExp_mul_neg left))

end

public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

open Purelib.Approximation

/-- Repeated multiplication of `exp(x)` is operationally the exponential of the corresponding finite repeated sum. -/
@[expose] def automaticExp_natSum (value : CoherentNamed) :
    (count : Nat) →
      Gaussian.Equivalence.NamedEquivalent
        (Power.natPower (Exponential.Progressive.Range.Coherent.exp value.name)
          count).name
        (Exponential.Progressive.Range.Name.named
          (Power.natSum value count).name)
  | 0 => by
      simpa only [Power.natPower, Power.natSum,
        Coherence.exact] using
        NamedEquivalent.symm
          Exponential.Progressive.Range.Exact.automaticExp_zero
  | count + 1 => by
      let exponential :=
        Exponential.Progressive.Range.Coherent.exp value.name
      let previousPower := Power.natPower exponential count
      let previousSum := Power.natSum value count
      let previousExponential :=
        Exponential.Progressive.Range.Coherent.exp previousSum.name
      have replacePrevious : Gaussian.Equivalence.NamedEquivalent
          (Named.mul
            exponential.name previousPower.name)
          (Named.mul
            exponential.name previousExponential.name) :=
        Congruence.coherentMul_respects exponential exponential
          previousPower previousExponential
          (NamedEquivalent.refl
            exponential.name)
          (Purelib.Approximation.Gaussian.Exponential.Laws.automaticExp_natSum value count)
      exact NamedEquivalent.trans
        (middle := Named.mul
          exponential.name previousExponential.name)
        (by
            simpa only [Power.natPower, exponential, previousPower, CoherentNamed.mul]
              using replacePrevious)
        (by
          simpa only [Power.natSum, previousSum, previousExponential,
            exponential, Exponential.Progressive.Range.Coherent.exp,
            Coherent.CoherentNamed.add] using
            Exponential.Progressive.Range.Addition.automaticExp_add value previousSum)

end

end

end Purelib.Approximation.Gaussian.Exponential.Laws
