module
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Data.Gaussian.RationalExponent
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Laws
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Congruence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Expression.Basic
public import Purelib.Approximation.Gaussian.Expression.Exponential
public import Purelib.Approximation.Gaussian.Expression.Logarithm
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Data.Gaussian.Natural
public import Purelib.Data.Gaussian.Natural.Inverse
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Exponent

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Expression.Power

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Natural
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Exponent

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

/-- One branch-selected `q`th-root CCL expression. This is deliberately not the public multi-valued root family `roots`.
-/
@[expose] def selectedRoot (input : Expression) (branch : AnchoredChart input.output)
    (degree : Positive.RootDegree) : Expression :=
  exponential
    (mul
      (exact
        (Inverse.inverseDegree degree))
      (Expression.logarithm input branch))

/-- Raising the selected root to its displayed positive natural degree reconstructs the original input operationally. -/
@[expose] def selectedRoot_power_reconstructs (input : Expression)
    (branch : AnchoredChart input.output) (degree : Positive.RootDegree) :
    NamedEquivalent
      (Power.natPower (selectedRoot input branch degree).output
        degree.value).name
      input.output.name := by
  let logarithm := (AnchoredChart.output branch)
  let scaled := Power.scale (Inverse.inverseDegree degree) logarithm
  let rootOutput := Progressive.Range.Coherent.exp scaled.name
  have sumsToLogarithm : NamedEquivalent
      (Power.natSum scaled degree.value).name logarithm.name := by
    have collect := Power.natSum_scale (Inverse.inverseDegree degree) logarithm degree.value
    have coefficientOne :
        Natural.repeatedCoefficient (Inverse.inverseDegree degree) degree.value = 1 :=
      Inverse.repeatedCoefficient_inverseDegree degree
    exact NamedEquivalent.trans collect
      (by
        rw [coefficientOne]
        exact Mul.coherentMul_one_left logarithm)
  have exponentialSums : NamedEquivalent
      (Progressive.Range.Name.named
        (Power.natSum scaled degree.value).name)
      (Progressive.Range.Name.named logarithm.name) :=
    Progressive.Range.Congruence.automaticExp_respects (Power.natSum scaled degree.value) logarithm
      sumsToLogarithm
  exact NamedEquivalent.trans
    (by
      simpa only [selectedRoot, rootOutput, scaled, logarithm,
        Power.scale,
        exponential,
        mul,
        exact,
        leaf,
        Expression.logarithm] using
        Laws.automaticExp_natSum scaled degree.value)
    (NamedEquivalent.trans
      exponentialSums (AnchoredChart.exponential_inverse branch))

/-- Natural-numerator rational power `(p/q)` using the same displayed branch and the explicitly repeated
reciprocal-degree coefficient. -/
@[expose] def naturalRationalPower (input : Expression)
    (branch : AnchoredChart input.output) (numerator : Nat)
    (denominator : Positive.RootDegree) : Expression :=
  exponential
    (mul
      (exact
        (Natural.repeatedCoefficient (Inverse.inverseDegree denominator) numerator))
      (Expression.logarithm input branch))

/-- The `p/q` construction is operationally the `p`th finite power of the branch-selected `q`th root. -/
@[expose] def selectedRoot_power_to_naturalRationalPower (input : Expression)
    (branch : AnchoredChart input.output) (numerator : Nat)
    (denominator : Positive.RootDegree) :
    NamedEquivalent
      (Power.natPower (selectedRoot input branch denominator).output
        numerator).name
      (naturalRationalPower input branch numerator denominator).output.name :=
        by
  let logarithm := (AnchoredChart.output branch)
  let scaled := Power.scale (Inverse.inverseDegree denominator) logarithm
  let combined :=
    Power.scale (Natural.repeatedCoefficient (Inverse.inverseDegree denominator) numerator)
      logarithm
  have sumToCombined : NamedEquivalent
      (Power.natSum scaled numerator).name combined.name :=
    Power.natSum_scale (Inverse.inverseDegree denominator) logarithm numerator
  exact NamedEquivalent.trans
    (middle := Progressive.Range.Name.named (Power.natSum scaled numerator).name)
    (by
      simpa only [selectedRoot, scaled, logarithm, Power.scale,
        exponential,
        mul,
        exact,
        leaf,
        Expression.logarithm] using
        Laws.automaticExp_natSum scaled numerator)
    (by
      simpa only [naturalRationalPower, combined, scaled, logarithm,
        Power.scale,
        exponential,
        mul,
        exact,
        leaf,
        Expression.logarithm,
        Progressive.Range.Coherent.exp] using
        Progressive.Range.Congruence.automaticExp_respects (Power.natSum scaled numerator) combined
          sumToCombined)

/-- Branch-certified rational power `exp((p/q) * log(y))` as an actual finite CCL expression. -/
@[expose] def rationalPower (input : Expression) (branch : AnchoredChart
  input.output)
    (exponent : RationalExponent) : Expression :=
  exponential
    (mul
      (exact
        (RationalExponent.coefficient exponent))
      (Expression.logarithm input branch))

end

end Purelib.Approximation.Gaussian.Expression.Power
