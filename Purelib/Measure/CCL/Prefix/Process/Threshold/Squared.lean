module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Threshold.Squared
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalOrder

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.Measure.CCL.Prefix
namespace PrefixFamilyProcess

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The squared-sensitivity margin request makes threshold probabilities identical for any two requested-state
realizations.

The fixed witnesses lie on either side of the threshold by the same positive margin, and both families realize the exact
requested blocks on all original atoms. -/
theorem request_squaredProbeThreshold_probabilities_eq {index :
  Type}
    (process : Cylinder.PrefixFamilyProcess index)
    (distribution : Measure.Distribution index)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredThresholdBlockCount margin factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredThresholdBlockCount margin factor)) atom.item)
        (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  let requested := process.request state
    (Budget.requiredSquaredThresholdBlockCount margin factor)
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold Measure.atLeastEvent
  have budgetSmall :=
    Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct marginPositive 2)
      factorPositive
      (process.request_length state
        (Budget.requiredSquaredThresholdBlockCount margin factor) atom.item)
  have leftEqual := Approximation.CCL.Prefix.realizedSquaredProbe_atLeastDecision_eq_of_margin
    (process.realizes requested atom.item) (leftRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  have rightEqual := Approximation.CCL.Prefix.realizedSquaredProbe_atLeastDecision_eq_of_margin
    (process.realizes requested atom.item) (rightRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

end PrefixFamilyProcess
end Purelib.Measure.CCL.Prefix

end
