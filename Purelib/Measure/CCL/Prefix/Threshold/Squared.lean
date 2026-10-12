module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Threshold.Squared
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalOrder

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
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

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- The squared-probe margin budget gives equal threshold probabilities for any two completed-prefix realizations.

Every original witness lies at least the supplied positive margin on either side of the threshold, and its exact
retained blocks meet that margin's request. -/
theorem prefixFamilySquaredProbe_thresholdProbabilities_eq_of_margin
    (distribution : Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe atom.item.witness ∨
        probe atom.item.witness + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold Measure.atLeastEvent
  have budgetSmall :=
    Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual := Approximation.CCL.Prefix.realizedSquaredProbe_atLeastDecision_eq_of_margin
    atom.item.witnessRealizes (leftRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  have rightEqual := Approximation.CCL.Prefix.realizedSquaredProbe_atLeastDecision_eq_of_margin
    atom.item.witnessRealizes (rightRealizes atom member)
    probe factor factorPositive.le sensitive threshold margin marginPositive
    (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

/-- The squared-probe margin budget gives equal threshold probabilities for any two projective-prefix realizations.

Both families retain projective realization evidence for the original blocks; the witnesses satisfy the common positive
threshold margin. -/
theorem projectivePrefixFamilySquaredProbe_thresholdProbabilities_eq_of_margin
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe atom.item.witness ∨
        probe atom.item.witness + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedProjectivePrefixCertificate →
      Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (leftPoints certificate)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun certificate =>
          probe (rightPoints certificate)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold Measure.atLeastEvent
  have budgetSmall :=
    Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual :=
    Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      atom.item.witnessRealizes (leftRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      (separated atom member) budgetSmall
  have rightEqual :=
    Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      atom.item.witnessRealizes (rightRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      (separated atom member) budgetSmall
  exact leftEqual.trans rightEqual.symm

end Purelib.Measure.CCL.Prefix

end
