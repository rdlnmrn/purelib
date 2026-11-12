module
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Division
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
public import Purelib.Approximation.Gaussian.Process.Coherent.Division.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Approximation.Gaussian.Sampling.Dyadic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Request

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence

/-- The positive rational quotient comparison coefficient determined by the two center bounds and the retained
denominator lower squared norm. -/
def coherentQuotientBridgeCoefficient
    (numerator denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) : Fraction.Rational :=
  8 +
    (32 *
      (2 * (1 + numerator.name.process.centerBound) +
        2 * (1 + denominator.name.process.centerBound))) /
      (apart.certificate.lowerSq * apart.certificate.lowerSq)

/-- The retained quotient comparison coefficient is strictly positive. -/
theorem
  coherentQuotientBridgeCoefficient_positive
    (numerator denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) :
    0 < coherentQuotientBridgeCoefficient numerator
      denominator apart := by
  unfold coherentQuotientBridgeCoefficient
  apply add_pos_of_pos_of_nonneg (by decide)
  have numeratorTerm :
      0 <= 2 * (1 + numerator.name.process.centerBound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) numerator.name.process.centerBound_nonneg)
  have denominatorTerm :
      0 <= 2 * (1 + denominator.name.process.centerBound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) denominator.name.process.centerBound_nonneg)
  have sumTerm :
      0 <= 2 * (1 + numerator.name.process.centerBound) +
        2 * (1 + denominator.name.process.centerBound) :=
    add_nonneg numeratorTerm denominatorTerm
  have thirtyTwoNonnegative : (0 : Fraction.Rational) <= 32 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 32) (by omega)).le
  have bridgeNumerator :
      0 <= 32 *
        (2 * (1 + numerator.name.process.centerBound) +
          2 * (1 + denominator.name.process.centerBound)) :=
    Arithmetic.mul_nonneg_direct thirtyTwoNonnegative sumTerm
  have bridgeDenominator :
      0 <= apart.certificate.lowerSq * apart.certificate.lowerSq :=
    Arithmetic.mul_nonneg_direct
      apart.certificate.positive.le apart.certificate.positive.le
  exact Field.div_nonneg_direct bridgeNumerator
    bridgeDenominator

/-- Divide the requested quotient tolerance by one plus the retained quotient comparison coefficient. -/
def coherentQuotientBridgeTarget
    (numerator denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) (target : Fraction.Rational) : Fraction.Rational :=
  target / (1 + coherentQuotientBridgeCoefficient numerator
    denominator apart)

/-- A positive output tolerance gives a positive quotient operand comparison tolerance.

The original positive bridge coefficient supplies a nonnegative increment.
Its unchanged unit-plus-coefficient denominator is strictly positive. -/
theorem coherentQuotientBridgeTarget_positive
    (numerator denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) {target : Fraction.Rational}
    (positive : 0 < target) :
    0 < coherentQuotientBridgeTarget numerator denominator
      apart target :=
  Field.div_pos_direct positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (coherentQuotientBridgeCoefficient_positive numerator
        denominator apart).le)

open Purelib.Approximation.Rational.Budget in
/-- Scaling the retained operand tolerance by its quotient coefficient stays below the output tolerance.

The original coefficient is strictly below its incremented denominator.
Positive target scaling and exact division cancellation bound the same retained tolerance. -/
theorem coherentQuotientBridgeTarget_budget_lt
    (numerator denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) {target : Fraction.Rational}
    (positive : 0 < target) :
    coherentQuotientBridgeTarget numerator denominator apart
      target *
        coherentQuotientBridgeCoefficient numerator
          denominator apart <
      target := by
  have paid := Weighted.mul_allowance_lt positive
    (coherentQuotientBridgeCoefficient_positive numerator denominator apart).le
  rewrite [Weighted.allowance_eq_div_one_add] at paid
  exact (Fraction.Field.mul_comm _ _).trans_lt paid

/-- The actual stateful quotient is operationally equivalent to the equal-index sampled quotient. The proof refines both
operand coherences only to explicit rational requests and applies the finite quotient estimate. -/
def coherentDiv_toSampled (numerator
  denominator : CoherentNamed)
    (apart : Named.Apart denominator.name) :
    NamedEquivalent
      (Named.div numerator.name denominator.name apart)
      (Sample.sampledQuotientApproximation numerator denominator apart).toNamed := by
  let numeratorProcess := numerator.name.process
  let denominatorProcess := denominator.name.process
  let process := numeratorProcess.div denominatorProcess apart.certificate
  let start : process.State := (numerator.name.state, denominator.name.state)
  let quotient := Sample.sampledQuotientApproximation numerator denominator apart
  let bridge : Equivalent
      (Sampling.approximation
        (Named.div numerator.name denominator.name
          apart)) quotient :=
    { compare := by
        intro actualStart sampledStart target positive
        let semanticTarget := coherentQuotientBridgeTarget
          numerator
          denominator apart target
        have semanticPositive : 0 < semanticTarget :=
          coherentQuotientBridgeTarget_positive numerator
            denominator apart
            positive
        let numeratorRequest := numerator.coherent.accuracyRequest semanticTarget
        let denominatorRequest :=
          denominator.coherent.accuracyRequest semanticTarget
        have numeratorRequestPositive : 0 < numeratorRequest :=
          numerator.coherent.accuracyRequest_pos semanticPositive
        have denominatorRequestPositive : 0 < denominatorRequest :=
          denominator.coherent.accuracyRequest_pos semanticPositive
        let sharedRequest := Coherent.commonRequest
          numeratorRequest denominatorRequest
        have sharedRequestPositive : 0 < sharedRequest :=
          Coherent.commonRequest_pos
            numeratorRequestPositive denominatorRequestPositive
        let outerRequest :=
          Coherent.divisionOuterTarget
            numeratorProcess denominatorProcess apart.certificate.lowerSq
              sharedRequest
        have outerRequestPositive : 0 < outerRequest :=
          Coherent.divisionOuterTarget_pos
            numeratorProcess denominatorProcess apart.certificate.positive
              sharedRequestPositive
        let actualRequest := Common.commonTarget
          outerRequest semanticTarget
        have actualRequestPositive : 0 < actualRequest :=
          Common.commonTarget_pos outerRequestPositive
            semanticPositive
        let actualIndex := Search.firstQuarterBelow
          1 actualStart actualRequest
        have actualIndexGe : actualStart <= actualIndex :=
          Search.firstQuarterBelow_ge
            1 actualStart actualRequest
        have actualRequestSmall :
            Process.Sampling.refinementTarget actualIndex <
              actualRequest :=
          Search.firstQuarterBelow_accurate
            1 (by decide) actualStart actualRequest actualRequestPositive
        have actualRequestLtOuter :
            Process.Sampling.refinementTarget actualIndex <
              outerRequest :=
          actualRequestSmall.trans
            (Common.commonTarget_lt_left outerRequestPositive
              semanticPositive)
        have actualRequestLtSemantic :
            Process.Sampling.refinementTarget actualIndex <
              semanticTarget :=
          actualRequestSmall.trans
            (Common.commonTarget_lt_right outerRequestPositive
              semanticPositive)
        let sampledIndex := Search.firstQuarterBelow
          1 sampledStart sharedRequest
        have sampledIndexGe : sampledStart <= sampledIndex :=
          Search.firstQuarterBelow_ge
            1 sampledStart sharedRequest
        have sampledRequestSmall :
            Process.Sampling.refinementTarget sampledIndex <
              sharedRequest :=
          Search.firstQuarterBelow_accurate
            1 (by decide) sampledStart sharedRequest sharedRequestPositive
        let baseState := Process.Sampling.stateAt process start actualIndex
        have baseComponentSmall :
            numerator.coherent.allowance baseState.1 < semanticTarget ∧
              denominator.coherent.allowance baseState.2 < semanticTarget :=
          Process.Coherent.Division.Sampling.quotient_stateAt_component_allowance_lt numerator.coherent
            denominator.coherent apart.certificate start actualIndex
              semanticTarget semanticPositive actualRequestLtOuter
        exact
          { leftIndex := actualIndex
            rightIndex := sampledIndex
            left_ge := actualIndexGe
            right_ge := sampledIndexGe
            close := by
              intro actualLater sampledLater actualOrder sampledOrder
              have canonicalRequestSmall :
                  Process.Sampling.refinementTarget sampledLater <
                    sharedRequest :=
                (quarterRadius_antitone (by decide)
                  sampledOrder).trans_lt
                  sampledRequestSmall
              have canonicalRequestLtNumerator :
                  Process.Sampling.refinementTarget sampledLater <
                    numeratorRequest :=
                canonicalRequestSmall.trans
                  (Coherent.commonRequest_lt_left
                    numeratorRequestPositive denominatorRequestPositive)
              have canonicalRequestLtDenominator :
                  Process.Sampling.refinementTarget sampledLater <
                    denominatorRequest :=
                canonicalRequestSmall.trans
                  (Coherent.commonRequest_lt_right
                    numeratorRequestPositive denominatorRequestPositive)
              have canonicalNumeratorSmall :
                  numerator.coherent.allowance
                      (Process.Sampling.stateAt numeratorProcess
                        numerator.name.state sampledLater) < semanticTarget :=
                Coherent.stateAt_allowance_lt
                  numerator.coherent numerator.name.state sampledLater
                    semanticTarget semanticPositive canonicalRequestLtNumerator
              have canonicalDenominatorSmall :
                  denominator.coherent.allowance
                      (Process.Sampling.stateAt denominatorProcess
                        denominator.name.state sampledLater) < semanticTarget :=
                Coherent.stateAt_allowance_lt
                  denominator.coherent denominator.name.state sampledLater
                    semanticTarget semanticPositive
                      canonicalRequestLtDenominator
              let numeratorReading := (numeratorProcess.witness baseState.1).val
              let denominatorReading :=
                (denominatorProcess.witness baseState.2).val
              let canonicalNumerator :=
                Process.Sampling.witnessAt numeratorProcess
                  numerator.name.state sampledLater
              let canonicalDenominator :=
                Process.Sampling.witnessAt denominatorProcess
                  denominator.name.state sampledLater
              have numeratorPossible :
                  numeratorProcess.Possible baseState.1 numeratorReading :=
                (numeratorProcess.witness baseState.1).property
              have denominatorPossible :
                  denominatorProcess.Possible baseState.2 denominatorReading :=
                (denominatorProcess.witness baseState.2).property
              have canonicalNumeratorPossible :
                  numeratorProcess.Possible
                    (Process.Sampling.stateAt numeratorProcess
                      numerator.name.state sampledLater) canonicalNumerator :=
                Process.Sampling.witnessAt_possible numeratorProcess
                  numerator.name.state sampledLater
              have canonicalDenominatorPossible :
                  denominatorProcess.Possible
                    (Process.Sampling.stateAt denominatorProcess
                      denominator.name.state sampledLater) canonicalDenominator :=
                Process.Sampling.witnessAt_possible denominatorProcess
                  denominator.name.state sampledLater
              have numeratorCloseRaw := numerator.coherent.possible_close
                numeratorPossible canonicalNumeratorPossible
              have denominatorCloseRaw := denominator.coherent.possible_close
                denominatorPossible canonicalDenominatorPossible
              have numeratorClose :
                  Basic.normSq (numeratorReading - canonicalNumerator) <=
                    8 * semanticTarget := by
                calc
                  Basic.normSq (numeratorReading - canonicalNumerator) <=
                      4 * (numerator.coherent.allowance baseState.1 +
                        numerator.coherent.allowance
                          (Process.Sampling.stateAt numeratorProcess
                            numerator.name.state sampledLater)) :=
                    numeratorCloseRaw
                  _ <= 4 * (semanticTarget + semanticTarget) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add baseComponentSmall.1.le
                        canonicalNumeratorSmall.le) (by decide)
                  _ = 8 * semanticTarget := by ring1
              have denominatorCloseForward :
                  Basic.normSq (denominatorReading - canonicalDenominator) <=
                    8 * semanticTarget := by
                calc
                  Basic.normSq (denominatorReading - canonicalDenominator) <=
                      4 * (denominator.coherent.allowance baseState.2 +
                        denominator.coherent.allowance
                          (Process.Sampling.stateAt denominatorProcess
                            denominator.name.state sampledLater)) :=
                    denominatorCloseRaw
                  _ <= 4 * (semanticTarget + semanticTarget) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add baseComponentSmall.2.le
                        canonicalDenominatorSmall.le) (by decide)
                  _ = 8 * semanticTarget := by ring1
              have denominatorClose :
                  Basic.normSq (canonicalDenominator - denominatorReading) <=
                    8 * semanticTarget := by
                have identity : canonicalDenominator - denominatorReading =
                    -(denominatorReading - canonicalDenominator) := by
                  apply Data.Gaussian.Basic.ext <;>
                    simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                      Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
                rw [identity, Basic.normSq_neg]
                exact denominatorCloseForward
              let numeratorBound := 2 * (1 + numeratorProcess.centerBound)
              let denominatorBound := 2 * (1 + denominatorProcess.centerBound)
              have canonicalNumeratorBound :
                  Basic.normSq canonicalNumerator <= numeratorBound :=
                Process.Sampling.witnessAt_bounded numeratorProcess
                  numerator.name.state sampledLater
              have canonicalDenominatorBound :
                  Basic.normSq canonicalDenominator <= denominatorBound :=
                Process.Sampling.witnessAt_bounded denominatorProcess
                  denominator.name.state sampledLater
              have denominatorReadingLower : apart.certificate.lowerSq <=
                  Basic.normSq denominatorReading :=
                apart.certificate.lower baseState.2
                  (denominatorProcess.possible_inside denominatorPossible)
              have canonicalDenominatorLower : apart.certificate.lowerSq <=
                  Basic.normSq canonicalDenominator :=
                apart.certificate.lower _
                  (denominatorProcess.possible_inside
                    canonicalDenominatorPossible)
              have quotientClose :=
                Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
                  apart.certificate.positive
                  (leftNumerator := numeratorReading)
                  (rightNumerator := canonicalNumerator)
                  (leftDenominator := denominatorReading)
                  (rightDenominator := canonicalDenominator)
                  (numeratorSlope := (8 : Fraction.Rational))
                  (numeratorBound := numeratorBound)
                  (denominatorBound := denominatorBound)
                  (pointMovement := semanticTarget)
                  (rootMovement := 8 * semanticTarget)
                  numeratorClose canonicalNumeratorBound
                  canonicalDenominatorBound denominatorClose
                  denominatorReadingLower canonicalDenominatorLower
              have quotientCloseSimplified :
                  Basic.normSq (numeratorReading / denominatorReading -
                      canonicalNumerator / canonicalDenominator) <=
                    (16 * semanticTarget *
                      (numeratorBound + denominatorBound)) /
                        (apart.certificate.lowerSq *
                          apart.certificate.lowerSq) := by
                exact quotientClose.trans_eq (by
                  unfold Rational.Budget.Quotient.quotientBound
                  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
                  ring1)
              have actualTail :
                  Basic.normSq
                      (Process.Sampling.witnessAt process start
                          actualLater -
                        Process.Sampling.witnessAt process start
                          actualIndex) <=
                    4 * Process.Sampling.refinementTarget actualIndex := by
                rw [← Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                exact Process.Sampling.witnessAt_later_close
                  process start actualOrder
              have baseWitness :
                  Process.Sampling.witnessAt process start actualIndex =
                    numeratorReading / denominatorReading := rfl
              change Basic.normSq
                  (Process.Sampling.witnessAt process start actualLater -
                    quotient.sample sampledLater) < target
              rw [Sample.sampledQuotientApproximation_sample]
              calc
                Basic.normSq
                    (Process.Sampling.witnessAt process start actualLater -
                      canonicalNumerator / canonicalDenominator) <=
                  2 *
                    (Basic.normSq
                        (Process.Sampling.witnessAt process start
                            actualLater -
                          Process.Sampling.witnessAt process start
                            actualIndex) +
                      Basic.normSq
                        (Process.Sampling.witnessAt process start
                            actualIndex -
                          canonicalNumerator / canonicalDenominator)) :=
                  Bounds.normSq_sub_le_via _ _ _
                _ <= 2 *
                    (4 * Process.Sampling.refinementTarget actualIndex +
                      (16 * semanticTarget *
                        (numeratorBound + denominatorBound)) /
                          (apart.certificate.lowerSq *
                            apart.certificate.lowerSq)) := by
                  apply Arithmetic.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact quotientCloseSimplified
                  · decide
                _ <= 2 *
                    (4 * semanticTarget +
                      (16 * semanticTarget *
                        (numeratorBound + denominatorBound)) /
                          (apart.certificate.lowerSq *
                            apart.certificate.lowerSq)) :=
                  Arithmetic.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (Arithmetic.mul_le_mul_of_nonneg_left_direct
                        actualRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget *
                    coherentQuotientBridgeCoefficient
                      numerator denominator
                      apart := by
                  dsimp only [numeratorBound, denominatorBound]
                  unfold
                    coherentQuotientBridgeCoefficient
                  rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
                    Algebra.Field.ExplicitField.div_eq_mul_inv]
                  ring1
                _ < target :=
                  coherentQuotientBridgeTarget_budget_lt
                  numerator denominator apart positive } }
  exact Equivalent.trans bridge
    (Equivalent.symm
      (Equivalent.toNamed_sampling quotient))

/-- Stateful apartness-certified division respects operational equality in both coherent operands. -/
def coherentDiv_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      CoherentNamed)
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    (numeratorEquivalent : NamedEquivalent firstNumerator.name
      secondNumerator.name)
    (denominatorEquivalent : NamedEquivalent firstDenominator.name
      secondDenominator.name) :
    NamedEquivalent
      (Named.div firstNumerator.name
        firstDenominator.name firstApart)
      (Named.div secondNumerator.name
        secondDenominator.name secondApart) :=
  NamedEquivalent.trans
    (coherentDiv_toSampled firstNumerator firstDenominator
      firstApart)
    (NamedEquivalent.trans
      (Equivalent.toNamed
        (SampleEquivalence.sampledQuotientApproximation_respects firstNumerator secondNumerator
          firstDenominator secondDenominator firstApart secondApart
            numeratorEquivalent denominatorEquivalent))
      (NamedEquivalent.symm
        (coherentDiv_toSampled secondNumerator
          secondDenominator secondApart)))

end Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence

end

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence

open Purelib.Approximation.Rational.Budget

/-- Compare the two actual guarded stateful quotients from finite operand comparisons.

The supplied operand comparisons may carry nonzero spatial errors. Both
original quotient programs keep their own denominator guards; their
original sampler bridges pay an independent accuracy request on each side.
The explicit finite quotient bound is separated from that added accuracy.
-/
def coherentDiv_comparison
    (firstNumerator secondNumerator firstDenominator secondDenominator : CoherentNamed)
    (firstApart : Named.Apart firstDenominator.name) (secondApart : Named.Apart secondDenominator.name)
    {numeratorLeftStart numeratorRightStart denominatorLeftStart denominatorRightStart : Nat}
    {numeratorTarget denominatorTarget : Fraction.Rational}
    (numeratorComparison : Comparison
      (Sampling.approximation firstNumerator.name) (Sampling.approximation secondNumerator.name)
      numeratorLeftStart numeratorRightStart numeratorTarget)
    (denominatorComparison : Comparison
      (Sampling.approximation firstDenominator.name) (Sampling.approximation secondDenominator.name)
      denominatorLeftStart denominatorRightStart denominatorTarget)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Comparison (Sampling.approximation (Named.div firstNumerator.name firstDenominator.name firstApart))
      (Sampling.approximation (Named.div secondNumerator.name secondDenominator.name secondApart))
      leftStart rightStart
      (4 * Quotient.quotientBound 1 (Sampling.approximation secondNumerator.name).centerBound
        (Sampling.approximation secondDenominator.name).centerBound
        (SampleEquivalence.commonLower firstApart secondApart) numeratorTarget denominatorTarget + accuracy) := by
  let precision := accuracy / 16
  have precisionPositive : 0 < precision := Field.div_pos_direct positive (by decide)
  let firstSource := Sample.sampledQuotientApproximation firstNumerator firstDenominator firstApart
  let secondSource := Sample.sampledQuotientApproximation secondNumerator secondDenominator secondApart
  let firstBridge := Equivalent.trans (coherentDiv_toSampled firstNumerator firstDenominator firstApart)
    (Equivalent.toNamed_sampling firstSource)
  let secondBridge := Equivalent.trans (coherentDiv_toSampled secondNumerator secondDenominator secondApart)
    (Equivalent.toNamed_sampling secondSource)
  let first := firstBridge.compare leftStart 0 precision precisionPositive
  let last := secondBridge.symm.compare 0 rightStart precision precisionPositive
  let bound := Quotient.quotientBound 1 (Sampling.approximation secondNumerator.name).centerBound
    (Sampling.approximation secondDenominator.name).centerBound
    (SampleEquivalence.commonLower firstApart secondApart) numeratorTarget denominatorTarget
  let numerator : Comparison (Sampling.approximation firstNumerator.name)
      (Sampling.approximation secondNumerator.name) 0 0 numeratorTarget :=
    ⟨numeratorComparison.leftIndex, numeratorComparison.rightIndex, Nat.zero_le _, Nat.zero_le _,
      numeratorComparison.close⟩
  let denominator : Comparison (Sampling.approximation firstDenominator.name)
      (Sampling.approximation secondDenominator.name) 0 0 denominatorTarget :=
    ⟨denominatorComparison.leftIndex, denominatorComparison.rightIndex, Nat.zero_le _, Nat.zero_le _,
      denominatorComparison.close⟩
  have budget : bound < bound + precision := by
    have paid := Arithmetic.add_lt_add_left_direct precisionPositive bound
    rewrite [show bound + 0 = bound by ring1] at paid
    exact paid
  let middle := SampleEquivalence.sampledQuotientComparison
    firstNumerator secondNumerator firstDenominator secondDenominator firstApart secondApart
    numerator denominator (bound + precision) budget
  let combined := first.trans (middle.trans last)
  have ordered : 2 * (precision + 2 * (bound + precision + precision)) ≤ 4 * bound + accuracy := by
    have grouped : 2 * (precision + 2 * (bound + precision + precision)) =
        4 * bound + (10 / 16 : Fraction.Rational) * accuracy := by
      dsimp only [precision]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rewrite [grouped]
    have paid := Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide +kernel : (10 / 16 : Fraction.Rational) < 1) positive
    rewrite [Fraction.Field.one_mul] at paid
    exact (Arithmetic.add_lt_add_left_direct paid (4 * bound)).le
  exact combined.weaken _ ordered

end Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence

end
