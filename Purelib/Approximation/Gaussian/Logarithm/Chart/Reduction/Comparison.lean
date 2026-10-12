module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Prepared
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Sampling
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Synchronized
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Division
public import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Projective.Homography.Cayley.Bounds
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Sampling
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat

public section

/-!
# Operational branch certificates for the complex logarithm

The geometric `Chart` data proves that its finite local recurrence is safe
and productive.  It intentionally permits any additive correction name.
This module records the additional semantic obligation needed to call that
correction a logarithm branch: exponentiating it must reproduce the inverse
of the chart's displayed scale, in finite operational equality.

Once the local inverse law and the exponential addition law are established,
this certificate is the missing branch datum in the calculation

`Exp(localLog(factor * input) + correction) = input`.

The exponentiation, equality, and inverse factor below are all CCL programs
or displayed Gaussian rationals.  No completed complex number or global
single-valued logarithm is introduced.
-/

/-- A fixed finite quadrance bound for a synchronized input witness once its coherence allowance is below one. -/
@[expose] def reducedBridgeSourceBound (input :
  Gaussian.Name.Basic.Named) :
    Fraction.Rational :=
  2 * (1 + input.process.centerBound)

/-- The uniform source bound computed from a name's retained centre bound is strictly positive. -/
theorem reducedBridgeSourceBound_pos (input :
  Gaussian.Name.Basic.Named) :
    0 < reducedBridgeSourceBound input :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) input.process.centerBound_nonneg)

/-- The displayed coefficient in the asynchronous reduced-coordinate sensitivity estimate, specialized to the fixed
finite source bound above. -/
@[expose] def reducedBridgeSensitivity (input : Gaussian.Name.Basic.Named) (chart : Chart input) :
    Fraction.Rational :=
  (4 *
      (Data.Gaussian.Norm.Basic.normSq chart.factor * Data.Gaussian.Norm.Basic.normSq chart.factor *
          reducedBridgeSourceBound input + Data.Gaussian.Norm.Basic.normSq chart.factor)) /
    (chart.denominatorApart.lowerSq * chart.denominatorApart.lowerSq)

/-- The retained branch certificate makes the asynchronous reduced-coordinate sensitivity strictly positive. -/
theorem reducedBridgeSensitivity_pos (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) :
    0 < Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity input chart := by
  have factorPositive : 0 < Data.Gaussian.Norm.Basic.normSq chart.factor :=
    Data.Gaussian.Norm.Basic.normSq_pos certificate.factor_ne_zero
  have squareSourceNonnegative :
      0 ≤ Data.Gaussian.Norm.Basic.normSq chart.factor * Data.Gaussian.Norm.Basic.normSq chart.factor
        *
        reducedBridgeSourceBound input :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Data.Gaussian.Norm.Basic.normSq_nonneg chart.factor) (Data.Gaussian.Norm.Basic.normSq_nonneg chart.factor))
      (reducedBridgeSourceBound_pos input).le
  have sumPositive :
      0 < Data.Gaussian.Norm.Basic.normSq chart.factor * Data.Gaussian.Norm.Basic.normSq chart.factor
        *
          reducedBridgeSourceBound input + Data.Gaussian.Norm.Basic.normSq chart.factor :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct squareSourceNonnegative factorPositive
  unfold Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) sumPositive)
    (Fraction.Order.Arithmetic.mul_pos_direct
      chart.denominatorApart.positive chart.denominatorApart.positive)

/-- Sixteen times the retained asynchronous reduced-coordinate sensitivity. -/
@[expose] def reducedBridgeCoefficient (input : Gaussian.Name.Basic.Named) (chart : Chart input) :
    Fraction.Rational :=
  16 * Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity input chart

/-- The asynchronous reduced-coordinate comparison coefficient is strictly positive. -/
theorem reducedBridgeCoefficient_pos (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) :
    0 < Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity_pos input chart certificate)

/-- A positive finite input-coherence budget whose displayed bridge coefficient consumes strictly less than the
requested final tolerance. -/
@[expose] def reducedBridgeTarget (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (target : Fraction.Rational) :
    Fraction.Rational :=
  target / (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)

/-- The reduced-coordinate input tolerance is positive for a positive output target. -/
theorem reducedBridgeTarget_pos (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget input chart target :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient_pos input chart
      certificate).le)

/-- The reduced-coordinate input tolerance is below one for a positive output target.

The retained comparison coefficient is strictly positive. Translating this
strict inequality by the target bounds the numerator by its positive denominator. -/
theorem reducedBridgeTarget_lt_one (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget input chart target < 1 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient_pos input chart
      certificate).le)).2
  calc
    target < target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart
      :=
      by
        have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient_pos input chart
            certificate) target
        rw [Fraction.Field.add_comm target 0, Fraction.Field.zero_add target] at translated
        exact translated
    _ = 1 * (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)
      := by
      ring1

/-- The input tolerance multiplied by the retained comparison coefficient is strictly below the positive output target.
-/
theorem reducedBridgeTarget_budget_lt (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget input chart target *
        Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart < target := by
  have denominatorPositive :
      0 < target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct positive
      (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient_pos input chart
      certificate).le
  change target / (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
    chart) *
      Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart < target
  calc
    target / (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)
      *
        Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart =
      (target * Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart) /
        (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart) :=
          by
      change (target *
          (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)⁻¹)
            *
            Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart =
        (target * Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart) *
          (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)⁻¹
      calc
        (target * (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
          chart)⁻¹) *
            Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart =
          target * ((target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
            chart)⁻¹ *
            Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart) :=
              Fraction.Field.mul_assoc _ _ _
        _ = target * (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart *
            (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
              chart)⁻¹) := by
          rw [Fraction.Field.mul_comm
            (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
              chart)⁻¹]
        _ = (target * Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart)
          *
            (target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
              chart)⁻¹ :=
          (Fraction.Field.mul_assoc _ _ _).symm
    _ < target := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        denominatorPositive).2
      have coefficientLt : Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input
        chart <
          target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart :=
            by
        calc
          Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart =
              0 + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart :=
            by ring1
          _ < target + Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart
            :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct positive _
      exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        positive coefficientLt

/-- The source-sample index selected by one finite sampling request to the productive synchronized reference wrapper. -/
@[expose] def synchronizedReducedSourceIndex (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart) (outputIndex : Nat) : Nat :=
  Sampling.emittedSampleIndex
    (Synchronized.synchronizedReducedApproximation input chart certificate) outputIndex

/-- One bounded scan computing an output index whose productive wrapper has reached a requested finite source index. -/
@[expose] def synchronizedReducedOutputIndexForSource (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (current requestedSource : Nat) : Nat :=
  Search.firstQuarterBelow 1 current
    (Geometric.Basic.quarterRadius
      (Synchronized.synchronizedReducedErrorScale input chart) requestedSource)

/-- The computed wrapper output index is no earlier than the supplied current output index. -/
theorem synchronizedReducedOutputIndexForSource_ge (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (current requestedSource : Nat) :
    current ≤ Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedOutputIndexForSource
      input chart current requestedSource :=
  Search.firstQuarterBelow_ge 1 current _

/-- The bounded scan really reaches the requested finite source index. -/
theorem synchronizedReduced_reachesRequestedSourceIndex (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (current requestedSource : Nat) :
    requestedSource ≤ Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedSourceIndex input
      chart certificate
      (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedOutputIndexForSource input chart
        current requestedSource) := by
  let approximation := Synchronized.synchronizedReducedApproximation input chart certificate
  let outputIndex := Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedOutputIndexForSource
    input chart current requestedSource
  let sourceIndex := Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedSourceIndex
    input chart certificate outputIndex
  have sourceRadius :
      Geometric.Basic.quarterRadius
          (Synchronized.synchronizedReducedErrorScale input chart) sourceIndex <
        Gaussian.Process.Sampling.refinementTarget outputIndex := by
    exact Gaussian.Process.Sampling.stateAt_accurate
      approximation.toProcess
        (show approximation.toProcess.State from (0 : Nat)) outputIndex
  have outputSmall :
      Gaussian.Process.Sampling.refinementTarget outputIndex <
        Geometric.Basic.quarterRadius
          (Synchronized.synchronizedReducedErrorScale input chart) requestedSource := by
    exact Search.firstQuarterBelow_accurate
      1 (by decide) current
      (Geometric.Basic.quarterRadius
        (Synchronized.synchronizedReducedErrorScale input chart) requestedSource)
      (Geometric.Basic.quarterRadius_pos
        (Synchronized.synchronizedReducedErrorScale_pos input chart certificate)
        requestedSource)
  have sourceSmall :
      Geometric.Basic.quarterRadius
          (Synchronized.synchronizedReducedErrorScale input chart) sourceIndex <
        Geometric.Basic.quarterRadius
          (Synchronized.synchronizedReducedErrorScale input chart) requestedSource :=
    sourceRadius.trans outputSmall
  by_contra notReached
  have sourceBefore : sourceIndex ≤ requestedSource :=
    Nat.le_of_lt (Nat.lt_of_not_ge notReached)
  have reverseBound := quarterRadius_antitone
    (Synchronized.synchronizedReducedErrorScale_nonneg input chart) sourceBefore
  exact (not_lt_of_ge reverseBound) sourceSmall

/-- The original stateful quotient, whose numerator and denominator may refine the input independently, is operationally
equal to the diagonal synchronized quotient.

For each displayed tolerance this comparison computes two finite indices and applies the explicit asynchronous rational
sensitivity estimate to three finite input witnesses. -/
@[expose] def reduced_equivalent_synchronizedReduced (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Reduction.reduced input chart.factor
        chart.denominatorApart)
      (Synchronized.synchronizedReducedNamed input chart certificate) where
  compare := by
    intro leftStart rightStart target positive
    let semanticTarget := Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget input chart
      target
    have semanticPositive : 0 < semanticTarget :=
      Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget_pos input chart certificate
        positive
    have semanticLtOne : semanticTarget < 1 :=
      Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget_lt_one input chart certificate
        positive
    let inputRequest := inputCoherent.accuracyRequest semanticTarget
    have inputRequestPositive : 0 < inputRequest :=
      inputCoherent.accuracyRequest_pos semanticPositive
    let numerator :=
      Reduction.numerator input chart.factor
    let preparedDenominator :=
      Reduction.preparedDenominator input chart.factor
        chart.denominatorApart
    let denominatorApart :=
      (Reduction.preparedDenominatorApart input
        chart.factor chart.denominatorApart).certificate
    let outerTarget :=
      Gaussian.Process.Coherence.Basic.Coherent.divisionOuterTarget
        numerator.process preparedDenominator.process denominatorApart.lowerSq
          inputRequest
    have outerPositive : 0 < outerTarget :=
      Gaussian.Process.Coherence.Basic.Coherent.divisionOuterTarget_pos
        numerator.process preparedDenominator.process denominatorApart.positive
          inputRequestPositive
    let leftIndex := Search.firstQuarterBelow
      1 leftStart outerTarget
    have leftIndexGe : leftStart ≤ leftIndex :=
      Search.firstQuarterBelow_ge
        1 leftStart outerTarget
    have leftRequestSmall :
        Gaussian.Process.Sampling.refinementTarget leftIndex <
          outerTarget :=
      Search.firstQuarterBelow_accurate
        1 (by decide) leftStart outerTarget outerPositive
    let requestedSource := Search.firstQuarterBelow
      1 0 inputRequest
    have requestedSourceRequestSmall :
        Gaussian.Process.Sampling.refinementTarget requestedSource <
          inputRequest :=
      Search.firstQuarterBelow_accurate
        1 (by decide) 0 inputRequest inputRequestPositive
    let rightIndex :=
      Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedOutputIndexForSource
      input chart rightStart requestedSource
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := leftIndexGe
        right_ge :=
          Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedOutputIndexForSource_ge
          input chart rightStart requestedSource
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let reduced := Reduction.reduced input
            chart.factor chart.denominatorApart
          let actualState := Gaussian.Process.Sampling.stateAt
            reduced.process reduced.state leftLater
          let actualValue := Gaussian.Process.Sampling.witnessAt
            reduced.process reduced.state leftLater
          have actualPossible : reduced.process.Possible actualState actualValue :=
            Gaussian.Process.Sampling.witnessAt_possible
              reduced.process reduced.state leftLater
          rcases Sampling.reducedPossible_sources input chart actualPossible with
            ⟨x, y, xPossible, yPossible, actualEqual⟩
          have actualRequestSmall :
              Gaussian.Process.Sampling.refinementTarget leftLater <
                outerTarget :=
            (quarterRadius_antitone (by decide)
              leftOrder).trans_lt
              leftRequestSmall
          have actualAllowancesSmall :=
            Sampling.reducedStateAt_input_allowances_lt input chart inputCoherent
              reduced.state leftLater semanticTarget semanticPositive
                actualRequestSmall
          let sourceIndex := Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReducedSourceIndex
            input chart
            certificate rightLater
          have sourceOrder : requestedSource ≤ sourceIndex :=
            (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.synchronizedReduced_reachesRequestedSourceIndex
              input chart
              certificate rightStart requestedSource).trans
              (Sampling.emittedSampleIndex_mono
                (Synchronized.synchronizedReducedApproximation input chart certificate)
                rightOrder)
          have sourceRequestSmall :
              Gaussian.Process.Sampling.refinementTarget sourceIndex <
                inputRequest :=
            (quarterRadius_antitone (by decide)
              sourceOrder).trans_lt
              requestedSourceRequestSmall
          let prepared := Prepared.preparedChartInput input chart
          let z := ComplexLog.inputSample
            prepared sourceIndex
          have zPossible : input.process.Possible
              (Gaussian.Process.Sampling.stateAt input.process
                prepared.state sourceIndex) z :=
            Gaussian.Process.Sampling.witnessAt_possible
              input.process prepared.state sourceIndex
          have zPossibleStart : input.process.Possible prepared.state z :=
            ComplexLog.inputSample_possible_start
              prepared sourceIndex
          have zAllowanceSmall :
              inputCoherent.allowance
                  (Gaussian.Process.Sampling.stateAt input.process
                    prepared.state sourceIndex) < semanticTarget :=
            Gaussian.Process.Coherence.Basic.Coherent.stateAt_allowance_lt
              inputCoherent prepared.state sourceIndex semanticTarget
                semanticPositive sourceRequestSmall
          have xClose := inputCoherent.possible_close xPossible zPossible
          have yClose := inputCoherent.possible_close yPossible zPossible
          have xDistanceSmall : Data.Gaussian.Norm.Basic.normSq (x - z) < 8 * semanticTarget := by
            calc
              Data.Gaussian.Norm.Basic.normSq (x - z) ≤
                  4 * (inputCoherent.allowance actualState.1.1.2 +
                    inputCoherent.allowance
                      (Gaussian.Process.Sampling.stateAt
                        input.process prepared.state sourceIndex)) := xClose
              _ < 4 * (semanticTarget + semanticTarget) :=
                Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (Fraction.Order.Arithmetic.add_lt_add_direct
                    actualAllowancesSmall.1 zAllowanceSmall)
              _ = 8 * semanticTarget := by ring1
          have yDistanceSmall : Data.Gaussian.Norm.Basic.normSq (y - z) < 8 * semanticTarget := by
            calc
              Data.Gaussian.Norm.Basic.normSq (y - z) ≤
                  4 * (inputCoherent.allowance actualState.2.source.1.2 +
                    inputCoherent.allowance
                      (Gaussian.Process.Sampling.stateAt
                        input.process prepared.state sourceIndex)) := yClose
              _ < 4 * (semanticTarget + semanticTarget) :=
                Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                  (by decide)
                  (Fraction.Order.Arithmetic.add_lt_add_direct
                    actualAllowancesSmall.2 zAllowanceSmall)
              _ = 8 * semanticTarget := by ring1
          have distanceSmall :
              Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (y - z) < 16 *
                semanticTarget := by
            calc
              Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (y - z) <
                  8 * semanticTarget + 8 * semanticTarget :=
                Fraction.Order.Arithmetic.add_lt_add_direct
                  xDistanceSmall yDistanceSmall
              _ = 16 * semanticTarget := by ring1
          have yDenominatorPossible :
              (Reduction.denominator input
                chart.factor).process.Possible actualState.2.source
                  (chart.factor * y + 1) :=
            ⟨chart.factor * y, 1,
              ⟨chart.factor, y, rfl, yPossible, rfl⟩, rfl, rfl⟩
          have yLower : chart.denominatorApart.lowerSq ≤
              Data.Gaussian.Norm.Basic.normSq (chart.factor * y + 1) :=
            chart.denominatorApart.lower actualState.2.source
              yDenominatorPossible
          have zLower : chart.denominatorApart.lowerSq ≤
              Data.Gaussian.Norm.Basic.normSq (chart.factor * z + 1) :=
            Prepared.preparedChartInput_denominator_lower input chart certificate
              zPossibleStart
          have zAllowanceLtOne :
              inputCoherent.allowance
                  (Gaussian.Process.Sampling.stateAt input.process
                    prepared.state sourceIndex) < 1 :=
            zAllowanceSmall.trans semanticLtOne
          have allowancePlusBound :
              inputCoherent.allowance
                    (Gaussian.Process.Sampling.stateAt input.process
                      prepared.state sourceIndex) + input.process.centerBound <
                1 + input.process.centerBound :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct
              zAllowanceLtOne input.process.centerBound
          have zBound : Data.Gaussian.Norm.Basic.normSq z ≤ reducedBridgeSourceBound input :=
            by
            have possibleBound :=
              Gaussian.Process.Coherence.Basic.Coherent.possible_normSq_le
                inputCoherent zPossible
            exact (possibleBound.trans_lt
              (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide) allowancePlusBound)).le
          have asynchronous :=
            Geometry.Projective.Homography.Cayley.Bounds.asynchronousScaledReduced_input_close
              chart.factor x y z chart.denominatorApart.lowerSq
                (reducedBridgeSourceBound input)
                chart.denominatorApart.positive yLower zLower zBound
          have referenceSample :
              (Sampling.approximation
                (Synchronized.synchronizedReducedNamed input chart certificate)).sample
                  rightLater =
                Synchronized.synchronizedReducedSample input chart sourceIndex := by
            change
              (Sampling.approximation
                (Synchronized.synchronizedReducedApproximation input chart
                  certificate).toNamed).sample rightLater =
                (Synchronized.synchronizedReducedApproximation input chart
                  certificate).sample
                    (Sampling.emittedSampleIndex
                      (Synchronized.synchronizedReducedApproximation input chart
                        certificate) rightLater)
            exact Sampling.emittedSample_eq
              (Synchronized.synchronizedReducedApproximation input chart certificate)
                rightLater
          change Data.Gaussian.Norm.Basic.normSq
              (actualValue -
                (Sampling.approximation
                  (Synchronized.synchronizedReducedNamed input chart certificate)).sample
                    rightLater) < target
          rw [referenceSample]
          change Data.Gaussian.Norm.Basic.normSq
              (actualValue -
                (chart.factor * z - 1) / (chart.factor * z + 1)) < target
          rw [actualEqual]
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((chart.factor * x - 1) / (chart.factor * y + 1) -
                  (chart.factor * z - 1) / (chart.factor * z + 1)) ≤
              Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity input chart *
                (Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (y - z)) :=
                  by
              simpa only [Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity] using
                asynchronous
            _ < Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity input chart *
                (16 * semanticTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeSensitivity_pos input chart
                  certificate)
                distanceSmall
            _ = semanticTarget *
              Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient input chart
              := by
              unfold Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeCoefficient
              ring1
            _ < target :=
              Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison.reducedBridgeTarget_budget_lt input chart
                certificate positive }

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison
