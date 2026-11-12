module

import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Evaluation
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Cast

/-! # Operational frontend regressions at original channels and local binders -/

namespace TestPurelib.Approximation.Gaussian.OperationalEquivalence

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Cast (natCast_re natCast_im)
open Purelib.Data.Rat.Fraction.Cast (natCast_eq_fromInt fromInt)
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic (Expr)

example (first second : CoherentNamed) :
    NamedEquivalent (CoherentNamed.add first second).name (CoherentNamed.add second first).name := by
  ccl_equiv

example : ∀ first second : CoherentNamed,
    BitLaw (CoherentNamed.add first second) (CoherentNamed.add second first) := by
  ccl_equiv

example (first second third : CoherentNamed) :
    NamedEquivalent (CoherentNamed.mul first (CoherentNamed.add second third)).name
      (CoherentNamed.add (CoherentNamed.mul first second) (CoherentNamed.mul first third)).name := by
  ccl_equiv

example (input : CoherentNamed) :
    NamedEquivalent (Power.namedPower input 3).name
      (CoherentNamed.mul (CoherentNamed.mul input input) input).name := by
  ccl_equiv

example (environment : Fin 2 → Annotated) :
    NamedEquivalent ((Expr.add (.atom 0) (.atom 1)).denote environment).name
      ((Expr.add (.atom 1) (.atom 0)).denote environment).name := by
  ccl_equiv

example : NamedEquivalent
    (CoherentNamed.add (CoherentNamed.Coherence.exact 2) (CoherentNamed.Coherence.exact 3)).name
    (CoherentNamed.Coherence.exact 5).name := by
  ccl_equiv

example (_first _second : CoherentNamed) : True := by
  fail_if_success
    have : NamedEquivalent _first.name _second.name := by ccl_equiv
  trivial

example (_input : CoherentNamed) (_exponent : Nat) : True := by
  fail_if_success
    have : NamedEquivalent (Power.namedPower _input _exponent).name _input.name := by ccl_equiv
  trivial

example (first second : CoherentNamed) (same : NamedEquivalent first.name second.name) :
    NamedEquivalent (CoherentNamed.mul first (CoherentNamed.add first (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.add (CoherentNamed.mul second second) second).name := by
  ccl_equiv [same]

example (first second third : CoherentNamed)
    (firstSecond : NamedEquivalent first.name second.name)
    (secondThird : NamedEquivalent second.name third.name) :
    NamedEquivalent (CoherentNamed.add first first).name (CoherentNamed.add third third).name := by
  ccl_equiv [firstSecond, secondThird]

example (first second : CoherentNamed) (same : NamedEquivalent first.name second.name) :
    NamedEquivalent (CoherentNamed.add second second).name (CoherentNamed.add first first).name := by
  ccl_equiv [same]

example (first second : CoherentNamed)
    (forward : NamedEquivalent first.name second.name) (_backward : NamedEquivalent second.name first.name) :
    NamedEquivalent (CoherentNamed.mul first first).name (CoherentNamed.mul second second).name := by
  ccl_equiv [forward, _backward]

example : ∀ (first second : CoherentNamed) (_same : NamedEquivalent first.name second.name),
    BitLaw (CoherentNamed.add first second) (CoherentNamed.add second second) := by
  ccl_equiv [_same]

example (_first _second _third : CoherentNamed) (_same : NamedEquivalent _first.name _second.name) : True := by
  fail_if_success
    have : NamedEquivalent _first.name _third.name := by ccl_equiv [_same]
  trivial

example (_first _second : CoherentNamed) : True := by
  fail_if_success
    have : NamedEquivalent _first.name _second.name := by ccl_equiv [Nat.le_refl 0]
  trivial

example (input : CoherentNamed) (equation : PowerIdentity input 3 2) :
    NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.add (CoherentNamed.Coherence.exact 1) input)
        (CoherentNamed.add
          (CoherentNamed.add (Power.namedPower input 2) (CoherentNamed.neg input))
          (CoherentNamed.Coherence.exact 1))).name
      (CoherentNamed.Coherence.exact 3).name := by
  ccl_equiv [equation]

example (input : CoherentNamed)
    (equation : NamedEquivalent (Power.namedPower input 5).name (CoherentNamed.Coherence.exact 7).name) :
    NamedEquivalent (Power.namedPower input 10).name (CoherentNamed.Coherence.exact 49).name := by
  have scalar : (49 : Canonical) = ⟨fromInt 49, 0⟩ :=
    Purelib.Data.Gaussian.Basic.ext ((natCast_re 49).trans (natCast_eq_fromInt 49)) (natCast_im 49)
  rewrite [scalar]
  ccl_equiv [equation]

example (input : CoherentNamed)
    (equation : NamedEquivalent (CoherentNamed.Coherence.exact 3).name (Power.namedPower input 2).name) :
    NamedEquivalent (Power.namedPower input 4).name (CoherentNamed.Coherence.exact 9).name := by
  ccl_equiv [equation]

example (original retained : CoherentNamed) (same : NamedEquivalent original.name retained.name)
    (equation : PowerIdentity original 3 2) :
    NamedEquivalent (Power.namedPower retained 6).name (CoherentNamed.Coherence.exact 4).name := by
  ccl_equiv [same, equation]

example : ∀ (input : CoherentNamed) (_equation : PowerIdentity input 3 2),
    BitLaw (Power.namedPower input 3) (CoherentNamed.Coherence.exact 2) := by
  ccl_equiv [_equation]

example (_input : CoherentNamed) (_degree : Nat) (_equation : PowerIdentity _input _degree 2) : True := by
  fail_if_success
    have : NamedEquivalent (Power.namedPower _input 3).name (CoherentNamed.Coherence.exact 2).name := by
      ccl_equiv [_equation]
  trivial

section ComparisonReduction

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence (ApproximationData)
open Purelib.Data.Rat.Fraction (Rational)

/-- Reversal retains the complete original comparison data at all inputs, including both paid starts. -/
example {left right : ApproximationData} (equivalent : Equivalent left right)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target) :
    let original := equivalent.compare leftStart rightStart target positive
    let reversed := equivalent.symm.compare rightStart leftStart target positive
    reversed =
      { leftIndex := original.rightIndex
        rightIndex := original.leftIndex
        left_ge := original.right_ge
        right_ge := original.left_ge
        close := reversed.close } := rfl

/-- Transitivity retains the original complete comparison result and its sequential middle request at every input. -/
example {left middle right : ApproximationData} (first : Equivalent left middle) (second : Equivalent middle right)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target) :
    let quarterPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let leftMiddle := first.compare leftStart 0 (target / 4) quarterPositive
    let middleRight := second.compare leftMiddle.rightIndex rightStart (target / 4) quarterPositive
    let composed := (first.trans second).compare leftStart rightStart target positive
    composed =
      { leftIndex := leftMiddle.leftIndex
        rightIndex := middleRight.rightIndex
        left_ge := leftMiddle.left_ge
        right_ge := middleRight.right_ge
        close := composed.close } := rfl

/-- Constant equality preserves the complete original immediate observation at both requested starts. -/
example (left right : ApproximationData) (value : Canonical)
    (leftSample : ∀ index, left.sample index = value) (rightSample : ∀ index, right.sample index = value)
    (leftStart rightStart : Nat) (target : Rational) (positive : 0 < target) :
    let compared := (Equivalent.of_constant_samples left right value leftSample rightSample).compare
      leftStart rightStart target positive
    compared =
      { leftIndex := leftStart
        rightIndex := rightStart
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := compared.close } := rfl

open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Data.Rat.Fraction.Order

/-- Sum congruence retains its complete original paired observation and quarter requests for every input. -/
example {leftOne leftTwo rightOne rightTwo : Basic.Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo) (rightEquivalent : NamedEquivalent rightOne rightTwo)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    let smallPositive := Field.div_pos_direct positive (by decide : (0 : Rational) < 4)
    let leftComparison := leftEquivalent.compare firstStart secondStart (target / 4) smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart (target / 4) smallPositive
    let compared := (Sum.Congruence.sampledSumApproximation_respects leftEquivalent rightEquivalent).compare
      firstStart secondStart target positive
    compared =
      { leftIndex := max leftComparison.leftIndex rightComparison.leftIndex
        rightIndex := max leftComparison.rightIndex rightComparison.rightIndex
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := compared.close } := rfl

/-- Product congruence retains both original magnitude-dependent requests and its whole paired comparison. -/
example {leftOne leftTwo rightOne rightTwo : Basic.Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo) (rightEquivalent : NamedEquivalent rightOne rightTwo)
    (firstStart secondStart : Nat) (target : Rational) (positive : 0 < target) :
    let payment := Multiplication.Bridge.approximationMulBridgeTarget
      (Sampling.approximation rightOne) (Sampling.approximation leftTwo) target
    let paid := Multiplication.Bridge.approximationMulBridgeTarget_pos
      (Sampling.approximation rightOne) (Sampling.approximation leftTwo) positive
    let leftComparison := leftEquivalent.compare firstStart secondStart payment paid
    let rightComparison := rightEquivalent.compare firstStart secondStart payment paid
    let compared := (Product.Congruence.sampledProductApproximation_respects leftEquivalent rightEquivalent).compare
      firstStart secondStart target positive
    compared =
      { leftIndex := max leftComparison.leftIndex rightComparison.leftIndex
        rightIndex := max leftComparison.rightIndex rightComparison.rightIndex
        left_ge := compared.left_ge
        right_ge := compared.right_ge
        close := compared.close } := rfl

end ComparisonReduction

section DenominatorPreparationReduction

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division

/-- State-based preparation retains its complete original denominator, apartness and operational comparison. -/
example {channel : CoherentNamed} (state : Name.Coherent.Refinement.State channel)
    (evidence : Process.Apart.Possible.PossibleApart
      (Process.Based.based channel.name.process state.source)) :
    Prepared.ofEvidence state evidence =
      { denominator := Partial.Preparation.preparedDenominator state evidence
        apart := Partial.Preparation.preparedApart state evidence
        equivalent := Partial.Equivalence.preparedDenominatorEquivalent state evidence } := rfl

end DenominatorPreparationReduction

end TestPurelib.Approximation.Gaussian.OperationalEquivalence
