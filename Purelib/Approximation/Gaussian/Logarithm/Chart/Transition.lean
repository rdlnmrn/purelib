module
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Laws
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Data.Gaussian.Basic

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Transition

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

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

/-- The finite transition from one anchored chart to another chart over the same coherent input. -/
@[expose] def transition {input : CoherentNamed}
    (source target : Anchored.AnchoredChart input) : Coherent.CoherentNamed :=
  Difference.difference (AnchoredChart.output source) (AnchoredChart.output target)

/-- Every certified finite chart transition exponentiates operationally to the exact rational unit. -/
@[expose] def exp_transition_unit {input : CoherentNamed}
    (source target : Anchored.AnchoredChart input) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Approximation.Gaussian.Logarithm.Chart.Transition.transition source target).name)
      (Named.exact 1) := by
  have exponentials : Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named target.output.name)
      (Exponential.Progressive.Range.Name.named source.output.name) :=
    NamedEquivalent.trans
      (AnchoredChart.exponential_inverse target)
      (NamedEquivalent.symm
        (AnchoredChart.exponential_inverse source))
  exact Laws.exp_difference_unit (AnchoredChart.output source) (AnchoredChart.output target) exponentials

/-- The branch discrepancy between `log(left * right)` and `log(left) + log(right)`, formed entirely from actual CCL
operations. -/
@[expose] def productBranchDiscrepancy
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput) : Coherent.CoherentNamed :=
  Difference.difference
    (CoherentNamed.add
      (AnchoredChart.output leftBranch) (AnchoredChart.output rightBranch))
    (AnchoredChart.output productBranch)

/-- Guarded logarithm multiplication law: whenever the supplied product input is operationally the actual CCL product,
the computed branch discrepancy exponentiates to exact one.

The theorem neither chooses nor completes a branch correction. -/
@[expose] def exp_productBranchDiscrepancy_unit
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : Anchored.AnchoredChart leftInput)
    (rightBranch : Anchored.AnchoredChart rightInput)
    (productBranch : Anchored.AnchoredChart productInput)
    (productEquivalent : Gaussian.Equivalence.NamedEquivalent productInput.name
      (Named.mul
        leftInput.name rightInput.name)) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Approximation.Gaussian.Logarithm.Chart.Transition.productBranchDiscrepancy leftInput rightInput productInput
          leftBranch rightBranch productBranch).name)
      (Named.exact 1) := by
  let leftLog := (AnchoredChart.output leftBranch)
  let rightLog := (AnchoredChart.output rightBranch)
  let sumLog :=
    CoherentNamed.add leftLog rightLog
  let productLog := (AnchoredChart.output productBranch)
  let leftExp := Exponential.Progressive.Range.Coherent.exp leftLog.name
  let rightExp := Exponential.Progressive.Range.Coherent.exp rightLog.name
  have sumExponential : Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named sumLog.name)
      productInput.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm
        (by
          simpa only [sumLog, leftExp, rightExp,
            CoherentNamed.add,
            Exponential.Progressive.Range.Coherent.exp] using
            Exponential.Progressive.Range.Addition.automaticExp_add leftLog rightLog))
      (NamedEquivalent.trans
        (Congruence.coherentMul_respects leftExp leftInput rightExp rightInput
          (AnchoredChart.exponential_inverse leftBranch) (AnchoredChart.exponential_inverse rightBranch))
        (NamedEquivalent.symm
          productEquivalent))
  have exponentials : Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named productLog.name)
      (Exponential.Progressive.Range.Name.named sumLog.name) :=
    NamedEquivalent.trans
      (AnchoredChart.exponential_inverse productBranch)
      (NamedEquivalent.symm
        sumExponential)
  simpa only [Approximation.Gaussian.Logarithm.Chart.Transition.productBranchDiscrepancy, sumLog, productLog, leftLog,
    rightLog] using Laws.exp_difference_unit sumLog productLog exponentials

/-- A chart's transition to itself is operationally the exact zero name. -/
@[expose] def transition_self_zero {input : CoherentNamed}
    (branch : Anchored.AnchoredChart input) :
    Gaussian.Equivalence.NamedEquivalent (Approximation.Gaussian.Logarithm.Chart.Transition.transition branch
      branch).name
      (Named.exact 0) :=
  Neg.coherentAdd_neg_right (AnchoredChart.output branch)

/-- Finite chart transitions compose additively. -/
@[expose] def transition_compose {input : CoherentNamed}
    (first second third : Anchored.AnchoredChart input) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Approximation.Gaussian.Logarithm.Chart.Transition.transition first second).name
        (Approximation.Gaussian.Logarithm.Chart.Transition.transition second third).name)
      (Approximation.Gaussian.Logarithm.Chart.Transition.transition first third).name := by
  let firstOutput := (AnchoredChart.output first)
  let secondOutput := (AnchoredChart.output second)
  let thirdOutput := (AnchoredChart.output third)
  let negativeFirst :=
    CoherentNamed.neg firstOutput
  let negativeSecond :=
    CoherentNamed.neg secondOutput
  let firstSecond := Difference.difference firstOutput secondOutput
  let secondThird := Difference.difference secondOutput thirdOutput
  let negativeSecondPlusFirstSecond :=
    CoherentNamed.add
      negativeSecond firstSecond
  let cancelledSecond :=
    CoherentNamed.add
      negativeSecond secondOutput
  let cancelledThenFirst :=
    CoherentNamed.add
      cancelledSecond negativeFirst
  let zero :=
    Coherence.exact 0
  let zeroPlusFirst :=
    CoherentNamed.add zero negativeFirst
  have swapTransitions : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        firstSecond.name secondThird.name)
      (Named.add
        secondThird.name firstSecond.name) :=
    Add.coherentAdd_comm firstSecond secondThird
  have exposeThird : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        secondThird.name firstSecond.name)
      (Named.add
        thirdOutput.name negativeSecondPlusFirstSecond.name) := by
    simpa only [secondThird, Difference.difference, negativeSecondPlusFirstSecond,
      negativeSecond,
      CoherentNamed.add,
      CoherentNamed.neg] using
      Add.coherentAdd_assoc thirdOutput negativeSecond firstSecond
  have cancelInside : Gaussian.Equivalence.NamedEquivalent negativeSecondPlusFirstSecond.name
      cancelledThenFirst.name := by
    simpa only [negativeSecondPlusFirstSecond, firstSecond, Difference.difference,
      cancelledThenFirst, cancelledSecond, negativeSecond, negativeFirst,
      CoherentNamed.add,
      CoherentNamed.neg] using
      NamedEquivalent.symm
        (Add.coherentAdd_assoc negativeSecond secondOutput negativeFirst)
  have replaceInside : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        thirdOutput.name negativeSecondPlusFirstSecond.name)
      (Named.add
        thirdOutput.name cancelledThenFirst.name) :=
    Congruence.coherentAdd_respects thirdOutput thirdOutput
      negativeSecondPlusFirstSecond cancelledThenFirst
      (NamedEquivalent.refl
        thirdOutput.name)
      cancelInside
  have cancelSecond : Gaussian.Equivalence.NamedEquivalent cancelledSecond.name zero.name := by
    simpa only [cancelledSecond, negativeSecond, zero,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_left secondOutput
  have reduceCancellation : Gaussian.Equivalence.NamedEquivalent cancelledThenFirst.name
      zeroPlusFirst.name :=
    Congruence.coherentAdd_respects cancelledSecond zero negativeFirst negativeFirst
      cancelSecond
      (NamedEquivalent.refl
        negativeFirst.name)
  have removeZero : Gaussian.Equivalence.NamedEquivalent zeroPlusFirst.name negativeFirst.name := by
    simpa only [zeroPlusFirst, zero,
      CoherentNamed.add,
      Coherence.exact] using
      Add.coherentAdd_zero_left negativeFirst
  have reduceInside : Gaussian.Equivalence.NamedEquivalent cancelledThenFirst.name
      negativeFirst.name :=
    NamedEquivalent.trans
      reduceCancellation removeZero
  have finish : Gaussian.Equivalence.NamedEquivalent
      (Named.add
        thirdOutput.name cancelledThenFirst.name)
      (Named.add
        thirdOutput.name negativeFirst.name) :=
    Congruence.coherentAdd_respects thirdOutput thirdOutput
      cancelledThenFirst negativeFirst
      (NamedEquivalent.refl
        thirdOutput.name)
      reduceInside
  exact NamedEquivalent.trans
    (by
      simpa only [Approximation.Gaussian.Logarithm.Chart.Transition.transition, firstSecond, secondThird] using
        swapTransitions)
    (NamedEquivalent.trans exposeThird
      (NamedEquivalent.trans
        replaceInside
        (NamedEquivalent.trans finish
          (NamedEquivalent.refl _))))

/-- Opposite chart transitions cancel operationally. -/
@[expose] def transition_reverse_zero {input : CoherentNamed}
    (first second : Anchored.AnchoredChart input) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Approximation.Gaussian.Logarithm.Chart.Transition.transition first second).name
        (Approximation.Gaussian.Logarithm.Chart.Transition.transition second first).name)
      (Named.exact 0) :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Transition.transition_compose first second first)
    (Approximation.Gaussian.Logarithm.Chart.Transition.transition_self_zero first)

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Transition
