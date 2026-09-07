import CCL.Transcendental.ComplexLogCorrectness
import CCL.Arithmetic.OperationalFieldLaws

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

namespace CCL.LogBranchCalculus

abbrev Named := CCL.ProgressiveTransducer.Named
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Chart := CCL.ComplexLogChart.Chart
abbrev BranchCertificate :=
  CCL.ComplexLogCorrectness.BranchCertificate

open CCL.TranscendentalCoherence
open CCL.OperationalFieldLaws

/-- One certified logarithm branch over a coherent CCL input. -/
structure AnchoredChart (input : CoherentNamed) where
  chart : Chart input.name
  certificate : BranchCertificate input.name chart
  correctionCoherent :
    CCL.ProgressiveCoherence.Coherent chart.correction.process

namespace AnchoredChart

/-- The actual charted-logarithm CCL process with its finite coherence
sidecar. -/
def output {input : CoherentNamed} (branch : AnchoredChart input) :
    CoherentNamed :=
  { name := CCL.ComplexLogChart.named input.name branch.chart
    coherent :=
      CCL.TranscendentalCoherence.complexLogNamedCoherent
        input.name branch.chart branch.correctionCoherent }

/-- Exponentiating the actual chart output reconstructs the original input
through finite operational equality. -/
def exponential_inverse {input : CoherentNamed}
    (branch : AnchoredChart input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named branch.output.name)
      input.name :=
  CCL.ComplexLogCorrectness.actualExp_chartedLog_named_equivalent
    input.name branch.chart branch.certificate input.coherent
      branch.correctionCoherent

end AnchoredChart

/-- Operational difference `right - left`, represented as actual addition
and negation so all later laws use the proved CCL arithmetic interface. -/
def difference (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add right
    (CCL.ProgressiveCoherence.CoherentNamed.neg left)

/-- If two coherent names have operationally equivalent exponentials, then
the exponential of their finite CCL difference is operationally exact one. -/
def exp_difference_unit (left right : CoherentNamed)
    (exponentials : NamedEquivalent
      (CCL.ProgressiveExpRange.named right.name)
      (CCL.ProgressiveExpRange.named left.name)) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (difference left right).name)
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  let negativeLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.neg left
  let rightExp := CCL.TranscendentalCoherence.exp right.name
  let leftExp := CCL.TranscendentalCoherence.exp left.name
  let negativeLeftExp :=
    CCL.TranscendentalCoherence.exp negativeLeft.name
  have products : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        rightExp.name negativeLeftExp.name)
      (CCL.ProgressiveTransducer.Named.mul
        leftExp.name negativeLeftExp.name) :=
    coherentMul_respects rightExp leftExp negativeLeftExp negativeLeftExp
      exponentials
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        negativeLeftExp.name)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (by
        simpa only [difference, negativeLeft, rightExp, negativeLeftExp,
          CCL.ProgressiveCoherence.CoherentNamed.add,
          CCL.ProgressiveCoherence.CoherentNamed.neg,
          CCL.TranscendentalCoherence.exp] using
          automaticExp_add right negativeLeft))
    (CCL.OperationalEquivalence.NamedEquivalent.trans products
      (automaticExp_mul_neg left))

/-- The finite transition from one anchored chart to another chart over the
same coherent input. -/
def transition {input : CoherentNamed}
    (source target : AnchoredChart input) : CoherentNamed :=
  difference source.output target.output

/-- Every certified finite chart transition exponentiates operationally to
the exact rational unit. -/
def exp_transition_unit {input : CoherentNamed}
    (source target : AnchoredChart input) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (transition source target).name)
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  have exponentials : NamedEquivalent
      (CCL.ProgressiveExpRange.named target.output.name)
      (CCL.ProgressiveExpRange.named source.output.name) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      target.exponential_inverse
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        source.exponential_inverse)
  exact exp_difference_unit source.output target.output exponentials

/-- The branch discrepancy between `log(left * right)` and
`log(left) + log(right)`, formed entirely from actual CCL operations. -/
def productBranchDiscrepancy
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput) : CoherentNamed :=
  difference
    (CCL.ProgressiveCoherence.CoherentNamed.add
      leftBranch.output rightBranch.output)
    productBranch.output

/-- Guarded logarithm multiplication law: whenever the supplied product
input is operationally the actual CCL product, the computed branch
discrepancy exponentiates to exact one.  The theorem neither chooses nor
completes a branch correction. -/
def exp_productBranchDiscrepancy_unit
    (leftInput rightInput productInput : CoherentNamed)
    (leftBranch : AnchoredChart leftInput)
    (rightBranch : AnchoredChart rightInput)
    (productBranch : AnchoredChart productInput)
    (productEquivalent : NamedEquivalent productInput.name
      (CCL.ProgressiveTransducer.Named.mul
        leftInput.name rightInput.name)) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (productBranchDiscrepancy leftInput rightInput productInput
          leftBranch rightBranch productBranch).name)
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  let leftLog := leftBranch.output
  let rightLog := rightBranch.output
  let sumLog :=
    CCL.ProgressiveCoherence.CoherentNamed.add leftLog rightLog
  let productLog := productBranch.output
  let leftExp := CCL.TranscendentalCoherence.exp leftLog.name
  let rightExp := CCL.TranscendentalCoherence.exp rightLog.name
  have sumExponential : NamedEquivalent
      (CCL.ProgressiveExpRange.named sumLog.name)
      productInput.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (by
          simpa only [sumLog, leftExp, rightExp,
            CCL.ProgressiveCoherence.CoherentNamed.add,
            CCL.TranscendentalCoherence.exp] using
            automaticExp_add leftLog rightLog))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (coherentMul_respects leftExp leftInput rightExp rightInput
          leftBranch.exponential_inverse rightBranch.exponential_inverse)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          productEquivalent))
  have exponentials : NamedEquivalent
      (CCL.ProgressiveExpRange.named productLog.name)
      (CCL.ProgressiveExpRange.named sumLog.name) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      productBranch.exponential_inverse
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        sumExponential)
  simpa only [productBranchDiscrepancy, sumLog, productLog, leftLog,
    rightLog] using exp_difference_unit sumLog productLog exponentials

/-- A chart's transition to itself is operationally the exact zero name. -/
def transition_self_zero {input : CoherentNamed}
    (branch : AnchoredChart input) :
    NamedEquivalent (transition branch branch).name
      (CCL.ProgressiveTransducer.Named.exact 0) :=
  coherentAdd_neg_right branch.output

/-- Finite chart transitions compose additively. -/
def transition_compose {input : CoherentNamed}
    (first second third : AnchoredChart input) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (transition first second).name
        (transition second third).name)
      (transition first third).name := by
  let firstOutput := first.output
  let secondOutput := second.output
  let thirdOutput := third.output
  let negativeFirst :=
    CCL.ProgressiveCoherence.CoherentNamed.neg firstOutput
  let negativeSecond :=
    CCL.ProgressiveCoherence.CoherentNamed.neg secondOutput
  let firstSecond := difference firstOutput secondOutput
  let secondThird := difference secondOutput thirdOutput
  let negativeSecondPlusFirstSecond :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      negativeSecond firstSecond
  let cancelledSecond :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      negativeSecond secondOutput
  let cancelledThenFirst :=
    CCL.ProgressiveCoherence.CoherentNamed.add
      cancelledSecond negativeFirst
  let zero :=
    CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let zeroPlusFirst :=
    CCL.ProgressiveCoherence.CoherentNamed.add zero negativeFirst
  have swapTransitions : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        firstSecond.name secondThird.name)
      (CCL.ProgressiveTransducer.Named.add
        secondThird.name firstSecond.name) :=
    coherentAdd_comm firstSecond secondThird
  have exposeThird : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        secondThird.name firstSecond.name)
      (CCL.ProgressiveTransducer.Named.add
        thirdOutput.name negativeSecondPlusFirstSecond.name) := by
    simpa only [secondThird, difference, negativeSecondPlusFirstSecond,
      negativeSecond,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg] using
      coherentAdd_assoc thirdOutput negativeSecond firstSecond
  have cancelInside : NamedEquivalent negativeSecondPlusFirstSecond.name
      cancelledThenFirst.name := by
    simpa only [negativeSecondPlusFirstSecond, firstSecond, difference,
      cancelledThenFirst, cancelledSecond, negativeSecond, negativeFirst,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg] using
      CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentAdd_assoc negativeSecond secondOutput negativeFirst)
  have replaceInside : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        thirdOutput.name negativeSecondPlusFirstSecond.name)
      (CCL.ProgressiveTransducer.Named.add
        thirdOutput.name cancelledThenFirst.name) :=
    coherentAdd_respects thirdOutput thirdOutput
      negativeSecondPlusFirstSecond cancelledThenFirst
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        thirdOutput.name)
      cancelInside
  have cancelSecond : NamedEquivalent cancelledSecond.name zero.name := by
    simpa only [cancelledSecond, negativeSecond, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_neg_left secondOutput
  have reduceCancellation : NamedEquivalent cancelledThenFirst.name
      zeroPlusFirst.name :=
    coherentAdd_respects cancelledSecond zero negativeFirst negativeFirst
      cancelSecond
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        negativeFirst.name)
  have removeZero : NamedEquivalent zeroPlusFirst.name negativeFirst.name := by
    simpa only [zeroPlusFirst, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_zero_left negativeFirst
  have reduceInside : NamedEquivalent cancelledThenFirst.name
      negativeFirst.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      reduceCancellation removeZero
  have finish : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        thirdOutput.name cancelledThenFirst.name)
      (CCL.ProgressiveTransducer.Named.add
        thirdOutput.name negativeFirst.name) :=
    coherentAdd_respects thirdOutput thirdOutput
      cancelledThenFirst negativeFirst
      (CCL.OperationalEquivalence.NamedEquivalent.refl
        thirdOutput.name)
      reduceInside
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [transition, firstSecond, secondThird] using swapTransitions)
    (CCL.OperationalEquivalence.NamedEquivalent.trans exposeThird
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        replaceInside
        (CCL.OperationalEquivalence.NamedEquivalent.trans finish
          (CCL.OperationalEquivalence.NamedEquivalent.refl _))))

/-- Opposite chart transitions cancel operationally. -/
def transition_reverse_zero {input : CoherentNamed}
    (first second : AnchoredChart input) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (transition first second).name
        (transition second first).name)
      (CCL.ProgressiveTransducer.Named.exact 0) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (transition_compose first second first)
    (transition_self_zero first)

/-- Sum a finite sequence of explicit chart transitions.  The recursion is
on the displayed finite list only. -/
def transitionChain {input : CoherentNamed} :
    AnchoredChart input → List (AnchoredChart input) → CoherentNamed
  | _start, [] =>
      CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | start, next :: rest =>
      CCL.ProgressiveCoherence.CoherentNamed.add
        (transition start next) (transitionChain next rest)

/-- Every finite chart-transition chain has unit exponential.  This is the
finite monodromy statement: it does not identify the chain with a completed
multiple of any non-rational constant. -/
def exp_transitionChain_unit {input : CoherentNamed} :
    (start : AnchoredChart input) → (rest : List (AnchoredChart input)) →
    NamedEquivalent
      (CCL.ProgressiveExpRange.named
        (transitionChain start rest).name)
      (CCL.ProgressiveTransducer.Named.exact 1)
  | _start, [] => by
      simpa only [transitionChain,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        automaticExp_zero
  | start, next :: rest => by
      let head := transition start next
      let tail := transitionChain next rest
      let headExp := CCL.TranscendentalCoherence.exp head.name
      let tailExp := CCL.TranscendentalCoherence.exp tail.name
      let one :=
        CCL.ProgressiveCoherence.CoherentNamed.exact 1
      have productToOne : NamedEquivalent
          (CCL.ProgressiveTransducer.Named.mul
            headExp.name tailExp.name)
          (CCL.ProgressiveTransducer.Named.mul
            one.name one.name) :=
        coherentMul_respects headExp one tailExp one
          (exp_transition_unit start next)
          (exp_transitionChain_unit next rest)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (by
            simpa only [transitionChain, head, tail, headExp, tailExp,
              CCL.ProgressiveCoherence.CoherentNamed.add,
              CCL.TranscendentalCoherence.exp] using
              automaticExp_add head tail))
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          productToOne
          (by
            simpa only [one,
              CCL.ProgressiveCoherence.CoherentNamed.exact] using
              coherentMul_one_right one))

end CCL.LogBranchCalculus
