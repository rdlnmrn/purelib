module
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
public import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Process.Coherence.Apart
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Division
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation.Gaussian.Logarithm (Chart)
open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

/-- A charted complex logarithm is coherent whenever its explicit additive branch-correction name is coherent. -/
def complexLogNamedCoherent (input :
  Named)
    (chart : Chart input)
    (correctionCoherent : Gaussian.Process.Coherence.Basic.Coherent chart.correction.process) :
    Gaussian.Process.Coherence.Basic.Coherent (Name.named input chart).process :=
  Gaussian.Process.Coherence.Basic.Coherent.add
    (Coherent.localComplexLogCoherent
      (Reduction.reduced input chart.factor
        chart.denominatorApart) chart.reducedDisk)
    correctionCoherent

end Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

end

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

/-! ## Finite coherence of the stateful chart arithmetic -/

/-- Scaling a coherent input by the displayed rational chart factor remains coherent. -/
def scaledCoherent (input : Named)
  (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Reduction.scaled input chart.factor).process :=
  Gaussian.Process.Coherence.Basic.Coherent.mul
    (Gaussian.Process.Coherence.Basic.Coherent.exact chart.factor)
    inputCoherent

/-- The stateful chart numerator inherits finite coherence. -/
def numeratorCoherent (input : Named)
  (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Reduction.numerator input chart.factor).process :=
  Gaussian.Process.Coherence.Basic.Coherent.sub
    (scaledCoherent input chart inputCoherent)
    (Gaussian.Process.Coherence.Basic.Coherent.exact 1)

/-- The unprepared stateful chart denominator inherits finite coherence. -/
def denominatorCoherent (input :
  Named) (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Reduction.denominator input chart.factor).process :=
  Gaussian.Process.Coherence.Basic.Coherent.add
    (scaledCoherent input chart inputCoherent)
    (Gaussian.Process.Coherence.Basic.Coherent.exact 1)

/-- One finite whole-ball apartness preparation preserves denominator coherence. -/
def preparedDenominatorCoherent (input :
  Named) (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Reduction.preparedDenominator input chart.factor
        chart.denominatorApart).process :=
  Gaussian.Process.Coherence.Basic.Coherent.apartify
    (denominatorCoherent input chart inputCoherent)
      chart.denominatorApart

/-- The actual independently sampled reduced quotient has a finite coherence certificate obtained by arithmetic closure
and its displayed denominator apartness. -/
def reducedCoherent (input : Named)
  (chart : Chart input)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process) :
    Gaussian.Process.Coherence.Basic.Coherent
      (Reduction.reduced input chart.factor
        chart.denominatorApart).process :=
  Gaussian.Process.Coherence.Basic.Coherent.div
    (numeratorCoherent input chart inputCoherent)
    (preparedDenominatorCoherent input chart inputCoherent)
    (Reduction.preparedDenominatorApart
      input chart.factor chart.denominatorApart).certificate

/-! ## Actual arbitrary-input exponential/logarithm composition -/

/-- The actual local-output and correction inputs of a chart, packaged with their finite coherence certificates. -/
def localOutputCoherentNamed (input :
  Named) (chart : Chart input) :
    Coherent.CoherentNamed :=
  { name := Name.localOutput input chart
    coherent :=
      Coherent.localComplexLogCoherent
        (Reduction.reduced input chart.factor
          chart.denominatorApart) chart.reducedDisk }

/-- Package the original chart correction name with the supplied coherence certificate for that exact process. -/
def correctionCoherentNamed (input :
  Named) (chart : Chart input)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process) :
    Coherent.CoherentNamed :=
  { name := chart.correction
    coherent := correctionCoherent }
end Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

end

section
@[expose] public section

/-!
# Operational congruence for anchored logarithm charts

Two finite chart constructions may use different based process state types and
different proofs of denominator and disk safety.  When their inputs are
operationally equivalent and they retain the same rational factor and
operationally equivalent branch corrections, their actual charted logarithm
outputs are operationally equivalent.

This is the schedule-coherence bridge needed by retryable anchored logarithm
preflight.  It compares finite programs directly; it does not identify
independently selected branches from equality of their exponentials.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

/-- Coherent packaging of the chart numerator. -/
def numeratorName (input : Coherent.CoherentNamed)
  (branch : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed where
  name := Reduction.numerator input.name branch.chart.factor
  coherent := numeratorCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the unprepared chart denominator. -/
def denominatorName (input : Coherent.CoherentNamed)
  (branch : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed where
  name := Reduction.denominator input.name branch.chart.factor
  coherent := denominatorCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the chart's actual apartified denominator. -/
def preparedDenominatorName (input :
  Coherent.CoherentNamed)
    (branch : Anchored.AnchoredChart input) : Coherent.CoherentNamed :=
  CoherentNamed.apartify
    (denominatorName input branch) branch.chart.denominatorApart

/-- Coherent packaging of the independently sampled reduced quotient. -/
def reducedName (input : Coherent.CoherentNamed) (branch
  : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed where
  name := Reduction.reduced input.name branch.chart.factor
    branch.chart.denominatorApart
  coherent := reducedCoherent
    input.name branch.chart input.coherent

/-- Coherent packaging of the local logarithm before adding its branch correction. -/
def localOutputName (input : Coherent.CoherentNamed)
  (branch : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed where
  name := Name.localOutput input.name branch.chart
  coherent := Coherent.localComplexLogCoherent
    (Reduction.reduced input.name branch.chart.factor
      branch.chart.denominatorApart) branch.chart.reducedDisk

/-- Coherent packaging of the explicitly anchored correction. -/
def correctionName {input : Coherent.CoherentNamed}
  (branch : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed where
  name := branch.chart.correction
  coherent := branch.correctionCoherent
end Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent

end
