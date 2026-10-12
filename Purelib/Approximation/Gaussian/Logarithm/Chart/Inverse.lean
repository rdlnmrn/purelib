module
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Comparison
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Reconstruction
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction.Synchronized
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Law
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Scale
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Inverse

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Logarithm
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
open Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
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

/-- The total exponential of a charted logarithm is operationally the product of its local-output exponential and
correction exponential.

The chart correction retains its own finite process-coherence certificate. -/
@[expose] def actualExp_chartedLog_split (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      (Named.mul
        (Exponential.Progressive.Range.Name.named
          (Name.localOutput input chart))
        (Exponential.Progressive.Range.Name.named chart.correction)) :=
  NamedEquivalent.symm
    (Exponential.Progressive.Range.Addition.automaticExp_add
      (Coherent.localOutputCoherentNamed input chart)
      (Coherent.correctionCoherentNamed input chart correctionCoherent))

/-- An anchored branch certificate replaces the correction exponential in the actual product by the exact displayed
reciprocal chart factor. -/
@[expose] def actualExp_chartedLog_to_anchoredProduct (input : Gaussian.Name.Basic.Named)
    (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      (Named.mul
        (Exponential.Progressive.Range.Name.named
          (Name.localOutput input chart))
        (Named.exact
          (1 / chart.factor))) := by
  let localOutput := Coherent.localOutputCoherentNamed input chart
  let correction := Coherent.correctionCoherentNamed input chart correctionCoherent
  let localExponential :=
    Exponential.Progressive.Range.Coherent.exp localOutput.name
  let correctionExponential :=
    Exponential.Progressive.Range.Coherent.exp correction.name
  let inverseFactor :=
    Coherence.exact
      (1 / chart.factor)
  have productEquivalent : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        localExponential.name correctionExponential.name)
      (Named.mul
        localExponential.name inverseFactor.name) :=
    Congruence.coherentMul_respects
      localExponential localExponential correctionExponential inverseFactor
      (NamedEquivalent.refl
        localExponential.name)
      certificate.correction_exponential
  exact NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_split input chart correctionCoherent)
    productEquivalent

/-- The anchored local product has no remaining transcendental content: it is operationally the explicit finite Möbius
reconstruction of the reduced chart readings, scaled by the displayed reciprocal chart factor. -/
@[expose] def anchoredLocalProduct_to_scaledChart (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Exponential.Progressive.Range.Name.named
          (Name.localOutput input chart))
        (Named.exact
          (1 / chart.factor)))
      (Scale.scaledDynamicLocalExpLogChartApproximation
          (Reduction.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed :=
  Law.automaticExpLocalComplexLog_mulExact_toScaledChart
      (Reduction.reduced input chart.factor
        chart.denominatorApart)
      chart.reducedDisk (1 / chart.factor)

/-- The actual exponential of an anchored charted logarithm reaches a wholly rational finite reconstruction program. -/
@[expose] def actualExp_chartedLog_to_scaledChart (input : Gaussian.Name.Basic.Named)
    (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      (Scale.scaledDynamicLocalExpLogChartApproximation
          (Reduction.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_to_anchoredProduct input chart certificate
      correctionCoherent)
    (Approximation.Gaussian.Logarithm.Chart.Inverse.anchoredLocalProduct_to_scaledChart input chart)

/-- Factored sufficiency interface: a finite operational proof of the rational Möbius reconstruction completes the
arbitrary-input global inverse.

The unconditional construction below supplies this hypothesis. -/
@[expose] def actualExp_chartedLog_named_equivalent_of_scaledChart
    (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process)
    (scaledChartReconstructs : Gaussian.Equivalence.NamedEquivalent
      (Scale.scaledDynamicLocalExpLogChartApproximation
          (Reduction.reduced input chart.factor
            chart.denominatorApart)
          chart.reducedDisk (1 / chart.factor)).toNamed
      input) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      input :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_to_scaledChart input chart certificate
      correctionCoherent)
    scaledChartReconstructs

/-- A synchronized reduced reference may be used to discharge the last rational resampling step.

Möbius sensitivity transports operational equality from the actual stateful quotient to the reference before its scaled
chart is identified with the original input. -/
@[expose] def actualExp_chartedLog_named_equivalent_of_reducedReference
    (input reference : Gaussian.Name.Basic.Named) (chart : Chart input)
    (referenceDisk :
      Domain.Disk reference)
    (certificate : Branch.BranchCertificate input chart)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process)
    (reducedEquivalent : Gaussian.Equivalence.NamedEquivalent
      (Reduction.reduced input chart.factor
        chart.denominatorApart)
      reference)
    (referenceReconstructs : Gaussian.Equivalence.NamedEquivalent
      (Scale.scaledDynamicLocalExpLogChartApproximation
        reference referenceDisk (1 / chart.factor)).toNamed
      input) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      input := by
  have reconstructedEquivalent :=
    Scale.scaledDynamicLocalExpLogChartNamed_respects
        chart.reducedDisk referenceDisk (1 / chart.factor) reducedEquivalent
  exact NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_to_scaledChart input chart certificate
      correctionCoherent)
    (NamedEquivalent.trans
      reconstructedEquivalent referenceReconstructs)

/-- Factored synchronized-reference interface accepting the finite comparison from the original independently sampled
quotient as an explicit input.

The comparison is constructed below. -/
@[expose] def actualExp_chartedLog_named_equivalent_of_synchronizedReduced
    (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process)
    (reducedEquivalent : Gaussian.Equivalence.NamedEquivalent
      (Reduction.reduced input chart.factor
        chart.denominatorApart)
      (Synchronized.synchronizedReducedNamed input chart certificate)) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      input :=
  Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_named_equivalent_of_reducedReference
    input (Synchronized.synchronizedReducedNamed input chart certificate) chart
    (Reconstruction.synchronizedReducedDisk input chart certificate) certificate
    correctionCoherent reducedEquivalent
    (Reconstruction.synchronizedScaledChart_reconstructsInput
      input chart certificate inputCoherent)

/-- Full arbitrary-input anchored exponential--logarithm inverse.

Every hypothesis is finite operational data: input and correction coherence, the displayed chart, and its anchored
branch certificate. -/
@[expose] def actualExp_chartedLog_named_equivalent (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) (certificate : Branch.BranchCertificate input chart)
    (inputCoherent :
      Gaussian.Process.Coherence.Basic.Coherent input.process)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      input :=
  Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_named_equivalent_of_synchronizedReduced
    input chart certificate inputCoherent correctionCoherent
      (Comparison.reduced_equivalent_synchronizedReduced
        input chart certificate inputCoherent)

/-- Alternative factored sufficiency interface: once the anchored product is related to the original input process, the
actual global exponential/logarithm round trip follows immediately. -/
@[expose] def actualExp_chartedLog_named_equivalent_of_anchoredProduct
    (input : Gaussian.Name.Basic.Named) (chart : Chart input)
    (certificate : Branch.BranchCertificate input chart)
    (correctionCoherent :
      Gaussian.Process.Coherence.Basic.Coherent
        chart.correction.process)
    (anchoredLocalInverse : Gaussian.Equivalence.NamedEquivalent
      (Named.mul
        (Exponential.Progressive.Range.Name.named
          (Name.localOutput input chart))
        (Named.exact
          (1 / chart.factor)))
      input) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named
        (Name.named input chart))
      input :=
  NamedEquivalent.trans
    (Approximation.Gaussian.Logarithm.Chart.Inverse.actualExp_chartedLog_to_anchoredProduct input chart certificate
      correctionCoherent)
    anchoredLocalInverse

end

public section

/-!
# The locally aligned logarithm--exponential inverse

Exponentiation forgets logarithm-branch information.  Consequently the
reverse inverse cannot be global.  The finite datum that distinguishes the
desired local branch is that its computed logarithm minus the supplied input
is operationally the exact zero name, rather than merely having unit
exponential.  From that branch-alignment certificate, ordinary proved CCL
field laws reconstruct the desired equality.

This module makes the unavoidable side condition explicit.  It does not use
an integer branch index, a completed `2πi`, or a global logarithm.
-/

/-- On the explicitly zero-aligned local branch, computing the logarithm of the actual CCL exponential returns the
original coherent CCL input. -/
@[expose] def logarithm_exponential_inverse (input : CoherentNamed)
    (branch : Anchored.AnchoredChart (Exponential.Progressive.Range.Coherent.exp input.name))
    (alignment : Difference.LocalAlignment input (AnchoredChart.output branch)) :
    Gaussian.Equivalence.NamedEquivalent (AnchoredChart.output branch).name input.name := by
  let negativeInput :=
    CoherentNamed.neg input
  let discrepancy :=
    Difference.difference input (AnchoredChart.output branch)
  let zero :=
    Coherence.exact 0
  let discrepancyPlusInput :=
    CoherentNamed.add discrepancy input
  let zeroPlusInput :=
    CoherentNamed.add zero input
  let cancelled :=
    CoherentNamed.add
      negativeInput input
  let branchPlusCancelled :=
    CoherentNamed.add
      (AnchoredChart.output branch) cancelled
  have reassociate : Gaussian.Equivalence.NamedEquivalent discrepancyPlusInput.name
      branchPlusCancelled.name := by
    simpa only [discrepancyPlusInput, discrepancy, negativeInput,
      branchPlusCancelled, cancelled,
      Difference.difference,
      CoherentNamed.add,
      CoherentNamed.neg] using
      Add.coherentAdd_assoc (AnchoredChart.output branch) negativeInput input
  have cancelInput : Gaussian.Equivalence.NamedEquivalent cancelled.name zero.name := by
    simpa only [cancelled, negativeInput, zero,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_left input
  have replaceCancelled : Gaussian.Equivalence.NamedEquivalent branchPlusCancelled.name
      (CoherentNamed.add
        (AnchoredChart.output branch) zero).name :=
    Congruence.coherentAdd_respects
      (AnchoredChart.output branch) (AnchoredChart.output branch) cancelled zero
      (NamedEquivalent.refl
        (AnchoredChart.output branch).name) cancelInput
  have removeZero : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        (AnchoredChart.output branch) zero).name (AnchoredChart.output branch).name :=
    Add.coherentAdd_zero_right (AnchoredChart.output branch)
  have discrepancyPlusInput_to_branch :
      Gaussian.Equivalence.NamedEquivalent discrepancyPlusInput.name (AnchoredChart.output branch).name :=
    NamedEquivalent.trans reassociate
      (NamedEquivalent.trans
        replaceCancelled removeZero)
  have alignmentProof : Gaussian.Equivalence.NamedEquivalent discrepancy.name zero.name := by
    simpa only [Difference.LocalAlignment, discrepancy, zero,
      Coherence.exact] using
      alignment
  have replaceDiscrepancy : Gaussian.Equivalence.NamedEquivalent discrepancyPlusInput.name
      zeroPlusInput.name :=
    Congruence.coherentAdd_respects
      discrepancy zero input input alignmentProof
      (NamedEquivalent.refl input.name)
  have removeLeadingZero : Gaussian.Equivalence.NamedEquivalent zeroPlusInput.name input.name := by
    simpa only [zeroPlusInput, zero,
      CoherentNamed.add,
      Coherence.exact] using
      Add.coherentAdd_zero_left input
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      discrepancyPlusInput_to_branch)
    (NamedEquivalent.trans
      replaceDiscrepancy removeLeadingZero)

end

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Inverse
