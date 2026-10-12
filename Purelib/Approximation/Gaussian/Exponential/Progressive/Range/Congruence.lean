module
-- Exposed comparison fields retain the reconstructed natural bound.
public import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Halving
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Scaling
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
import Purelib.Approximation.Gaussian.Name.DyadicReduction
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.ContractiveScale
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Dyadic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Congruence

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Data.Gaussian

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

open Purelib.Approximation

/-- The total automatically range-reduced exponential transform respects finite operational equality of arbitrary
coherent progressive inputs, even when the two input processes select different range exponents. -/
@[expose] def automaticExp_respects (left right : Coherent.CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named left.name)
      (Exponential.Progressive.Range.Name.named right.name) := by
  let leftBase :=
    DyadicReduction.rangeExponent left.name
  let rightBase :=
    DyadicReduction.rangeExponent right.name
  let common := max leftBase rightBase
  let leftExtra := common - leftBase
  let rightExtra := common - rightBase
  have leftOrder : leftBase ≤ common := Purelib.Data.Nat.Order.le_max_left _ _
  have rightOrder : rightBase ≤ common := Purelib.Data.Nat.Order.le_max_right _ _
  have leftCommon : leftBase + leftExtra = common := by
    dsimp only [leftExtra]
    rw [Nat.add_comm, Purelib.Data.Nat.Subtraction.sub_add_cancel leftOrder]
  have rightCommon : rightBase + rightExtra = common := by
    dsimp only [rightExtra]
    rw [Nat.add_comm, Purelib.Data.Nat.Subtraction.sub_add_cancel rightOrder]
  let leftAutomaticInput := Exponential.Progressive.Range.Scaling.automaticScaled left
  let rightAutomaticInput := Exponential.Progressive.Range.Scaling.automaticScaled right
  let leftDomain :=
    DyadicReduction.scaledDomain left.name
  let rightDomain :=
    DyadicReduction.scaledDomain right.name
  let leftCommonInput := Dyadic.halfIterate leftExtra leftAutomaticInput
  let rightCommonInput := Dyadic.halfIterate rightExtra rightAutomaticInput
  let leftCommonDomain := Exponential.Progressive.Local.Halving.halfIterateUnitDisk leftExtra
    leftAutomaticInput leftDomain
  let rightCommonDomain := Exponential.Progressive.Local.Halving.halfIterateUnitDisk rightExtra
    rightAutomaticInput rightDomain
  let leftScaledApproximation := DyadicScale.dyadicScaledApproximation common left.name
  let rightScaledApproximation := DyadicScale.dyadicScaledApproximation common right.name
  have leftNormalized : Gaussian.Equivalence.NamedEquivalent leftCommonInput.name
      leftScaledApproximation.toNamed := by
    simpa only [leftCommonInput, leftAutomaticInput,
      leftScaledApproximation, leftCommon, leftBase] using
        Exponential.Progressive.Range.Scaling.halfIterateAutomatic_to_dyadicScaled leftExtra left
  have rightNormalized : Gaussian.Equivalence.NamedEquivalent rightCommonInput.name
      rightScaledApproximation.toNamed := by
    simpa only [rightCommonInput, rightAutomaticInput,
      rightScaledApproximation, rightCommon, rightBase] using
        Exponential.Progressive.Range.Scaling.halfIterateAutomatic_to_dyadicScaled rightExtra right
  have scaledEquivalent : Gaussian.Equivalence.NamedEquivalent
      leftScaledApproximation.toNamed rightScaledApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (ContractiveScale.contractiveScaleApproximation_respects (Dyadic.inverseDyadicAt common)
        (Dyadic.normSq_inverseDyadicAt_le_one common) equivalent)
  have commonInputEquivalent : Gaussian.Equivalence.NamedEquivalent
      leftCommonInput.name rightCommonInput.name :=
    NamedEquivalent.trans
      leftNormalized
      (NamedEquivalent.trans
        scaledEquivalent
        (NamedEquivalent.symm
          rightNormalized))
  let leftCommonLocal : Coherent.CoherentNamed :=
    { name := Exponential.Progressive.Local.Name.named
        leftCommonInput.name leftCommonDomain
      coherent := Exponential.Progressive.Local.Coherent.localExpCoherent leftCommonInput.name leftCommonDomain }
  let rightCommonLocal : Coherent.CoherentNamed :=
    { name := Exponential.Progressive.Local.Name.named
        rightCommonInput.name rightCommonDomain
      coherent := Exponential.Progressive.Local.Coherent.localExpCoherent rightCommonInput.name rightCommonDomain }
  have commonLocalEquivalent : Gaussian.Equivalence.NamedEquivalent
      leftCommonLocal.name rightCommonLocal.name :=
    Exponential.Progressive.Local.Congruence.localExpNamed_respects leftCommonDomain rightCommonDomain
      commonInputEquivalent
  have commonRestoredEquivalent : Gaussian.Equivalence.NamedEquivalent
      (Power.squareIterate common
        leftCommonLocal.name)
      (Power.squareIterate common
        rightCommonLocal.name) :=
    Congruence.squareIterate_respects common leftCommonLocal rightCommonLocal
      commonLocalEquivalent
  have leftRaise := Exponential.Progressive.Range.Addition.coherentDyadicExp_raise leftBase leftExtra
    leftAutomaticInput leftDomain
  have rightRaise := Exponential.Progressive.Range.Addition.coherentDyadicExp_raise rightBase rightExtra
    rightAutomaticInput rightDomain
  exact NamedEquivalent.trans
    (NamedEquivalent.symm
      (by simpa only [leftCommon, leftCommonInput, leftAutomaticInput,
          leftCommonLocal, leftCommonDomain, leftBase, leftDomain,
          Exponential.Progressive.Range.Scaling.automaticScaled, Exponential.Progressive.Range.Name.named]
        using leftRaise))
    (NamedEquivalent.trans
      commonRestoredEquivalent
      (by simpa only [rightCommon, rightCommonInput, rightAutomaticInput,
          rightCommonLocal, rightCommonDomain, rightBase, rightDomain,
          Exponential.Progressive.Range.Scaling.automaticScaled, Exponential.Progressive.Range.Name.named]
        using rightRaise))

/-- If every possible reading of a coherent input is already in the local unit disk, the total automatic exponential is
operationally the direct local exponential, even if its conservative initial ball selected a nonzero range exponent. -/
@[expose] def automaticExp_toLocal (input : Coherent.CoherentNamed)
    (domain : Name.UnitDisk input.name) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named input.name)
      (Exponential.Progressive.Local.Name.named input.name domain) := by
  let exponent :=
    DyadicReduction.rangeExponent input.name
  let automaticInput := Exponential.Progressive.Range.Scaling.automaticScaled input
  let automaticDomain :=
    DyadicReduction.scaledDomain input.name
  let halvedInput := Dyadic.halfIterate exponent input
  let halvedDomain := Exponential.Progressive.Local.Halving.halfIterateUnitDisk exponent input domain
  have automaticToScaled := Exponential.Progressive.Range.Scaling.automaticScaled_to_dyadicScaled input
  have halvedToScaled := Dyadic.halfIterate_to_dyadicScaled exponent input
  have inputEquivalent : Gaussian.Equivalence.NamedEquivalent
      automaticInput.name halvedInput.name :=
    NamedEquivalent.trans
      automaticToScaled
      (NamedEquivalent.symm
        halvedToScaled)
  let automaticLocal : Coherent.CoherentNamed :=
    { name := Exponential.Progressive.Local.Name.named
        automaticInput.name automaticDomain
      coherent := Exponential.Progressive.Local.Coherent.localExpCoherent automaticInput.name automaticDomain }
  let halvedLocal : Coherent.CoherentNamed :=
    { name := Exponential.Progressive.Local.Name.named
        halvedInput.name halvedDomain
      coherent := Exponential.Progressive.Local.Coherent.localExpCoherent halvedInput.name halvedDomain }
  have localEquivalent : Gaussian.Equivalence.NamedEquivalent
      automaticLocal.name halvedLocal.name :=
    Exponential.Progressive.Local.Congruence.localExpNamed_respects automaticDomain halvedDomain inputEquivalent
  have restoredEquivalent := Congruence.squareIterate_respects exponent
    automaticLocal halvedLocal localEquivalent
  have halvedToLocal := Exponential.Progressive.Range.Addition.coherentDyadicExp_raise 0 exponent input domain
  exact NamedEquivalent.trans
    (middle := Power.squareIterate exponent halvedLocal.name)
    (by simpa only [exponent, automaticInput, automaticDomain, automaticLocal,
        Exponential.Progressive.Range.Scaling.automaticScaled, Exponential.Progressive.Range.Name.named]
      using restoredEquivalent)
    (by
        simpa only [Nat.zero_add, halvedInput, halvedDomain, halvedLocal, Power.squareIterate]
          using halvedToLocal)

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Congruence
