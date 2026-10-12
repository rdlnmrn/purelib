module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Bounds
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
public import Purelib.Approximation.Gaussian.Name.DyadicReduction
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Dyadic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Coherence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Scaling

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat

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

/-- The actual automatically selected scaled input, with its coherence certificate. -/
@[expose] def automaticScaled (input : Coherent.CoherentNamed) : Coherent.CoherentNamed :=
  { name := DyadicReduction.scaledInput input.name
    coherent :=
      Gaussian.Process.Coherence.Basic.Coherent.mul
        (Gaussian.Process.Coherence.Basic.Coherent.exact
          (DyadicReduction.inverseDyadic input.name))
        input.coherent }

/-- The automatically selected scaling factor is exactly the inverse dyadic at the retained range exponent. -/
theorem automaticScaled_inverse_eq (input : Gaussian.Name.Basic.Named) :
    DyadicReduction.inverseDyadic input =
      Dyadic.inverseDyadicAt
        (DyadicReduction.rangeExponent input) :=
  rfl

/-- The actual automatic scaling process is operationally its explicit inverse-dyadic sampler. -/
@[expose] def automaticScaled_to_dyadicScaled (input : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled input).name
      (DyadicScale.dyadicScaledApproximation
        (DyadicReduction.rangeExponent input.name)
        input.name).toNamed := by
  let scale := Coherence.exact
    (DyadicReduction.inverseDyadic input.name)
  let product := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation scale.name input.name
  let target := DyadicScale.dyadicScaledApproximation
    (DyadicReduction.rangeExponent input.name) input.name
  exact NamedEquivalent.trans
    (Bridge.coherentMul_toNamed scale input)
    (Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq product target
        (by intro index; rfl)))

/-- Automatic scaling followed by any finite number of halvings normalizes to the one sampler at the sum of the two
displayed exponents. -/
@[expose] def halfIterateAutomatic_to_dyadicScaled (extra : Nat)
    (input : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Dyadic.halfIterate extra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
        input)).name
      (DyadicScale.dyadicScaledApproximation
        (DyadicReduction.rangeExponent input.name + extra)
        input.name).toNamed :=
  Dyadic.halfIterate_to_dyadicScaledFrom
    (DyadicReduction.rangeExponent input.name)
    extra input (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled input)
      (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled_to_dyadicScaled input)

/-- Semantic form of the same normalization, used only to transfer the finite unit-disk certificate to the common-scale
sum process. -/
theorem halfIterateAutomatic_possible (extra : Nat)
    (input : Coherent.CoherentNamed) {value : Data.Gaussian.Basic.Canonical}
    (possible :
      (Dyadic.halfIterate extra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
        input)).name.process.Possible
        (Dyadic.halfIterate extra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          input)).name.state value) :
    ∃ sourceValue,
      input.name.process.Possible input.name.state sourceValue ∧
        value = Dyadic.inverseDyadicAt
          (DyadicReduction.rangeExponent input.name + extra) *
            sourceValue := by
  rcases Dyadic.halfIterate_possible extra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
    input) possible with
    ⟨scaledValue, scaledPossible, valueEqual⟩
  rcases scaledPossible with ⟨scaleValue, sourceValue,
    scalePossible, sourcePossible, scaledEqual⟩
  change scaleValue =
    DyadicReduction.inverseDyadic input.name at scalePossible
  subst scaleValue
  subst scaledValue
  refine ⟨sourceValue, sourcePossible, ?_⟩
  rw [valueEqual, Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled_inverse_eq,
    ← Data.Gaussian.Basic.mul_assoc,
    Dyadic.inverseDyadicAt_mul]

/-- The actual sum of two independently scheduled automatically scaled names at one common exponent satisfies the local
unit-disk contract. -/
theorem automaticCommonAddUnitDisk
    (xExtra yExtra sumExtra common : Nat)
    (left right : Coherent.CoherentNamed)
    (xCommon :
      DyadicReduction.rangeExponent left.name + xExtra =
        common)
    (yCommon :
      DyadicReduction.rangeExponent right.name + yExtra =
        common)
    (sumCommon :
      DyadicReduction.rangeExponent
          (CoherentNamed.add
            left right).name + sumExtra = common) :
    Name.UnitDisk
      (Named.add
        (Dyadic.halfIterate xExtra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          left)).name
        (Dyadic.halfIterate yExtra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          right)).name) where
  possible_unit := by
    intro value possible
    let sumInput :=
      CoherentNamed.add left right
    rcases possible with ⟨leftValue, rightValue,
      leftPossible, rightPossible, rfl⟩
    rcases Approximation.Gaussian.Exponential.Progressive.Range.Scaling.halfIterateAutomatic_possible xExtra left
      leftPossible with
      ⟨leftSource, leftSourcePossible, leftEqual⟩
    rcases Approximation.Gaussian.Exponential.Progressive.Range.Scaling.halfIterateAutomatic_possible yExtra right
      rightPossible with
      ⟨rightSource, rightSourcePossible, rightEqual⟩
    rw [xCommon] at leftEqual
    rw [yCommon] at rightEqual
    rw [leftEqual, rightEqual]
    have sumPossible :
        sumInput.name.process.Possible sumInput.name.state
          (leftSource + rightSource) :=
      ⟨leftSource, rightSource, leftSourcePossible, rightSourcePossible, rfl⟩
    have sumBound :=
      Gaussian.Name.Bounds.possible_normSq_le_inputBound
        sumInput.name sumPossible
    have sumBaseLeCommon :
        DyadicReduction.rangeExponent sumInput.name ≤
          common := by
      rw [← sumCommon]
      exact Nat.le_add_right _ _
    have radiusOrder :
        Geometric.Basic.quarterRadius
            (Gaussian.Name.Bounds.inputBound sumInput.name)
            common ≤
          Geometric.Basic.quarterRadius
            (Gaussian.Name.Bounds.inputBound sumInput.name)
            (DyadicReduction.rangeExponent
              sumInput.name) :=
      quarterRadius_antitone
        (Gaussian.Name.Bounds.inputBound_nonneg sumInput.name)
        sumBaseLeCommon
    have identity :
        Dyadic.inverseDyadicAt common * leftSource +
            Dyadic.inverseDyadicAt common * rightSource =
          Dyadic.inverseDyadicAt common * (leftSource + rightSource) :=
      (Data.Gaussian.Basic.left_distrib _ _ _).symm
    rw [identity, Data.Gaussian.Norm.Basic.normSq_mul, Dyadic.normSq_inverseDyadicAt]
    calc
      Geometric.Basic.quarterRadius 1 common *
          Data.Gaussian.Norm.Basic.normSq (leftSource + rightSource) ≤
        Geometric.Basic.quarterRadius 1 common *
          Gaussian.Name.Bounds.inputBound sumInput.name :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
          (Geometric.Basic.quarterRadius_nonneg (by decide) _)
      _ = Geometric.Basic.quarterRadius
          (Gaussian.Name.Bounds.inputBound sumInput.name)
          common := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      _ ≤ Geometric.Basic.quarterRadius
          (Gaussian.Name.Bounds.inputBound sumInput.name)
          (DyadicReduction.rangeExponent sumInput.name) :=
        radiusOrder
      _ ≤ 1 :=
        (DyadicReduction.rangeExponent_accurate
          sumInput.name).le

/-- The three independently automatic scaling paths become operationally additive after a finite maximum raises them to
one common exponent. -/
@[expose] def automaticCommonScaledAdd_equivalent
    (xExtra yExtra sumExtra common : Nat)
    (left right : Coherent.CoherentNamed)
    (xCommon :
      DyadicReduction.rangeExponent left.name + xExtra =
        common)
    (yCommon :
      DyadicReduction.rangeExponent right.name + yExtra =
        common)
    (sumCommon :
      DyadicReduction.rangeExponent
          (CoherentNamed.add
            left right).name + sumExtra = common) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Dyadic.halfIterate xExtra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          left)).name
        (Dyadic.halfIterate yExtra (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          right)).name)
      (Dyadic.halfIterate sumExtra
        (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled
          (CoherentNamed.add
            left right))).name := by
  let sumInput :=
    CoherentNamed.add left right
  let xNormalized := Dyadic.halfIterate xExtra
    (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled left)
  let yNormalized := Dyadic.halfIterate yExtra
    (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled right)
  let sumNormalized := Dyadic.halfIterate sumExtra
    (Approximation.Gaussian.Exponential.Progressive.Range.Scaling.automaticScaled sumInput)
  let xScaledApproximation := DyadicScale.dyadicScaledApproximation common left.name
  let yScaledApproximation := DyadicScale.dyadicScaledApproximation common right.name
  let sumScaledApproximation := DyadicScale.dyadicScaledApproximation common sumInput.name
  let xScaled :=
    CoherentNamed.ofApproximation
      xScaledApproximation
  let yScaled :=
    CoherentNamed.ofApproximation
      yScaledApproximation
  have xEquivalent : Gaussian.Equivalence.NamedEquivalent xNormalized.name xScaled.name := by
    simpa only [xNormalized, xScaled, xScaledApproximation, xCommon,
      CoherentNamed.ofApproximation] using
      Approximation.Gaussian.Exponential.Progressive.Range.Scaling.halfIterateAutomatic_to_dyadicScaled xExtra left
  have yEquivalent : Gaussian.Equivalence.NamedEquivalent yNormalized.name yScaled.name := by
    simpa only [yNormalized, yScaled, yScaledApproximation, yCommon,
      CoherentNamed.ofApproximation] using
      Approximation.Gaussian.Exponential.Progressive.Range.Scaling.halfIterateAutomatic_to_dyadicScaled yExtra right
  have sumEquivalent : Gaussian.Equivalence.NamedEquivalent
      sumNormalized.name sumScaledApproximation.toNamed := by
    simpa only [sumNormalized, sumScaledApproximation, sumInput, sumCommon]
      using Approximation.Gaussian.Exponential.Progressive.Range.Scaling.halfIterateAutomatic_to_dyadicScaled sumExtra
        sumInput
  have inputsToScaled :
      Gaussian.Equivalence.NamedEquivalent
        (Named.add
          xNormalized.name yNormalized.name)
        (Named.add
          xScaled.name yScaled.name) :=
    Congruence.coherentAdd_respects xNormalized xScaled yNormalized yScaled
      xEquivalent yEquivalent
  exact NamedEquivalent.trans
    inputsToScaled
    (NamedEquivalent.trans
      (Dyadic.dyadicScaledAdd_equivalent common left right)
      (NamedEquivalent.symm
        sumEquivalent))

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Scaling
