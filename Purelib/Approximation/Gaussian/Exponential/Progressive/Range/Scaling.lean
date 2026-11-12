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
@[expose] def automaticScaled (input : CoherentNamed) : CoherentNamed :=
  { name := DyadicReduction.scaledInput input.name
    coherent :=
      Process.Coherence.Basic.Coherent.mul
        (Process.Coherence.Basic.Coherent.exact
          (DyadicReduction.inverseDyadic input.name))
        input.coherent }

/-- The automatically selected scaling factor is exactly the inverse dyadic at the retained range exponent. -/
theorem automaticScaled_inverse_eq (input : Named) :
    DyadicReduction.inverseDyadic input =
      Dyadic.inverseDyadicAt
        (DyadicReduction.rangeExponent input) :=
  rfl

/-- The actual automatic scaling process is operationally its explicit inverse-dyadic sampler. -/
@[expose] def automaticScaled_to_dyadicScaled (input : CoherentNamed) :
    NamedEquivalent
      (automaticScaled input).name
      (DyadicScale.dyadicScaledApproximation
        (DyadicReduction.rangeExponent input.name)
        input.name).toNamed := by
  let scale := Coherence.exact
    (DyadicReduction.inverseDyadic input.name)
  let product := Product.sampledProductApproximation scale.name input.name
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
    (input : CoherentNamed) :
    NamedEquivalent
      (Dyadic.halfIterate extra (automaticScaled
        input)).name
      (DyadicScale.dyadicScaledApproximation
        (DyadicReduction.rangeExponent input.name + extra)
        input.name).toNamed :=
  Dyadic.halfIterate_to_dyadicScaledFrom
    (DyadicReduction.rangeExponent input.name)
    extra input (automaticScaled input)
      (automaticScaled_to_dyadicScaled input)

/-- Semantic form of the same normalization, used only to transfer the finite unit-disk certificate to the common-scale
sum process. -/
theorem halfIterateAutomatic_possible (extra : Nat)
    (input : CoherentNamed) {value : Basic.Canonical}
    (possible :
      (Dyadic.halfIterate extra (automaticScaled
        input)).name.process.Possible
        (Dyadic.halfIterate extra (automaticScaled
          input)).name.state value) :
    ∃ sourceValue,
      input.name.process.Possible input.name.state sourceValue ∧
        value = Dyadic.inverseDyadicAt
          (DyadicReduction.rangeExponent input.name + extra) *
            sourceValue := by
  rcases Dyadic.halfIterate_possible extra (automaticScaled
    input) possible with
    ⟨scaledValue, scaledPossible, valueEqual⟩
  rcases scaledPossible with ⟨scaleValue, sourceValue,
    scalePossible, sourcePossible, scaledEqual⟩
  change scaleValue =
    DyadicReduction.inverseDyadic input.name at scalePossible
  subst scaleValue
  subst scaledValue
  refine ⟨sourceValue, sourcePossible, ?_⟩
  rw [valueEqual, automaticScaled_inverse_eq,
    ← Basic.mul_assoc,
    Dyadic.inverseDyadicAt_mul]

/-- The actual sum of two independently scheduled automatically scaled names at one common exponent satisfies the local
unit-disk contract. -/
theorem automaticCommonAddUnitDisk
    (xExtra yExtra sumExtra common : Nat)
    (left right : CoherentNamed)
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
    UnitDisk
      (Named.add
        (Dyadic.halfIterate xExtra (automaticScaled
          left)).name
        (Dyadic.halfIterate yExtra (automaticScaled
          right)).name) where
  possible_unit := by
    intro value possible
    let sumInput :=
      CoherentNamed.add left right
    rcases possible with ⟨leftValue, rightValue,
      leftPossible, rightPossible, rfl⟩
    rcases halfIterateAutomatic_possible xExtra left
      leftPossible with
      ⟨leftSource, leftSourcePossible, leftEqual⟩
    rcases halfIterateAutomatic_possible yExtra right
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
      Bounds.possible_normSq_le_inputBound
        sumInput.name sumPossible
    have sumBaseLeCommon :
        DyadicReduction.rangeExponent sumInput.name ≤
          common := by
      rw [← sumCommon]
      exact Nat.le_add_right _ _
    have radiusOrder :
        Geometric.Basic.quarterRadius
            (Bounds.inputBound sumInput.name)
            common ≤
          Geometric.Basic.quarterRadius
            (Bounds.inputBound sumInput.name)
            (DyadicReduction.rangeExponent
              sumInput.name) :=
      quarterRadius_antitone
        (Bounds.inputBound_nonneg sumInput.name)
        sumBaseLeCommon
    have identity :
        Dyadic.inverseDyadicAt common * leftSource +
            Dyadic.inverseDyadicAt common * rightSource =
          Dyadic.inverseDyadicAt common * (leftSource + rightSource) :=
      (Basic.left_distrib _ _ _).symm
    rw [identity, Norm.Basic.normSq_mul, Dyadic.normSq_inverseDyadicAt]
    calc
      Geometric.Basic.quarterRadius 1 common *
          Norm.Basic.normSq (leftSource + rightSource) ≤
        Geometric.Basic.quarterRadius 1 common *
          Bounds.inputBound sumInput.name :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
          (Geometric.Basic.quarterRadius_nonneg (by decide) _)
      _ = Geometric.Basic.quarterRadius
          (Bounds.inputBound sumInput.name)
          common := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      _ ≤ Geometric.Basic.quarterRadius
          (Bounds.inputBound sumInput.name)
          (DyadicReduction.rangeExponent sumInput.name) :=
        radiusOrder
      _ ≤ 1 :=
        (DyadicReduction.rangeExponent_accurate
          sumInput.name).le

/-- The three independently automatic scaling paths become operationally additive after a finite maximum raises them to
one common exponent. -/
@[expose] def automaticCommonScaledAdd_equivalent
    (xExtra yExtra sumExtra common : Nat)
    (left right : CoherentNamed)
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
    NamedEquivalent
      (Named.add
        (Dyadic.halfIterate xExtra (automaticScaled
          left)).name
        (Dyadic.halfIterate yExtra (automaticScaled
          right)).name)
      (Dyadic.halfIterate sumExtra
        (automaticScaled
          (CoherentNamed.add
            left right))).name := by
  let sumInput :=
    CoherentNamed.add left right
  let xNormalized := Dyadic.halfIterate xExtra
    (automaticScaled left)
  let yNormalized := Dyadic.halfIterate yExtra
    (automaticScaled right)
  let sumNormalized := Dyadic.halfIterate sumExtra
    (automaticScaled sumInput)
  let xScaledApproximation := DyadicScale.dyadicScaledApproximation common left.name
  let yScaledApproximation := DyadicScale.dyadicScaledApproximation common right.name
  let sumScaledApproximation := DyadicScale.dyadicScaledApproximation common sumInput.name
  let xScaled :=
    CoherentNamed.ofApproximation
      xScaledApproximation
  let yScaled :=
    CoherentNamed.ofApproximation
      yScaledApproximation
  have xEquivalent : NamedEquivalent xNormalized.name xScaled.name := by
    simpa only [xNormalized, xScaled, xScaledApproximation, xCommon,
      CoherentNamed.ofApproximation] using
      halfIterateAutomatic_to_dyadicScaled xExtra left
  have yEquivalent : NamedEquivalent yNormalized.name yScaled.name := by
    simpa only [yNormalized, yScaled, yScaledApproximation, yCommon,
      CoherentNamed.ofApproximation] using
      halfIterateAutomatic_to_dyadicScaled yExtra right
  have sumEquivalent : NamedEquivalent
      sumNormalized.name sumScaledApproximation.toNamed := by
    simpa only [sumNormalized, sumScaledApproximation, sumInput, sumCommon]
      using halfIterateAutomatic_to_dyadicScaled sumExtra
        sumInput
  have inputsToScaled :
      NamedEquivalent
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
