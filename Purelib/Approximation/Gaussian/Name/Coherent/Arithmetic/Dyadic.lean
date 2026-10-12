module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.ContractiveScale
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Dyadic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
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

/-- One explicit halving of an arbitrary coherent progressive input. -/
@[expose] def halfScaled (input : Coherent.CoherentNamed) : Coherent.CoherentNamed :=
  CoherentNamed.mul
    (Coherence.exact Dyadic.dyadicHalf)
    input

/-- Adding two actual, independently scheduled half-scaled copies is operationally the original coherent input.

The comparison passes through only finite canonical samplers. -/
@[expose] def halfScaledSelfAdd_equivalent (input : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfScaled input).name
          (Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfScaled input).name)
      input.name := by
  let halfExact :=
    Coherence.exact Dyadic.dyadicHalf
  let half := Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfScaled input
  let halfProduct := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation halfExact.name input.name
  let halfProductName :=
    CoherentNamed.ofApproximation
      halfProduct
  let inputApproximation :=
    Sampling.approximation input.name
  have halfToProduct : Gaussian.Equivalence.NamedEquivalent half.name halfProductName.name :=
    Bridge.coherentMul_toNamed halfExact input
  have addToProductAdd :
      Gaussian.Equivalence.NamedEquivalent
        (Named.add half.name half.name)
        (Named.add
          halfProductName.name halfProductName.name) :=
    Congruence.coherentAdd_respects half halfProductName half halfProductName
      halfToProduct halfToProduct
  have productAddToSampled :
      Gaussian.Equivalence.NamedEquivalent
        (Named.add
          halfProductName.name halfProductName.name)
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation
          halfProductName.name halfProductName.name).toNamed :=
    Bridge.coherentAdd_toNamed halfProductName halfProductName
  have sampledToInput :
      Gaussian.Equivalence.NamedEquivalent
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation
          halfProductName.name halfProductName.name).toNamed
        inputApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Congruence.pointwiseSumApproximation_respects
        (Equivalent.toNamed_sampling
          halfProduct)
        (Equivalent.toNamed_sampling
          halfProduct)
        (by intro index; rfl)
        (by
          intro index
          change inputApproximation.sample index =
            Dyadic.dyadicHalf * inputApproximation.sample index +
              Dyadic.dyadicHalf * inputApproximation.sample index
          exact (Dyadic.dyadicScale_succ_add_self 0
            (inputApproximation.sample index)).symm))
  exact NamedEquivalent.trans
    addToProductAdd
    (NamedEquivalent.trans
      productAddToSampled
      (NamedEquivalent.trans
        sampledToInput
        (NamedEquivalent.symm
          (Equivalence.named_toSamplingNamed input.name))))

/-- A finite chain of explicit input halvings. -/
@[expose] def halfIterate : Nat → Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed →
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
  | 0, input => input
  | extra + 1, input => Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfScaled
    (Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra input)

/-- Normalize a finite halving chain to one explicit dyadic-scaled sampler, starting from any name already equivalent to
the sampler at `base`. -/
@[expose] def halfIterate_to_dyadicScaledFrom (base : Nat) :
    (extra : Nat) → (original start : Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed) →
      Gaussian.Equivalence.NamedEquivalent start.name
        (Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale.dyadicScaledApproximation base
          original.name).toNamed →
      Gaussian.Equivalence.NamedEquivalent
        (Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra start).name
        (Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale.dyadicScaledApproximation (base + extra)
          original.name).toNamed
  | 0, _original, _start, startEquivalent => startEquivalent
  | extra + 1, original, start, startEquivalent => by
      let previous := Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra start
      let previousApproximation :=
        Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale.dyadicScaledApproximation (base + extra)
          original.name
      let previousApproximationName :=
        Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.ofApproximation
          previousApproximation
      let halfExact :=
        Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact
          Purelib.Data.Gaussian.Dyadic.dyadicHalf
      let halfConstant :=
        Purelib.Approximation.Gaussian.Sequence.Constant.constantApproximation Purelib.Data.Gaussian.Dyadic.dyadicHalf
      let halfConstantName :=
        Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.ofApproximation
          halfConstant
      let nextApproximation :=
        Purelib.Approximation.Gaussian.Sequence.Arithmetic.DyadicScale.dyadicScaledApproximation ((base + extra) + 1)
          original.name
      have previousEquivalent :
          Gaussian.Equivalence.NamedEquivalent previous.name previousApproximationName.name :=
        Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate_to_dyadicScaledFrom base extra
          original start
          startEquivalent
      have actualToApproximationFactors :
          Gaussian.Equivalence.NamedEquivalent
            (Purelib.Approximation.Gaussian.Name.Basic.Named.mul
              halfExact.name previous.name)
            (Purelib.Approximation.Gaussian.Name.Basic.Named.mul
              halfConstantName.name previousApproximationName.name) :=
        Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects halfExact
          halfConstantName
          previous previousApproximationName
          (Purelib.Approximation.Gaussian.Sequence.Name.Exact.exact_toConstantNamed
            Purelib.Data.Gaussian.Dyadic.dyadicHalf) previousEquivalent
      have factorsToNext :
          Gaussian.Equivalence.NamedEquivalent
            (Purelib.Approximation.Gaussian.Name.Basic.Named.mul
              halfConstantName.name previousApproximationName.name)
            nextApproximation.toNamed :=
        Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
          halfConstant previousApproximation
          nextApproximation (by
            intro index
            change Purelib.Data.Gaussian.Dyadic.inverseDyadicAt ((base + extra) + 1) *
                (Purelib.Approximation.Gaussian.Name.Sampling.approximation
                  original.name).sample index =
              Purelib.Data.Gaussian.Dyadic.dyadicHalf *
                (Purelib.Data.Gaussian.Dyadic.inverseDyadicAt (base + extra) *
                  (Purelib.Approximation.Gaussian.Name.Sampling.approximation
                    original.name).sample index)
            rw [← Purelib.Data.Gaussian.Dyadic.inverseDyadicAt_succ]
            exact Purelib.Data.Gaussian.Basic.mul_assoc _ _ _)
      exact Gaussian.Equivalence.NamedEquivalent.trans
        actualToApproximationFactors factorsToNext

/-- Every finite halving chain has the explicit inverse-dyadic sampler of its original coherent input. -/
@[expose] def halfIterate_to_dyadicScaled (extra : Nat) (input : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra input).name
      (DyadicScale.dyadicScaledApproximation extra input.name).toNamed := by
  let source := Sampling.approximation input.name
  have baseEquivalent : Gaussian.Equivalence.NamedEquivalent input.name
      (DyadicScale.dyadicScaledApproximation 0 input.name).toNamed :=
    NamedEquivalent.trans
      (Equivalence.named_toSamplingNamed input.name)
      (Equivalence.approximationEquivalent_toNamed
        (Equivalence.approximationEquivalentOfSamplesEq source
          (DyadicScale.dyadicScaledApproximation 0 input.name)
          (by
            intro index
            rw [DyadicScale.dyadicScaledApproximation_sample, Dyadic.inverseDyadicAt_zero,
              Data.Gaussian.Basic.one_mul])))
  simpa only [Nat.zero_add] using
    Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate_to_dyadicScaledFrom 0 extra input input
      baseEquivalent

/-- At one displayed inverse-dyadic scale, the two canonical operand samplers add operationally to the canonical sampler
of the actual input sum. -/
@[expose] def dyadicScaledAdd_equivalent (exponent : Nat)
    (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (Named.add
        (DyadicScale.dyadicScaledApproximation exponent left.name).toNamed
        (DyadicScale.dyadicScaledApproximation exponent right.name).toNamed)
      (DyadicScale.dyadicScaledApproximation exponent
        (CoherentNamed.add
          left right).name).toNamed := by
  let leftScaled := DyadicScale.dyadicScaledApproximation exponent left.name
  let rightScaled := DyadicScale.dyadicScaledApproximation exponent right.name
  let leftScaledName :=
    CoherentNamed.ofApproximation
      leftScaled
  let rightScaledName :=
    CoherentNamed.ofApproximation
      rightScaled
  let sumInput :=
    CoherentNamed.add left right
  let sourceSum := Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation left.name right.name
  let directScaledSum := ContractiveScale.contractiveScaleApproximation
    (Dyadic.inverseDyadicAt exponent) (Dyadic.normSq_inverseDyadicAt_le_one exponent)
      sourceSum
  let sumScaled := DyadicScale.dyadicScaledApproximation exponent sumInput.name
  have addToSampled :
      Gaussian.Equivalence.NamedEquivalent
        (Named.add
          leftScaledName.name rightScaledName.name)
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation
          leftScaledName.name rightScaledName.name).toNamed :=
    Bridge.coherentAdd_toNamed leftScaledName rightScaledName
  have sampledToDirect :
      Gaussian.Equivalence.NamedEquivalent
        (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation
          leftScaledName.name rightScaledName.name).toNamed
        directScaledSum.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Congruence.pointwiseSumApproximation_respects
        (Equivalent.toNamed_sampling
          leftScaled)
        (Equivalent.toNamed_sampling
          rightScaled)
        (by intro index; rfl)
        (by
          intro index
          change Dyadic.inverseDyadicAt exponent *
                ((Sampling.approximation
                    left.name).sample index +
                  (Sampling.approximation
                    right.name).sample index) =
              Dyadic.inverseDyadicAt exponent *
                  (Sampling.approximation
                    left.name).sample index +
                Dyadic.inverseDyadicAt exponent *
                  (Sampling.approximation
                    right.name).sample index
          exact Data.Gaussian.Basic.left_distrib _ _ _))
  have sumSamplerToDirect : Gaussian.Equivalence.Equivalent
      (Sampling.approximation sumInput.name)
      sourceSum :=
    Equivalent.trans
      (Bridge.coherentAdd_toNamed left right)
      (Equivalent.toNamed_sampling
        sourceSum)
  have sumScaledToDirect : Gaussian.Equivalence.Equivalent sumScaled directScaledSum :=
    ContractiveScale.contractiveScaleApproximation_respects
      (Dyadic.inverseDyadicAt exponent) (Dyadic.normSq_inverseDyadicAt_le_one exponent)
      sumSamplerToDirect
  exact NamedEquivalent.trans
    addToSampled
    (NamedEquivalent.trans
      sampledToDirect
      (NamedEquivalent.symm
        (Equivalence.approximationEquivalent_toNamed sumScaledToDirect)))

/-- A possible reading after finitely many actual halvings is an explicitly displayed inverse-dyadic multiple of a
possible original reading. -/
theorem halfIterate_possible (extra : Nat) (input : Coherent.CoherentNamed)
    {value : Data.Gaussian.Basic.Canonical}
    (possible : (Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra input).name.process.Possible
      (Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic.halfIterate extra input).name.state value) :
    ∃ sourceValue,
      input.name.process.Possible input.name.state sourceValue ∧
        value = Dyadic.inverseDyadicAt extra * sourceValue := by
  induction extra generalizing value with
  | zero =>
      exact ⟨value, possible, by rw [Dyadic.inverseDyadicAt_zero,
        Data.Gaussian.Basic.one_mul]⟩
  | succ extra inductionHypothesis =>
      rcases possible with ⟨scaleValue, previousValue,
        scalePossible, previousPossible, rfl⟩
      change scaleValue = Dyadic.dyadicHalf at scalePossible
      subst scaleValue
      rcases inductionHypothesis previousPossible with
        ⟨sourceValue, sourcePossible, previousEqual⟩
      refine ⟨sourceValue, sourcePossible, ?_⟩
      rw [previousEqual, ← Data.Gaussian.Basic.mul_assoc,
        Dyadic.inverseDyadicAt_succ]

end

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
