module
-- The exposed comparison retains this exact bound certificate.
public import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Halving
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Halving
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Scaling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Dyadic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.DyadicReduction
import Purelib.Approximation.Gaussian.Name.UnitDisk

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

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

/-- Raising the displayed restoration exponent by any finite amount while halving the arbitrary coherent input the same
number of times preserves the global exponential name operationally. -/
@[expose] def coherentDyadicExp_raise (base extra : Nat) (input : CoherentNamed)
    (domain : UnitDisk input.name) :
    NamedEquivalent
      (Power.squareIterate (base + extra)
        (Local.Name.named (Dyadic.halfIterate extra input).name
          (Local.Halving.halfIterateUnitDisk extra input domain)))
      (Power.squareIterate base
        (Local.Name.named input.name domain)) := by
  induction extra with
  | zero =>
      exact NamedEquivalent.refl _
  | succ extra inductionHypothesis =>
      have step := Halving.coherentDyadicExp_step (base + extra)
        (Dyadic.halfIterate extra input) (Local.Halving.halfIterateUnitDisk extra input domain)
      exact NamedEquivalent.trans
        (by simpa only [Nat.add_succ, Dyadic.halfIterate] using step)
        inductionHypothesis

/-- Coherent restored local exponential at an explicitly supplied finite range exponent. -/
@[expose] def restoredLocalExp (exponent : Nat) (input : CoherentNamed)
    (domain : UnitDisk input.name) :
    CoherentNamed :=
  { name := Power.squareIterate exponent
      (Local.Name.named input.name domain)
    coherent := Coherent.squareIterateCoherent exponent _
      (Local.Coherent.localExpCoherent input.name domain) }

/-- Global exponential addition with three independent starting exponents, reduced to one explicit finite compatibility
certificate between the three common-scale input names.

All exponent raising and output algebra is proved here; no completed operand value is selected. -/
@[expose] def coherentDyadicExp_add_independent
    (xBase xExtra yBase yExtra sumBase sumExtra common : Nat)
    (xInput yInput sumInput : CoherentNamed)
    (xDomain : UnitDisk xInput.name)
    (yDomain : UnitDisk yInput.name)
    (sumDomain : UnitDisk sumInput.name)
    (xCommon : xBase + xExtra = common)
    (yCommon : yBase + yExtra = common)
    (sumCommon : sumBase + sumExtra = common)
    (commonAddDomain : UnitDisk
      (Named.add
        (Dyadic.halfIterate xExtra xInput).name
        (Dyadic.halfIterate yExtra yInput).name))
    (scaledAdd : NamedEquivalent
      (Named.add
        (Dyadic.halfIterate xExtra xInput).name
        (Dyadic.halfIterate yExtra yInput).name)
      (Dyadic.halfIterate sumExtra sumInput).name) :
    NamedEquivalent
      (Named.mul
        (restoredLocalExp xBase xInput xDomain).name
        (restoredLocalExp yBase yInput yDomain).name)
      (restoredLocalExp sumBase sumInput sumDomain).name := by
  let xCommonInput := Dyadic.halfIterate xExtra xInput
  let yCommonInput := Dyadic.halfIterate yExtra yInput
  let sumCommonInput := Dyadic.halfIterate sumExtra sumInput
  let xCommonDomain := Local.Halving.halfIterateUnitDisk xExtra xInput xDomain
  let yCommonDomain := Local.Halving.halfIterateUnitDisk yExtra yInput yDomain
  let sumCommonDomain := Local.Halving.halfIterateUnitDisk sumExtra sumInput sumDomain
  let xBaseExp := restoredLocalExp xBase xInput xDomain
  let yBaseExp := restoredLocalExp yBase yInput yDomain
  let sumBaseExp := restoredLocalExp sumBase sumInput sumDomain
  let xCommonExp := restoredLocalExp common xCommonInput xCommonDomain
  let yCommonExp := restoredLocalExp common yCommonInput yCommonDomain
  let sumCommonExp := restoredLocalExp common sumCommonInput sumCommonDomain
  have xRaise : NamedEquivalent xCommonExp.name xBaseExp.name := by
    simpa only [xCommonExp, xCommonInput, xBaseExp, restoredLocalExp, xCommon]
      using coherentDyadicExp_raise xBase xExtra xInput xDomain
  have yRaise : NamedEquivalent yCommonExp.name yBaseExp.name := by
    simpa only [yCommonExp, yCommonInput, yBaseExp, restoredLocalExp, yCommon]
      using coherentDyadicExp_raise yBase yExtra yInput yDomain
  have sumRaise : NamedEquivalent sumCommonExp.name sumBaseExp.name := by
    simpa only [sumCommonExp, sumCommonInput, sumBaseExp, restoredLocalExp,
      sumCommon] using
        coherentDyadicExp_raise sumBase sumExtra sumInput sumDomain
  have factorsToCommon :
      NamedEquivalent
        (Named.mul
          xBaseExp.name yBaseExp.name)
        (Named.mul
          xCommonExp.name yCommonExp.name) :=
    Congruence.coherentMul_respects xBaseExp xCommonExp yBaseExp yCommonExp
      (NamedEquivalent.symm xRaise)
      (NamedEquivalent.symm yRaise)
  have commonLaw := Local.Addition.Power.coherentLocalExp_add_after_squareIterate common
    xCommonInput yCommonInput xCommonDomain yCommonDomain commonAddDomain
  let commonAddInput :=
    CoherentNamed.add
      xCommonInput yCommonInput
  let commonAddExp : CoherentNamed :=
    { name := Local.Name.named
        commonAddInput.name commonAddDomain
      coherent := Local.Coherent.localExpCoherent commonAddInput.name commonAddDomain }
  let sumLocalExp : CoherentNamed :=
    { name := Local.Name.named
        sumCommonInput.name sumCommonDomain
      coherent := Local.Coherent.localExpCoherent sumCommonInput.name sumCommonDomain }
  have localToSum : NamedEquivalent commonAddExp.name sumLocalExp.name :=
    Local.Congruence.localExpNamed_respects commonAddDomain sumCommonDomain scaledAdd
  have restoredToSum : NamedEquivalent
      (Power.squareIterate common
        commonAddExp.name)
      sumCommonExp.name := by
    simpa only [sumCommonExp, restoredLocalExp] using
      Congruence.squareIterate_respects common commonAddExp sumLocalExp localToSum
  exact NamedEquivalent.trans
    factorsToCommon
    (NamedEquivalent.trans
      (by simpa only [xCommonExp, yCommonExp, restoredLocalExp,
          commonAddExp, commonAddInput,
          CoherentNamed.add]
        using commonLaw)
      (NamedEquivalent.trans
        restoredToSum sumRaise))

/-- Global exponential addition for arbitrary coherent progressive CCL inputs.

The three automatic range reductions may choose different finite exponents; a computed maximum, explicit halving chains,
and finite sampler normalization reconcile them without selecting completed input values. -/
@[expose] def automaticExp_add (left right : CoherentNamed) :
    NamedEquivalent
      (Named.mul
        (Name.named left.name)
        (Name.named right.name))
      (Name.named
        (Named.add
          left.name right.name)) := by
  let sumInput :=
    CoherentNamed.add left right
  let xBase :=
    DyadicReduction.rangeExponent left.name
  let yBase :=
    DyadicReduction.rangeExponent right.name
  let sumBase :=
    DyadicReduction.rangeExponent sumInput.name
  let common := max xBase (max yBase sumBase)
  let xExtra := common - xBase
  let yExtra := common - yBase
  let sumExtra := common - sumBase
  have xOrder : xBase ≤ common := Data.Nat.Order.le_max_left _ _
  have yOrder : yBase ≤ common :=
    (Data.Nat.Order.le_max_left yBase sumBase).trans (Data.Nat.Order.le_max_right _ _)
  have sumOrder : sumBase ≤ common :=
    (Data.Nat.Order.le_max_right yBase sumBase).trans (Data.Nat.Order.le_max_right _ _)
  have xCommon : xBase + xExtra = common := by
    dsimp only [xExtra]
    rw [Nat.add_comm, Data.Nat.Subtraction.sub_add_cancel xOrder]
  have yCommon : yBase + yExtra = common := by
    dsimp only [yExtra]
    rw [Nat.add_comm, Data.Nat.Subtraction.sub_add_cancel yOrder]
  have sumCommon : sumBase + sumExtra = common := by
    dsimp only [sumExtra]
    rw [Nat.add_comm, Data.Nat.Subtraction.sub_add_cancel sumOrder]
  let xDomain := DyadicReduction.scaledDomain left.name
  let yDomain := DyadicReduction.scaledDomain right.name
  let sumDomain :=
    DyadicReduction.scaledDomain sumInput.name
  let commonAddDomain := Scaling.automaticCommonAddUnitDisk
    xExtra yExtra sumExtra common left right xCommon yCommon sumCommon
  let scaledAdd := Scaling.automaticCommonScaledAdd_equivalent
    xExtra yExtra sumExtra common left right xCommon yCommon sumCommon
  simpa only [xBase, yBase, sumBase, sumInput, restoredLocalExp,
      Scaling.automaticScaled, Name.named,
      CoherentNamed.add] using
    coherentDyadicExp_add_independent
      xBase xExtra yBase yExtra sumBase sumExtra common
      (Scaling.automaticScaled left)
        (Scaling.automaticScaled right)
      (Scaling.automaticScaled sumInput) xDomain yDomain sumDomain
      xCommon yCommon sumCommon commonAddDomain scaledAdd

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Addition
