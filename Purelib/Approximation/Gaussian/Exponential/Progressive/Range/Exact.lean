module
-- Exposed comparison fields retain the reconstructed natural bound.
public import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Zero
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Addition.Power
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Congruence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent
import Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Congruence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Exact
import Purelib.Approximation.Gaussian.Name.DyadicReduction
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Sequence.Coherence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Name.Exact
public import Purelib.Data.Gaussian.Dyadic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Arithmetic
open Purelib.Approximation.Gaussian.Name.Arithmetic.Power
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.UnitDisk
open Purelib.Approximation.Gaussian.Sequence
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

/-- Adjacent admissible dyadic exponents give operationally equivalent restored exponential names. -/
@[expose] def exactDyadicExp_step (exponent : Nat) (value : Basic.Canonical)
    (unit : Norm.Basic.normSq (Dyadic.dyadicScale exponent value) ≤ 1) :
    NamedEquivalent
      (Power.squareIterate (exponent + 1)
        (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale (exponent + 1) value)
          (Dyadic.dyadicScale_unit_succ unit)))
      (Power.squareIterate exponent
        (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale exponent value) unit)) := by
  have doubleUnit :
      Norm.Basic.normSq
          (Dyadic.dyadicScale (exponent + 1) value +
            Dyadic.dyadicScale (exponent + 1) value) ≤ 1 := by
    rw [Dyadic.dyadicScale_succ_add_self]
    exact unit
  simpa only [Dyadic.dyadicScale_succ_add_self] using
    Local.Addition.Power.exactLocalExp_doubling_after_squareIterate exponent
      (Dyadic.dyadicScale (exponent + 1) value)
      (Dyadic.dyadicScale_unit_succ unit) doubleUnit

/-- Raising any admissible displayed dyadic exponent by a finite amount does not change the restored exact exponential
name operationally. -/
@[expose] def exactDyadicExp_raise (base extra : Nat) (value : Basic.Canonical)
    (unit : Norm.Basic.normSq (Dyadic.dyadicScale base value) ≤ 1) :
    NamedEquivalent
      (Power.squareIterate (base + extra)
        (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale (base + extra) value)
          (Dyadic.dyadicScale_unit_add base extra value unit)))
      (Power.squareIterate base
        (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale base value) unit)) := by
  induction extra with
  | zero =>
      exact NamedEquivalent.refl _
  | succ extra inductionHypothesis =>
      have step := exactDyadicExp_step (base + extra) value
        (Dyadic.dyadicScale_unit_add base extra value unit)
      exact NamedEquivalent.trans
        (by simpa only [Nat.add_succ] using step)
        inductionHypothesis

/-- At one common admissible dyadic exponent, the restored exact CCL exponential is an operational homomorphism from
addition to multiplication. -/
@[expose] def exactDyadicExp_add_at_common_exponent (exponent : Nat)
    (x y : Basic.Canonical)
    (xUnit : Norm.Basic.normSq (Dyadic.dyadicScale exponent x) ≤ 1)
    (yUnit : Norm.Basic.normSq (Dyadic.dyadicScale exponent y) ≤ 1)
    (sumUnit : Norm.Basic.normSq (Dyadic.dyadicScale exponent (x + y)) ≤ 1) :
    NamedEquivalent
      (Named.mul
        (Power.squareIterate exponent
          (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale exponent x) xUnit))
        (Power.squareIterate exponent
          (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale exponent y) yUnit)))
      (Power.squareIterate exponent
        (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale exponent (x + y)) sumUnit)) := by
  have scaledSumUnit :
      Norm.Basic.normSq (Dyadic.dyadicScale exponent x + Dyadic.dyadicScale exponent y) ≤ 1 := by
    rw [← Dyadic.dyadicScale_add]
    exact sumUnit
  simpa only [← Dyadic.dyadicScale_add] using
    Local.Addition.Power.exactLocalExp_add_after_squareIterate exponent xUnit yUnit
      scaledSumUnit

/-- Coherent exact exponential name at a displayed admissible dyadic exponent. -/
@[expose] def exactDyadicExpCoherent (exponent : Nat) (value : Basic.Canonical)
    (unit : Norm.Basic.normSq (Dyadic.dyadicScale exponent value) ≤ 1) : CoherentNamed
      :=
  { name := Power.squareIterate exponent
      (Local.Exact.exactLocalExpNamed (Dyadic.dyadicScale exponent value) unit)
    coherent := Coherent.squareIterateCoherent exponent _
      (Process.Coherence.Basic.Coherent.ofApproximation
        (Local.Exact.exactLocalExpApproximation (Dyadic.dyadicScale exponent value) unit)) }

/-- Ordered admissible dyadic exponents are interchangeable in the restored exact exponential name. -/
@[expose] def exactDyadicExp_raise_to {lower upper : Nat} (value : Basic.Canonical)
    (order : lower ≤ upper)
    (unit : Norm.Basic.normSq (Dyadic.dyadicScale lower value) ≤ 1) :
    NamedEquivalent
      (exactDyadicExpCoherent upper value
        (Dyadic.dyadicScale_unit_of_le value order unit)).name
      (exactDyadicExpCoherent lower value unit).name := by
  let extra := upper - lower
  have sumEq : lower + extra = upper := by
    dsimp only [extra]
    rw [Nat.add_comm, Data.Nat.Subtraction.sub_add_cancel order]
  simpa only [exactDyadicExpCoherent, sumEq] using
    exactDyadicExp_raise lower extra value unit

/-- Exact Gaussian-rational inputs may choose three independent admissible dyadic exponents for `x`, `y`, and `x+y`.

A finite maximum raises all three to one common exponent, applies the common-exponent law, and lowers the sum side
again. -/
@[expose] def exactDyadicExp_add_independent
    (xExponent yExponent sumExponent : Nat) (x y : Basic.Canonical)
    (xUnit : Norm.Basic.normSq (Dyadic.dyadicScale xExponent x) ≤ 1)
    (yUnit : Norm.Basic.normSq (Dyadic.dyadicScale yExponent y) ≤ 1)
    (sumUnit : Norm.Basic.normSq (Dyadic.dyadicScale sumExponent (x + y)) ≤ 1) :
    NamedEquivalent
      (Named.mul
        (exactDyadicExpCoherent xExponent x xUnit).name
        (exactDyadicExpCoherent yExponent y yUnit).name)
      (exactDyadicExpCoherent sumExponent (x + y) sumUnit).name := by
  let common := max xExponent (max yExponent sumExponent)
  have xOrder : xExponent ≤ common := Data.Nat.Order.le_max_left _ _
  have yOrder : yExponent ≤ common :=
    (Data.Nat.Order.le_max_left yExponent sumExponent).trans (Data.Nat.Order.le_max_right _ _)
  have sumOrder : sumExponent ≤ common :=
    (Data.Nat.Order.le_max_right yExponent sumExponent).trans (Data.Nat.Order.le_max_right _ _)
  let xCommonUnit := Dyadic.dyadicScale_unit_of_le x xOrder xUnit
  let yCommonUnit := Dyadic.dyadicScale_unit_of_le y yOrder yUnit
  let sumCommonUnit := Dyadic.dyadicScale_unit_of_le (x + y) sumOrder sumUnit
  let xBase := exactDyadicExpCoherent xExponent x xUnit
  let yBase := exactDyadicExpCoherent yExponent y yUnit
  let sumBase := exactDyadicExpCoherent sumExponent (x + y) sumUnit
  let xCommon := exactDyadicExpCoherent common x xCommonUnit
  let yCommon := exactDyadicExpCoherent common y yCommonUnit
  have factorsToCommon :
      NamedEquivalent
        (Named.mul
          xBase.name yBase.name)
        (Named.mul
          xCommon.name yCommon.name) :=
    Congruence.coherentMul_respects xBase xCommon yBase yCommon
      (NamedEquivalent.symm
        (exactDyadicExp_raise_to x xOrder xUnit))
      (NamedEquivalent.symm
        (exactDyadicExp_raise_to y yOrder yUnit))
  have commonLaw :
      NamedEquivalent
        (Named.mul
          xCommon.name yCommon.name)
        (exactDyadicExpCoherent common (x + y) sumCommonUnit).name :=
    exactDyadicExp_add_at_common_exponent common x y
      xCommonUnit yCommonUnit sumCommonUnit
  have sumFromCommon :
      NamedEquivalent
        (exactDyadicExpCoherent common (x + y) sumCommonUnit).name
        sumBase.name :=
    exactDyadicExp_raise_to (x + y) sumOrder sumUnit
  exact NamedEquivalent.trans
    factorsToCommon
    (NamedEquivalent.trans
      commonLaw sumFromCommon)

/-- Scaling an exact Gaussian by its automatically selected inverse dyadic factor equals its dyadic reduction. -/
theorem inverseDyadic_exact_mul_eq_dyadicScale (value : Basic.Canonical) :
    DyadicReduction.inverseDyadic
          (Named.exact value) * value =
      Dyadic.dyadicScale
        (DyadicReduction.rangeExponent
          (Named.exact value)) value := by
  exact (Dyadic.dyadicScale_eq_inversePower
    (DyadicReduction.rangeExponent
      (Named.exact value)) value).symm

/-- The automatically selected dyadic reduction of an exact Gaussian lies in the unit disk. -/
theorem automaticExactDyadicScale_unit (value : Basic.Canonical) :
    Norm.Basic.normSq
        (Dyadic.dyadicScale
          (DyadicReduction.rangeExponent
            (Named.exact value)) value) ≤
      1 := by
  let input := Named.exact value
  have possible :
      (DyadicReduction.scaledInput input).process.Possible
        (DyadicReduction.scaledInput input).state
        (DyadicReduction.inverseDyadic input * value) :=
    ⟨DyadicReduction.inverseDyadic input, value,
      rfl, rfl, rfl⟩
  have unit :=
    (DyadicReduction.scaledDomain input).possible_unit
      possible
  rw [inverseDyadic_exact_mul_eq_dyadicScale value] at unit
  exact unit

/-- The actual automatic exponential of an exact rational input is operationally its explicit dyadic normal form. -/
@[expose] def automaticExactExp_toDyadic (value : Basic.Canonical) :
    NamedEquivalent
      (Name.named
        (Named.exact value))
      (exactDyadicExpCoherent
        (DyadicReduction.rangeExponent
          (Named.exact value))
        value (automaticExactDyadicScale_unit value)).name := by
  let input := Named.exact value
  let exponent := DyadicReduction.rangeExponent input
  let scaled := DyadicReduction.scaledInput input
  let actualDomain := DyadicReduction.scaledDomain input
  let exactUnit := automaticExactDyadicScale_unit value
  let exactScaled := Named.exact
    (Dyadic.dyadicScale exponent value)
  let exactDomain := UnitDisk.exact
    (Dyadic.dyadicScale exponent value) exactUnit
  have scaledEquivalent : NamedEquivalent scaled exactScaled := by
    simpa only [scaled, exactScaled, input,
      DyadicReduction.scaledInput,
      inverseDyadic_exact_mul_eq_dyadicScale] using
        Exact.exactMul_named_equivalent
          (DyadicReduction.inverseDyadic input) value
  let actualLocal : CoherentNamed :=
    { name := Local.Name.named scaled actualDomain
      coherent := Local.Coherent.localExpCoherent scaled actualDomain }
  let exactLocal : CoherentNamed :=
    CoherentNamed.ofApproximation
      (Local.Exact.exactLocalExpApproximation (Dyadic.dyadicScale exponent value) exactUnit)
  have localEquivalent : NamedEquivalent actualLocal.name exactLocal.name :=
    Local.Congruence.localExpNamed_respects actualDomain exactDomain scaledEquivalent
  exact Congruence.squareIterate_respects exponent actualLocal exactLocal localEquivalent

/-- Global exponential addition for the actual automatically range-reduced CCL entry point on arbitrary displayed
Gaussian-rational inputs.

Each of the three calls may compute a different finite range exponent. -/
@[expose] def automaticExactExp_add (x y : Basic.Canonical) :
    NamedEquivalent
      (Named.mul
        (Name.named
          (Named.exact x))
        (Name.named
          (Named.exact y)))
      (Name.named
        (Named.exact (x + y))) := by
  let xInput := Named.exact x
  let yInput := Named.exact y
  let sumInput := Named.exact (x + y)
  let xExponent := DyadicReduction.rangeExponent xInput
  let yExponent := DyadicReduction.rangeExponent yInput
  let sumExponent := DyadicReduction.rangeExponent sumInput
  let xUnit := automaticExactDyadicScale_unit x
  let yUnit := automaticExactDyadicScale_unit y
  let sumUnit := automaticExactDyadicScale_unit (x + y)
  let xAutomatic := Coherent.exp xInput
  let yAutomatic := Coherent.exp yInput
  let xDyadic := exactDyadicExpCoherent xExponent x xUnit
  let yDyadic := exactDyadicExpCoherent yExponent y yUnit
  have factorsToDyadic :
      NamedEquivalent
        (Named.mul
          xAutomatic.name yAutomatic.name)
        (Named.mul
          xDyadic.name yDyadic.name) :=
    Congruence.coherentMul_respects xAutomatic xDyadic yAutomatic yDyadic
      (automaticExactExp_toDyadic x)
      (automaticExactExp_toDyadic y)
  have dyadicLaw :
      NamedEquivalent
        (Named.mul
          xDyadic.name yDyadic.name)
        (exactDyadicExpCoherent sumExponent (x + y) sumUnit).name :=
    exactDyadicExp_add_independent xExponent yExponent sumExponent x y
      xUnit yUnit sumUnit
  exact NamedEquivalent.trans
    factorsToDyadic
    (NamedEquivalent.trans dyadicLaw
      (NamedEquivalent.symm
        (automaticExactExp_toDyadic (x + y))))

/-- The automatic range exponent of the exact zero name is zero. -/
theorem rangeExponent_exact_zero :
    DyadicReduction.rangeExponent
      (Named.exact 0) = 0 := by
  decide

/-- The actual total automatic exponential sends the exact zero CCL name to the exact one CCL name operationally. -/
@[expose] def automaticExp_zero :
    NamedEquivalent
      (Name.named
        (Named.exact 0))
      (Named.exact 1) := by
  let zeroUnit : Norm.Basic.normSq (0 : Basic.Canonical) ≤ 1 := by decide
  have localToFinite : NamedEquivalent
      (Local.Exact.exactLocalExpNamed 0 zeroUnit)
      Zero.expZeroApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      (Equivalence.approximationEquivalentOfSamplesEq
        (Local.Exact.exactLocalExpApproximation 0 zeroUnit)
        Zero.expZeroApproximation
        (by intro index; rfl))
  have finiteToOne : NamedEquivalent
      Zero.expZeroApproximation.toNamed
      Constant.oneApproximation.toNamed :=
    Equivalence.approximationEquivalent_toNamed
      Zero.exp_zero_equivalent_one
  have oneToExact : NamedEquivalent
      Constant.oneApproximation.toNamed
      (Named.exact 1) :=
    NamedEquivalent.symm
      (Exact.exact_toConstantNamed 1)
  have dyadicToOne : NamedEquivalent
      (exactDyadicExpCoherent
        (DyadicReduction.rangeExponent
          (Named.exact 0))
        0 (automaticExactDyadicScale_unit 0)).name
      (Named.exact 1) := by
    simpa only [rangeExponent_exact_zero,
      exactDyadicExpCoherent,
        Dyadic.dyadicScale, Power.squareIterate] using
      NamedEquivalent.trans
        localToFinite
        (NamedEquivalent.trans
          finiteToOne oneToExact)
  exact NamedEquivalent.trans
    (automaticExactExp_toDyadic 0) dyadicToOne

end

end Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
