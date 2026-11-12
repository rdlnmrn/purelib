module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Weighted.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Weighted Taylor samples on the retained original Legendre node observations

Source and target observations at each original spatial node keep the same
parameter increment and their own retained root and arithmetic owners.
Both finite coefficient-certificate banks are materialized once. The
identical supplied weight vector then forms their actual weighted Taylor
samples, with internally computed finite remainder factors.

These are weighted chart-node samples. No geometric integral, affine spatial
cell certificate or comparison with a period owner is asserted here.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted

open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)

open Purelib
open Purelib.Algebra
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

variable {count : Nat} {parameter increment : Canonical}
variable {points : Data.Vector Canonical count}
variable {sources : (node : Fin count) →
  CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter (points node))}
variable {targets : (node : Fin count) →
  CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) (points node))}
variable {unit : Norm.Basic.normSq increment ≤ 1}

/-- The exact original finite family of arithmetic observations on the retained node-wise sampled jets. -/
abbrev NodeObservations
    (jets : (node : Fin count) →
      Sampling.SampledJet parameter increment (points node) (sources node) (targets node) unit) : Type 1 :=
  (node : Fin count) → Observations (jets node)

variable {jets : (node : Fin count) →
  Sampling.SampledJet parameter increment (points node) (sources node) (targets node) unit}

set_option genInjectivity false in
/-- Materialized weighted value and first-derivative Taylor banks on the identical original node observations.

The original points, observations and Gaussian weights remain indices.
Every certificate entry is the complete original arithmetic construction,
and the two weighted banks consume these same cached entry vectors.
-/
structure Bank (observations : NodeObservations jets) (weights : Data.Vector Canonical count) where
  /-- The actual original value Taylor certificate entries, stored once for both differential rows. -/
  valueEntries : Data.Vector (Data.Vector (Certificate increment) count) 2
  /-- Each cached value entry is the complete construction on its identical original arithmetic observations. -/
  valueEntries_eq : ∀ coordinate node,
    valueEntries coordinate node = (observations node).valueCertificate coordinate
  /-- The actual original first derivative Taylor entries, retaining their independently observed second slopes. -/
  firstEntries : Data.Vector (Data.Vector (Certificate increment) count) 2
  /-- Each cached first entry is the complete original arithmetic first variation construction. -/
  firstEntries_eq : ∀ coordinate node,
    firstEntries coordinate node = (observations node).firstCertificate coordinate
  /-- The actual weighted value certificates computed from the same retained weights and entry vectors. -/
  value : Data.Vector (Certificate increment) 2
  /-- Every value sum retains the complete weighted construction on its exact cached entries. -/
  value_eq : ∀ coordinate, value coordinate = Certificate.weightedSum weights (valueEntries coordinate)
  /-- The actual weighted first derivative certificates constructed on the same original Gaussian weights. -/
  first : Data.Vector (Certificate increment) 2
  /-- Every first sum retains the complete construction on its identical cached first entries. -/
  first_eq : ∀ coordinate, first coordinate = Certificate.weightedSum weights (firstEntries coordinate)

constructive_injectivity Bank

namespace Bank

variable {observations : NodeObservations jets} {weights : Data.Vector Canonical count}

/-- Materialize both original entry banks once, then construct their weighted certificates from these exact caches. -/
@[expose] def build (observations : NodeObservations jets) (weights : Data.Vector Canonical count) :
    Bank observations weights :=
  let valueEntries := Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun node : Fin count => (observations node).valueCertificate coordinate))
  let firstEntries := Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun node : Fin count => (observations node).firstCertificate coordinate))
  let value := Data.Vector.Basic.vectorOfFn (fun coordinate =>
    Certificate.weightedSum weights (valueEntries coordinate))
  let first := Data.Vector.Basic.vectorOfFn (fun coordinate =>
    Certificate.weightedSum weights (firstEntries coordinate))
  { valueEntries := valueEntries
    valueEntries_eq := fun coordinate node => by
      change (Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Data.Vector.Basic.vectorOfFn (fun node : Fin count =>
          (observations node).valueCertificate coordinate))) coordinate node = _
      rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
      rfl
    firstEntries := firstEntries
    firstEntries_eq := fun coordinate node => by
      change (Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Data.Vector.Basic.vectorOfFn (fun node : Fin count =>
          (observations node).firstCertificate coordinate))) coordinate node = _
      rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
      rfl
    value := value
    value_eq := fun coordinate => Data.Vector.Basic.vectorOfFn_apply _ coordinate
    first := first
    first_eq := fun coordinate => Data.Vector.Basic.vectorOfFn_apply _ coordinate }

/-- The weighted value base sums the identical actual source value readings at the retained original nodes. -/
theorem value_base (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.value coordinate).base =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceValue coordinate).reading) := by
  rewrite [bank.value_eq coordinate, Certificate.weightedSum_base]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.valueEntries_eq coordinate node, Observations.valueCertificate_base]
  rfl

/-- The weighted value output preserves every actual target reading on the same retained original weight. -/
theorem value_output (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.value coordinate).output =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetValue coordinate).reading) := by
  rewrite [bank.value_eq coordinate, Certificate.weightedSum_output]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.valueEntries_eq coordinate node, Observations.valueCertificate_output]
  rfl

/-- The weighted value slope is the same weighted sum of the actual original source first derivative readings. -/
theorem value_slope (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.value coordinate).slope =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading) := by
  rewrite [bank.value_eq coordinate, Certificate.weightedSum_slope]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.valueEntries_eq coordinate node, Observations.valueCertificate_slope]
  rfl

/-- The first derivative weighted base preserves the identical original source first readings. -/
theorem first_base (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.first coordinate).base =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading) := by
  rewrite [bank.first_eq coordinate, Certificate.weightedSum_base]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.firstEntries_eq coordinate node, Observations.firstCertificate_base]
  rfl

/-- The first derivative weighted output keeps every independently observed original target first reading. -/
theorem first_output (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.first coordinate).output =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetFirst coordinate).reading) := by
  rewrite [bank.first_eq coordinate, Certificate.weightedSum_output]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.firstEntries_eq coordinate node, Observations.firstCertificate_output]
  rfl

/-- The weighted first slope sums the actual original source second derivative observations with the same weights. -/
theorem first_slope (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.first coordinate).slope =
      FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceSecond coordinate).reading) := by
  rewrite [bank.first_eq coordinate, Certificate.weightedSum_slope]
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.firstEntries_eq coordinate node, Observations.firstCertificate_slope]
  rfl

/-- The weighted value factor pays every original node's complete arithmetic Taylor factor separately. -/
theorem value_factor (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.value coordinate).factor = (count : Fraction.Rational) *
      FiniteSum.Fin.sumFin (fun node =>
        Norm.Basic.normSq (weights node) * ((observations node).valueCertificate coordinate).factor) := by
  rewrite [bank.value_eq coordinate, Certificate.weightedSum_factor]
  unfold Certificate.weightedFactor
  apply congrArg (fun total => (count : Fraction.Rational) * total)
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.valueEntries_eq coordinate node]
  rfl

/-- The weighted first factor retains each original node's independent second-slope arithmetic payment. -/
theorem first_factor (bank : Bank observations weights) (coordinate : Fin 2) :
    (bank.first coordinate).factor = (count : Fraction.Rational) *
      FiniteSum.Fin.sumFin (fun node =>
        Norm.Basic.normSq (weights node) * ((observations node).firstCertificate coordinate).factor) := by
  rewrite [bank.first_eq coordinate, Certificate.weightedSum_factor]
  unfold Certificate.weightedFactor
  apply congrArg (fun total => (count : Fraction.Rational) * total)
  apply FiniteSum.Fin.sumFin_congr
  intro node
  rewrite [bank.firstEntries_eq coordinate node]
  rfl

/-- Uniform node factors and the original dyadic weight payment bound the exact cached value factor at every depth. -/
theorem value_factor_le (bank : Bank observations weights) (coordinate : Fin 2)
    (depth : Nat) (count_eq : count = 2 ^ depth) (weightScale factorCeiling : Fraction.Rational)
    (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ node, Norm.Basic.normSq (weights node) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ node, ((observations node).valueCertificate coordinate).factor ≤ factorCeiling) :
    (bank.value coordinate).factor ≤ weightScale * factorCeiling := by
  rewrite [bank.value_eq coordinate, Certificate.weightedSum_factor]
  apply Certificate.dyadic_weightedFactor_le weights (bank.valueEntries coordinate)
    depth count_eq weightScale factorCeiling factorNonnegative weightBound
  intro node
  rewrite [bank.valueEntries_eq coordinate node]
  exact factorBound node

/-- The retained first-derivative bank has the same mesh-independent bound using its own original entry factors. -/
theorem first_factor_le (bank : Bank observations weights) (coordinate : Fin 2)
    (depth : Nat) (count_eq : count = 2 ^ depth) (weightScale factorCeiling : Fraction.Rational)
    (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ node, Norm.Basic.normSq (weights node) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ node, ((observations node).firstCertificate coordinate).factor ≤ factorCeiling) :
    (bank.first coordinate).factor ≤ weightScale * factorCeiling := by
  rewrite [bank.first_eq coordinate, Certificate.weightedSum_factor]
  apply Certificate.dyadic_weightedFactor_le weights (bank.firstEntries coordinate)
    depth count_eq weightScale factorCeiling factorNonnegative weightBound
  intro node
  rewrite [bank.firstEntries_eq coordinate node]
  exact factorBound node

/-- The actual weighted value sample obeys its internally computed finite Taylor remainder bound. -/
theorem value_remainder_le (bank : Bank observations weights) (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetValue coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceValue coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading)) ≤
      (bank.value coordinate).factor * Canonical.normSq increment ^ 2 := by
  have bound := (bank.value coordinate).remainder_le
  rewrite [← (bank.value coordinate).expansion, bank.value_base coordinate, bank.value_output coordinate,
    bank.value_slope coordinate] at bound
  exact bound

/-- The actual weighted first derivative sample obeys its finite bound with the retained weighted second slope. -/
theorem first_remainder_le (bank : Bank observations weights) (coordinate : Fin 2) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetFirst coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceSecond coordinate).reading)) ≤
      (bank.first coordinate).factor * Canonical.normSq increment ^ 2 := by
  have bound := (bank.first coordinate).remainder_le
  rewrite [← (bank.first coordinate).expansion, bank.first_base coordinate, bank.first_output coordinate,
    bank.first_slope coordinate] at bound
  exact bound

/-- The actual weighted value readings obey the common fourth-order remainder bound on every paid dyadic mesh. -/
theorem value_uniform_remainder_le (bank : Bank observations weights) (coordinate : Fin 2)
    (depth : Nat) (count_eq : count = 2 ^ depth) (weightScale factorCeiling : Fraction.Rational)
    (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ node, Norm.Basic.normSq (weights node) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ node, ((observations node).valueCertificate coordinate).factor ≤ factorCeiling) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetValue coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceValue coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading)) ≤
      weightScale * factorCeiling * Canonical.normSq increment ^ 2 :=
  (bank.value_remainder_le coordinate).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (bank.value_factor_le coordinate depth count_eq weightScale factorCeiling factorNonnegative
        weightBound factorBound)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Independently observed weighted first readings obey a common fourth-order bound on the same original mesh. -/
theorem first_uniform_remainder_le (bank : Bank observations weights) (coordinate : Fin 2)
    (depth : Nat) (count_eq : count = 2 ^ depth) (weightScale factorCeiling : Fraction.Rational)
    (factorNonnegative : 0 ≤ factorCeiling)
    (weightBound : ∀ node, Norm.Basic.normSq (weights node) ≤
      Approximation.Rational.Geometric.Basic.quarterRadius weightScale depth)
    (factorBound : ∀ node, ((observations node).firstCertificate coordinate).factor ≤ factorCeiling) :
    Canonical.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetFirst coordinate).reading) -
        FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading) -
        increment *
          FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceSecond coordinate).reading)) ≤
      weightScale * factorCeiling * Canonical.normSq increment ^ 2 :=
  (bank.first_remainder_le coordinate).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (bank.first_factor_le coordinate depth count_eq weightScale factorCeiling factorNonnegative
        weightBound factorBound)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end Bank

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted
