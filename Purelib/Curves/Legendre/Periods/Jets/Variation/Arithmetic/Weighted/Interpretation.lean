module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Interpretation
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Weighted algebraic readings of the original finite parameter Taylor banks

One finite dependent spine stores interpretations of the original node
observations. The actual old and independently selected algebraic readings
pay their derived comparison bound at each node. The existing finite-sum
estimate and perturbation operation then attach both old weighted banks
to the selected algebraic readings with an explicit fourth-order remainder.
The original weights, numerical observations and Taylor certificates remain
inputs; these are finite samples, without a geometric period assertion.
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
variable {jets : (node : Fin count) →
  Sampling.SampledJet parameter increment (points node) (sources node) (targets node) unit}
variable {observations : NodeObservations jets} {weights : Data.Vector Canonical count}

/-- One materialized interpretation cache for each original finite node and all ten of its actual readings. -/
abbrev Interpretations (observations : NodeObservations jets) : Type 3 :=
  Vector.DependentVector (fun node => Arithmetic.Interpretations (observations node))

namespace Interpretations

/-- Interpret each original node's already retained numerical observations exactly once. -/
def build (observations : NodeObservations jets) : Interpretations observations :=
  Vector.DependentVector.ofFn (fun node => Arithmetic.Interpretations.build (observations node))

/-- Sum the actual selected algebraic source value readings with the unchanged original Gaussian weights. -/
@[expose] def sourceValue (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) : Canonical :=
  FiniteSum.Fin.sumFin (fun node =>
    weights node * (((retained.get node).sourceValue).get coordinate).requested.reading.value)

/-- Sum the actual selected algebraic target value readings with the unchanged original Gaussian weights. -/
@[expose] def targetValue (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) : Canonical :=
  FiniteSum.Fin.sumFin (fun node =>
    weights node * (((retained.get node).targetValue).get coordinate).requested.reading.value)

/-- Sum the actual selected algebraic source first derivative readings with the unchanged original Gaussian weights. -/
@[expose] def sourceFirst (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) : Canonical :=
  FiniteSum.Fin.sumFin (fun node =>
    weights node * (((retained.get node).sourceFirst).get coordinate).requested.reading.value)

/-- Sum the actual selected algebraic target first derivative readings with the unchanged original Gaussian weights. -/
@[expose] def targetFirst (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) : Canonical :=
  FiniteSum.Fin.sumFin (fun node =>
    weights node * (((retained.get node).targetFirst).get coordinate).requested.reading.value)

/-- Sum the actual selected algebraic source second derivative readings with the unchanged original Gaussian weights. -/
@[expose] def sourceSecond (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) : Canonical :=
  FiniteSum.Fin.sumFin (fun node =>
    weights node * (((retained.get node).sourceSecond).get coordinate).requested.reading.value)

end Interpretations

/-- The finite comparison factor retains the exact original weights and the derived two-radius payment. -/
@[expose] def interpretationFactor (weights : Data.Vector Canonical count) : Fraction.Rational :=
  (count : Fraction.Rational) *
    FiniteSum.Fin.sumFin (fun node => Norm.Basic.normSq (weights node) * (5 / 2 : Fraction.Rational))

/-- The original finite comparison factor is nonnegative, including empty families and zero weights. -/
theorem interpretationFactor_nonnegative (weights : Data.Vector Canonical count) :
    0 ≤ interpretationFactor weights :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
    (FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun node =>
      Fraction.Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg (weights node))
        (by decide +kernel : (0 : Fraction.Rational) ≤ 5 / 2)))

/-- The original finite-sum comparison pays its actual node-wise discrepancies at the shared increment. -/
private theorem weighted_error_le (first last : Fin count → Canonical)
    (weights : Data.Vector Canonical count)
    (bounded : ∀ node, Norm.Basic.normSq (first node - last node) ≤
      (5 / 2 : Fraction.Rational) * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * first node) -
        FiniteSum.Fin.sumFin (fun node => weights node * last node)) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  have bound := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    (fun node => weights node * first node) (fun node => weights node * last node)
    (fun node => (Norm.Basic.normSq (weights node) * (5 / 2 : Fraction.Rational)) *
      Norm.Basic.normSq increment ^ 2) (fun node => by
        rewrite [show weights node * first node - weights node * last node =
            weights node * (first node - last node) by ring1, Norm.Basic.normSq_mul]
        exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded node)
          (Norm.Basic.normSq_nonneg (weights node))).trans_eq (by ring1))
  exact bound.trans_eq (by
    rewrite [FiniteSum.Fin.sumFin_mul_right]
    unfold interpretationFactor
    ring1)

namespace Interpretations

/-- Compare the unchanged weighted numerical source value with the actual stored algebraic readings. -/
theorem sourceValue_error_le (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceValue coordinate).reading) -
        retained.sourceValue weights coordinate) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  apply weighted_error_le
  intro node
  have bound := (((retained.get node).sourceValue).get coordinate).error_lt.le
  rewrite [(jets node).accuracy_eq] at bound
  exact bound

/-- Compare the unchanged weighted numerical target value with the actual stored algebraic readings. -/
theorem targetValue_error_le (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetValue coordinate).reading) -
        retained.targetValue weights coordinate) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  apply weighted_error_le
  intro node
  have bound := (((retained.get node).targetValue).get coordinate).error_lt.le
  rewrite [(jets node).accuracy_eq] at bound
  exact bound

/-- Compare the unchanged weighted numerical source first derivative with the actual stored algebraic readings. -/
theorem sourceFirst_error_le (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceFirst coordinate).reading) -
        retained.sourceFirst weights coordinate) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  apply weighted_error_le
  intro node
  have bound := (((retained.get node).sourceFirst).get coordinate).error_lt.le
  rewrite [(jets node).accuracy_eq] at bound
  exact bound

/-- Compare the unchanged weighted numerical target first derivative with the actual stored algebraic readings. -/
theorem targetFirst_error_le (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).targetFirst coordinate).reading) -
        retained.targetFirst weights coordinate) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  apply weighted_error_le
  intro node
  have bound := (((retained.get node).targetFirst).get coordinate).error_lt.le
  rewrite [(jets node).accuracy_eq] at bound
  exact bound

/-- Compare the unchanged weighted numerical source second derivative with the actual stored algebraic readings. -/
theorem sourceSecond_error_le (retained : Interpretations observations) (weights : Data.Vector Canonical count)
    (coordinate : Fin 2) :
    Norm.Basic.normSq
      (FiniteSum.Fin.sumFin (fun node => weights node * ((observations node).sourceSecond coordinate).reading) -
        retained.sourceSecond weights coordinate) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  apply weighted_error_le
  intro node
  have bound := (((retained.get node).sourceSecond).get coordinate).error_lt.le
  rewrite [(jets node).accuracy_eq] at bound
  exact bound

end Interpretations

namespace Bank

/-- The actual original value base and its selected algebraic sum pay the stored finite comparison factor. -/
theorem value_base_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.sourceValue weights coordinate - (bank.value coordinate).base) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.value_base coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.sourceValue_error_le weights coordinate

/-- The actual original value output and its selected algebraic sum pay the stored finite comparison factor. -/
theorem value_output_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.targetValue weights coordinate - (bank.value coordinate).output) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.value_output coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.targetValue_error_le weights coordinate

/-- The actual original value slope and its selected algebraic sum pay the stored finite comparison factor. -/
theorem value_slope_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.sourceFirst weights coordinate - (bank.value coordinate).slope) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.value_slope coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.sourceFirst_error_le weights coordinate

/-- Attach the original weighted value certificate to its actual selected algebraic endpoints and slope.

The old numerical certificate and every original node observation remain
inputs. Three internally derived finite comparison bounds pay the new
readings through the existing perturbation constructor.
-/
def valueInterpretation (bank : Bank observations weights) (retained : Interpretations observations)
    (coordinate : Fin 2) : Certificate increment :=
  (bank.value coordinate).perturb (retained.sourceValue weights coordinate)
    (retained.targetValue weights coordinate) (retained.sourceFirst weights coordinate)
    (interpretationFactor weights) (interpretationFactor weights) (interpretationFactor weights)
    (interpretationFactor_nonnegative weights) (interpretationFactor_nonnegative weights)
    (interpretationFactor_nonnegative weights) unit
    (bank.value_base_interpretation_le retained coordinate)
    (bank.value_output_interpretation_le retained coordinate)
    (bank.value_slope_interpretation_le retained coordinate)

/-- The interpreted value certificate retains its actual selected algebraic base sum. -/
theorem valueInterpretation_base (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.valueInterpretation retained coordinate).base = retained.sourceValue weights coordinate := by
  unfold valueInterpretation
  rewrite [Certificate.perturb_base]
  rfl

/-- The interpreted value certificate retains its actual selected algebraic output sum. -/
theorem valueInterpretation_output (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.valueInterpretation retained coordinate).output = retained.targetValue weights coordinate := by
  unfold valueInterpretation
  rewrite [Certificate.perturb_output]
  rfl

/-- The interpreted value certificate retains its actual selected algebraic slope sum. -/
theorem valueInterpretation_slope (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.valueInterpretation retained coordinate).slope = retained.sourceFirst weights coordinate := by
  unfold valueInterpretation
  rewrite [Certificate.perturb_slope]
  rfl

/-- The interpreted value factor preserves its old factor and pays all three original-to-algebraic comparisons. -/
theorem valueInterpretation_factor (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.valueInterpretation retained coordinate).factor =
      4 * ((bank.value coordinate).factor + interpretationFactor weights +
        interpretationFactor weights + interpretationFactor weights) := by
  unfold valueInterpretation
  rewrite [Certificate.perturb_factor]
  rfl

/-- The actual original first base and its selected algebraic sum pay the stored finite comparison factor. -/
theorem first_base_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.sourceFirst weights coordinate - (bank.first coordinate).base) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.first_base coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.sourceFirst_error_le weights coordinate

/-- The actual original first output and its selected algebraic sum pay the stored finite comparison factor. -/
theorem first_output_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.targetFirst weights coordinate - (bank.first coordinate).output) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.first_output coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.targetFirst_error_le weights coordinate

/-- The actual original first slope and its selected algebraic sum pay the stored finite comparison factor. -/
theorem first_slope_interpretation_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Norm.Basic.normSq (retained.sourceSecond weights coordinate - (bank.first coordinate).slope) ≤
      interpretationFactor weights * Norm.Basic.normSq increment ^ 2 := by
  rewrite [bank.first_slope coordinate, Norm.Bounds.normSq_sub_symm]
  exact retained.sourceSecond_error_le weights coordinate

/-- Attach the original weighted first certificate to its actual selected algebraic endpoints and slope.

The old numerical certificate and every original node observation remain
inputs. Three internally derived finite comparison bounds pay the new
readings through the existing perturbation constructor.
-/
def firstInterpretation (bank : Bank observations weights) (retained : Interpretations observations)
    (coordinate : Fin 2) : Certificate increment :=
  (bank.first coordinate).perturb (retained.sourceFirst weights coordinate)
    (retained.targetFirst weights coordinate) (retained.sourceSecond weights coordinate)
    (interpretationFactor weights) (interpretationFactor weights) (interpretationFactor weights)
    (interpretationFactor_nonnegative weights) (interpretationFactor_nonnegative weights)
    (interpretationFactor_nonnegative weights) unit
    (bank.first_base_interpretation_le retained coordinate)
    (bank.first_output_interpretation_le retained coordinate)
    (bank.first_slope_interpretation_le retained coordinate)

/-- The interpreted first certificate retains its actual selected algebraic base sum. -/
theorem firstInterpretation_base (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.firstInterpretation retained coordinate).base = retained.sourceFirst weights coordinate := by
  unfold firstInterpretation
  rewrite [Certificate.perturb_base]
  rfl

/-- The interpreted first certificate retains its actual selected algebraic output sum. -/
theorem firstInterpretation_output (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.firstInterpretation retained coordinate).output = retained.targetFirst weights coordinate := by
  unfold firstInterpretation
  rewrite [Certificate.perturb_output]
  rfl

/-- The interpreted first certificate retains its actual selected algebraic slope sum. -/
theorem firstInterpretation_slope (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.firstInterpretation retained coordinate).slope = retained.sourceSecond weights coordinate := by
  unfold firstInterpretation
  rewrite [Certificate.perturb_slope]
  rfl

/-- The interpreted first factor preserves its old factor and pays all three original-to-algebraic comparisons. -/
theorem firstInterpretation_factor (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    (bank.firstInterpretation retained coordinate).factor =
      4 * ((bank.first coordinate).factor + interpretationFactor weights +
        interpretationFactor weights + interpretationFactor weights) := by
  unfold firstInterpretation
  rewrite [Certificate.perturb_factor]
  rfl

/-- The actual selected algebraic value readings satisfy their internally constructed finite Taylor estimate. -/
theorem valueInterpretation_remainder_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Canonical.normSq
      (retained.targetValue weights coordinate - retained.sourceValue weights coordinate -
        increment * retained.sourceFirst weights coordinate) ≤
      (4 * ((bank.value coordinate).factor + interpretationFactor weights +
        interpretationFactor weights + interpretationFactor weights)) * Canonical.normSq increment ^ 2 := by
  have bound := (bank.valueInterpretation retained coordinate).remainder_le
  rewrite [← (bank.valueInterpretation retained coordinate).expansion,
    bank.valueInterpretation_base retained coordinate,
    bank.valueInterpretation_output retained coordinate,
    bank.valueInterpretation_slope retained coordinate,
    bank.valueInterpretation_factor retained coordinate] at bound
  exact bound

/-- The actual selected algebraic first readings satisfy their internally constructed finite Taylor estimate. -/
theorem firstInterpretation_remainder_le (bank : Bank observations weights)
    (retained : Interpretations observations) (coordinate : Fin 2) :
    Canonical.normSq
      (retained.targetFirst weights coordinate - retained.sourceFirst weights coordinate -
        increment * retained.sourceSecond weights coordinate) ≤
      (4 * ((bank.first coordinate).factor + interpretationFactor weights +
        interpretationFactor weights + interpretationFactor weights)) * Canonical.normSq increment ^ 2 := by
  have bound := (bank.firstInterpretation retained coordinate).remainder_le
  rewrite [← (bank.firstInterpretation retained coordinate).expansion,
    bank.firstInterpretation_base retained coordinate,
    bank.firstInterpretation_output retained coordinate,
    bank.firstInterpretation_slope retained coordinate,
    bank.firstInterpretation_factor retained coordinate] at bound
  exact bound

end Bank

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Weighted

end
