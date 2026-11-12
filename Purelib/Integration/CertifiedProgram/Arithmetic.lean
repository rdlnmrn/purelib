module

public import Purelib.Integration.CertifiedProgram.Comparison
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Arithmetic.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Arithmetic of original retained certified-program caches -/

public section

namespace Purelib.Integration.CertifiedProgram

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {FirstModel : Type u} {LastModel : Type v}
  {firstOperations : ModelOperations FirstModel} {lastOperations : ModelOperations LastModel}

namespace ModelOperations

/-- Sum operations read both supplied whole original caches and combine their saved sample and allowance.

The model is the pair of the actual existing caches. The sample is their
sum, and twice the sum of their saved allowances pays the squared sum
estimate. No original model operation or cache producer is rerun.
-/
def add (first : ModelOperations FirstModel) (last : ModelOperations LastModel) :
    ModelOperations (CachedModel first × CachedModel last) where
  sample model := model.1.sample + model.2.sample
  allowance model := 2 * (model.1.allowance + model.2.allowance)

/-- Sum sampling reads the two supplied whole caches' saved sample fields. -/
theorem add_sample (first : ModelOperations FirstModel) (last : ModelOperations LastModel)
    (model : CachedModel first × CachedModel last) :
    (first.add last).sample model = model.1.sample + model.2.sample := by
  unfold add
  rfl

/-- Sum allowance reads the actual two cached allowances with the original squared-sum factor. -/
theorem add_allowance (first : ModelOperations FirstModel) (last : ModelOperations LastModel)
    (model : CachedModel first × CachedModel last) :
    (first.add last).allowance model = 2 * (model.1.allowance + model.2.allowance) := by
  unfold add
  rfl

end ModelOperations

namespace CachedModel

/-- Retain both actual original caches and compute their sum readbacks once.

The existing pair model preserves both supplied nominal cache parents,
models and defining equations. Its two readbacks consume their saved
sample and allowance fields directly.
-/
def add (first : CachedModel firstOperations) (last : CachedModel lastOperations) :
    CachedModel (firstOperations.add lastOperations) :=
  canonical (first, last)

/-- A retained sum's model is the literal pair of both original whole caches. -/
theorem add_model (first : CachedModel firstOperations) (last : CachedModel lastOperations) :
    (first.add last).model = (first, last) := by
  unfold add canonical
  rfl

/-- The retained sum's sample adds the two supplied cached samples. -/
theorem add_sample (first : CachedModel firstOperations) (last : CachedModel lastOperations) :
    (first.add last).sample = first.sample + last.sample := by
  unfold add canonical ModelOperations.add
  rfl

/-- The retained sum's allowance combines the two actual supplied cached allowances. -/
theorem add_allowance (first : CachedModel firstOperations) (last : CachedModel lastOperations) :
    (first.add last).allowance = 2 * (first.allowance + last.allowance) := by
  unfold add canonical ModelOperations.add
  rfl

end CachedModel

namespace Program

/-- Add two original certified programmes through their actual retained stage caches.

Each stage selects each supplied programme cache once and stores that
literal pair. The original geometric addition supplies its movement and
magnitude certificates. Allowances consume the same original saved fields;
no path-model replacement or caller-supplied Cauchy certificate is needed.
-/
def add (first : Program firstOperations) (last : Program lastOperations) :
    Program (firstOperations.add lastOperations) :=
  let source := first.geometric.add last.geometric
  { stage index := (first.stage index).add (last.stage index)
    errorScale := source.errorScale
    errorScale_nonneg := source.errorScale_nonneg
    modelAllowance_le := by
      intro index
      rewrite [CachedModel.add_allowance]
      change 2 * ((first.stage index).allowance + (last.stage index).allowance) ≤
        Basic.quarterRadius (2 * (first.errorScale + last.errorScale)) index
      apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (first.modelAllowance_le index)
          (last.modelAllowance_le index)) (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow,
        Basic.quarterRadius_eq_mul_pow]
      ring1
    later_close := by
      intro earlier later order
      change Norm.Basic.normSq (((first.stage later).sample + (last.stage later).sample) -
        ((first.stage earlier).sample + (last.stage earlier).sample)) ≤ _
      exact source.later_close order
    centerBound := source.centerBound
    centerBound_nonneg := source.centerBound_nonneg
    sample_bounded := by
      intro index
      change Norm.Basic.normSq ((first.stage index).sample + (last.stage index).sample) ≤ _
      exact source.sample_bounded index }

/-- Each sum stage is exactly the one original cache-pair construction on the two selected original stages. -/
theorem add_stage (first : Program firstOperations) (last : Program lastOperations) (index : Nat) :
    (first.add last).stage index = (first.stage index).add (last.stage index) := by
  unfold add
  rfl

/-- The actual certified sum sample reads the same two retained source stage caches. -/
theorem add_sample (first : Program firstOperations) (last : Program lastOperations) (index : Nat) :
    ((first.add last).stage index).sample = (first.stage index).sample + (last.stage index).sample := by
  rewrite [add_stage, CachedModel.add_sample]
  rfl

/-- The sum's geometric movement scale is twice the sum of its original input scales. -/
theorem add_errorScale (first : Program firstOperations) (last : Program lastOperations) :
    (first.add last).errorScale = 2 * (first.errorScale + last.errorScale) := by
  unfold add geometric Geometric.GeometricApproximation.add
  rfl

/-- Adding the original output channels realizes the same retained certified sum programme.

The original finite pointwise-sum comparison consumes the actual source
approximations. The exact stage-sample readback derives the output
comparison without assuming integral or geometric-path equivalence.
-/
def add_output_equivalent (first : Program firstOperations) (last : Program lastOperations)
    (combined : { value : Program (firstOperations.add lastOperations) // value = first.add last } :=
      ⟨first.add last, rfl⟩) :
    NamedEquivalent (first.output.add last.output).name combined.val.output.name := by
  have samples (index : Nat) : (combined.val.stage index).sample =
      (first.stage index).sample + (last.stage index).sample :=
    (congrArg (fun value => (value.stage index).sample) combined.property).trans (add_sample first last index)
  simpa only [output, Name.Coherent.CoherentNamed.add, Name.Coherent.CoherentNamed.ofApproximation] using
    Arithmetic.Sampling.addToNamed_equivalent_pointwise first.approximation last.approximation
      combined.val.approximation samples

section Four

variable {ThirdModel : Type w} {FourthModel : Type x}
  {thirdOperations : ModelOperations ThirdModel} {fourthOperations : ModelOperations FourthModel}

/-- Retain a balanced sum of four supplied whole programmes and its actual four-input output comparison.

The source order is first, second, third, fourth. Each of the three binary
sum programmes is computed once, then passed to its own original output
comparison. Every resulting stage retains all four original whole caches.
-/
def addFour (first : Program firstOperations) (second : Program lastOperations)
    (third : Program thirdOperations) (fourth : Program fourthOperations) :
    (produced : Program ((firstOperations.add lastOperations).add (thirdOperations.add fourthOperations))) ×
      NamedEquivalent ((first.output.add second.output).add (third.output.add fourth.output)).name
        produced.output.name := by
  let earlier := first.add second
  let later := third.add fourth
  let produced := earlier.add later
  have firstPair := first.add_output_equivalent second ⟨earlier, rfl⟩
  have lastPair := third.add_output_equivalent fourth ⟨later, rfl⟩
  have pairs := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (first.output.add second.output) earlier.output
    (third.output.add fourth.output) later.output firstPair lastPair
  exact ⟨produced, pairs.trans (earlier.add_output_equivalent later ⟨produced, rfl⟩)⟩

/-- The complete balanced four-programme result retains the original three binary additions literally. -/
theorem addFour_program (first : Program firstOperations) (second : Program lastOperations)
    (third : Program thirdOperations) (fourth : Program fourthOperations) :
    (first.addFour second third fourth).1 = (first.add second).add (third.add fourth) := by
  unfold addFour
  rfl

end Four

end Program

end Purelib.Integration.CertifiedProgram

end
