module

public import Purelib.Integration.CertifiedProgram.Comparison
public import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Geometric.Comparison
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Certified programmes retaining source caches and actual original observation requests -/

public section

namespace Purelib.Integration.CertifiedProgram.Observation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

variable {SourceModel : Type u} {sourceOperations : ModelOperations SourceModel}

/-- The same supplied whole original source cache with its exact requested stage and producer identity. -/
@[expose] def SourceCache (source : Program sourceOperations) (index : Nat) :=
  { value : CachedModel sourceOperations // value = source.stage index }

/-- Each displayed observation target may read its same supplied original source cache at that stage. -/
abbrev Targets (source : Program sourceOperations) :=
  (index : Nat) → SourceCache source index → Fraction.Rational

/-- One stage retains the original source cache and whole paid observation request under both original parents.

The model is the existing dependent pair of index, exact supplied source
cache and actual original Request. The numerical target reads that same
retained cache; it does not reconstruct the source's stage or child caches.
-/
@[expose] def Model (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source) :=
  (index : Nat) × (cached : SourceCache source index) × Equivalence.Observation.Request original (targets index cached)

/-- The weighted sample uses the same saved Request reading and same saved original source sample. -/
def operations (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source) :
    ModelOperations (Model original source targets) where
  sample model := model.2.2.reading.value * model.2.1.val.sample
  allowance _ := 0

/-- The weighted operation reads the same actual whole source cache and original retained Request reading. -/
theorem operations_sample (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (model : Model original source targets) :
    (operations original source targets).sample model = model.2.2.reading.value * model.2.1.val.sample :=
  (rfl)

/-- Retain one original source cache and compute one Request using that same supplied whole cache. -/
private def buildModel (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached) (index : Nat) : Model original source targets :=
  let actual := source.stage index
  let cached : SourceCache source index := ⟨actual, rfl⟩
  let request := Equivalence.Observation.Request.build original (targets index cached) (positive index cached)
  ⟨index, cached, request⟩

/-- Actual saved Request readings have geometric movement from their own original semantic payments. -/
private def requestApproximation (original : CoherentNamed) (source : Program sourceOperations)
    (targets : Targets source)
    (entries : (index : Nat) → (cached : SourceCache source index) ×
      Equivalence.Observation.Request original (targets index cached))
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) :
    Geometric.GeometricApproximation where
  sample index := (entries index).2.reading.value
  errorScale := 8
  errorScale_nonneg := by decide +kernel
  later_close := by
    intro earlier later order
    let first := entries later
    let last := entries earlier
    have firstPaid := first.2.allowance_lt.trans_le
      ((bounded later first.1).trans (Basic.quarterRadius_antitone (by decide) order))
    have lastPaid := last.2.allowance_lt.trans_le (bounded earlier last.1)
    have close := original.coherent.possible_close first.2.reading.possible last.2.reading.possible
    have paid := Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide +kernel : (0 : Fraction.Rational) < 4)
      (Arithmetic.add_lt_add_direct firstPaid lastPaid)
    have grouped : 4 * (Basic.quarterRadius 1 earlier + Basic.quarterRadius 1 earlier) =
        Basic.quarterRadius 8 earlier := by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1
    exact close.trans (paid.le.trans_eq grouped)
  centerBound := 2 * (1 + original.name.process.centerBound)
  centerBound_nonneg := Arithmetic.mul_nonneg_direct (by decide) (by
    change (0 : Fraction.Rational) + 0 ≤ 1 + original.name.process.centerBound
    exact Arithmetic.add_le_add_direct (by decide) original.name.process.centerBound_nonneg)
  sample_bounded := by
    intro index
    let actual := entries index
    have allowance := actual.2.allowance_lt.le.trans
      ((bounded index actual.1).trans (Basic.quarterRadius_le_scale (by decide) index))
    exact (original.coherent.possible_normSq_le actual.2.reading.possible).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct allowance (Fraction.Order.Basic.le_refl _)) (by decide))

/-- Actual saved Requests realize their original coherent input through independently paid canonical samples. -/
private def request_equivalent (original : CoherentNamed) (source : Program sourceOperations)
    (targets : Targets source)
    (entries : (index : Nat) → (cached : SourceCache source index) ×
      Equivalence.Observation.Request original (targets index cached))
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) :
    NamedEquivalent
      (requestApproximation original source targets entries bounded).toApproximation.toNamed original.name := by
  let indices := fun index => Search.firstQuarterBelow 1 index
    (original.coherent.accuracyRequest (Basic.quarterRadius 1 index))
  have floor (index : Nat) : index ≤ indices index := Search.firstQuarterBelow_ge _ _ _
  let canonical := Geometric.GeometricApproximation.ofNamed original.name
  let selected := canonical.selectStages indices floor
  let observed := requestApproximation original source targets entries bounded
  have distance (index : Nat) : Norm.Basic.normSq (observed.sample index - selected.sample index) ≤
      Basic.quarterRadius 8 index := by
    let actual := entries index
    have targetPositive := Basic.quarterRadius_pos (by decide : (0 : Fraction.Rational) < 1) index
    have readingPaid := actual.2.allowance_lt.trans_le (bounded index actual.1)
    have samplerPaid := Search.firstQuarterBelow_accurate 1 (by decide) index
      (original.coherent.accuracyRequest (Basic.quarterRadius 1 index))
      (original.coherent.accuracyRequest_pos targetPositive)
    have close := actual.2.reading.sample_distance_le targetPositive readingPaid (indices index) samplerPaid
    have grouped : 8 * Basic.quarterRadius 1 index = Basic.quarterRadius 8 index := by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1
    change Norm.Basic.normSq (actual.2.reading.value - (canonical.selectStages indices floor).sample index) ≤ _
    rewrite [Geometric.GeometricApproximation.selectStages_sample, Geometric.GeometricApproximation.ofNamed_sample]
    exact close.trans_eq grouped
  let compared := observed.equivalentOfSamplesClose selected 8 (by decide) distance
  let unselect := (canonical.selectedStages_equivalent indices floor).symm
  let actual := (compared.trans unselect).withSamples observed.toApproximation
    (Name.Sampling.approximation original.name) (fun _ => rfl) (fun _ => rfl)
  exact (Sequence.Name.Equivalence.approximationEquivalent_toNamed actual).trans
    (Sequence.Name.Equivalence.named_toSamplingNamed original.name).symm

/-- The same actual weighted cache sample is the product of its Request-reading stream and original source stream. -/
private theorem sample_eq (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) (index : Nat) :
    (CachedModel.canonical (operations := operations original source targets)
      (buildModel original source targets positive index)).sample =
    ((requestApproximation original source targets
      (fun stage => (buildModel original source targets positive stage).2) bounded).mul
        source.geometric).sample index := by
  rewrite [Geometric.GeometricApproximation.mul_sample]
  unfold CachedModel.canonical operations requestApproximation
  exact congrArg (fun value => (buildModel original source targets positive index).2.2.reading.value * value)
    (congrArg (fun value => value.sample) (buildModel original source targets positive index).2.1.property)

/-- Build a weighted observation programme using each actual source stage and Request exactly once.

The target reads the retained source cache. That same cache supplies its
sample, and its paired Request supplies the multiplier. Original coherence
and the computed target bound derive the Request stream's Cauchy and
magnitude bounds; original geometric multiplication supplies the weighted
programme certificates. No output equality or successful integration is
assumed. The original source's whole caches remain stored in every stage.
-/
def program (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) :
    Program (operations original source targets) :=
  let approximation := (requestApproximation original source targets
      (fun stage => (buildModel original source targets positive stage).2) bounded).mul source.geometric
  { stage index := .canonical (buildModel original source targets positive index)
    errorScale := approximation.errorScale
    errorScale_nonneg := approximation.errorScale_nonneg
    modelAllowance_le := fun index => Basic.quarterRadius_nonneg approximation.errorScale_nonneg index
    later_close := by
      intro earlier later order
      rewrite [sample_eq original source targets positive bounded later,
        sample_eq original source targets positive bounded earlier]
      exact approximation.later_close order
    centerBound := approximation.centerBound
    centerBound_nonneg := approximation.centerBound_nonneg
    sample_bounded := by
      intro index
      rewrite [sample_eq original source targets positive bounded index]
      exact approximation.sample_bounded index }

/-- Every actual weighted stage retains the complete once-produced source cache and its same original Request. -/
theorem program_stage (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) (index : Nat) :
    (program original source targets positive bounded).stage index =
      CachedModel.canonical (operations := operations original source targets)
        ⟨index, ⟨source.stage index, rfl⟩,
          Equivalence.Observation.Request.build original (targets index ⟨source.stage index, rfl⟩)
            (positive index ⟨source.stage index, rfl⟩)⟩ := by
  unfold program buildModel
  rfl

/-- The weighted programme sample reads its same retained Request and original source sample fields. -/
theorem program_sample (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index) (index : Nat) :
    let actual := (program original source targets positive bounded).stage index
    actual.sample = actual.model.2.2.reading.value * actual.model.2.1.val.sample :=
  ((program original source targets positive bounded).stage index).sample_eq.trans
    (operations_sample original source targets ((program original source targets positive bounded).stage index).model)

/-- The exact supplied whole programme producer retains its requested original stage index. -/
private theorem retainedIndex (original : CoherentNamed) (source : Program sourceOperations)
    (targets : Targets source) (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index)
    (produced : { value : Program (operations original source targets) //
      value = program original source targets positive bounded }) (index : Nat) :
    (produced.val.stage index).model.1 = index :=
  (congrArg (fun value : Program (operations original source targets) => (value.stage index).model.1)
    produced.property).trans
    (congrArg (fun value : CachedModel (operations original source targets) => value.model.1)
      (program_stage original source targets positive bounded index))

/-- Read the actual supplied programme stage's same whole source cache and Request at its requested index. -/
private def retainedEntries (original : CoherentNamed) (source : Program sourceOperations)
    (targets : Targets source) (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index)
    (produced : { value : Program (operations original source targets) //
      value = program original source targets positive bounded }) (index : Nat) :
    (cached : SourceCache source index) × Equivalence.Observation.Request original (targets index cached) := by
  let actual := produced.val.stage index
  have indexed := retainedIndex original source targets positive bounded produced index
  exact Eq.mp (congrArg (fun stage => (cached : SourceCache source stage) ×
    Equivalence.Observation.Request original (targets stage cached)) indexed) actual.model.2

/-- The transported actual retained Request and source cache preserve their whole weighted sample. -/
private theorem retainedEntries_sample (original : CoherentNamed) (source : Program sourceOperations)
    (targets : Targets source) (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index)
    (produced : { value : Program (operations original source targets) //
      value = program original source targets positive bounded }) (index : Nat) :
    let actual := retainedEntries original source targets positive bounded produced index
    actual.2.reading.value * actual.1.val.sample = (produced.val.stage index).sample := by
  have readback (first last : Nat) (same : first = last)
      (entry : (cached : SourceCache source first) ×
        Equivalence.Observation.Request original (targets first cached)) :
      let moved := Eq.mp (congrArg (fun stage => (cached : SourceCache source stage) ×
        Equivalence.Observation.Request original (targets stage cached)) same) entry
      moved.2.reading.value * moved.1.val.sample = entry.2.reading.value * entry.1.val.sample := by
    cases same
    rfl
  unfold retainedEntries
  exact (readback (produced.val.stage index).model.1 index
    (retainedIndex original source targets positive bounded produced index)
    (produced.val.stage index).model.2).trans (produced.val.stage index).sample_eq.symm

/-- The actual weighted programme realizes the original coherent multiplier times the same supplied source output.

The Request stream projects the supplied programme's actual retained
stages. Original semantic payments compare those same readings to
independently paid canonical samples. The finite multiplication bridge
consumes the actual product samples. It does not rebuild a canonical
Request stream in place of the supplied programme's original stages.
-/
def output_equivalent (original : CoherentNamed) (source : Program sourceOperations) (targets : Targets source)
    (positive : ∀ index cached, 0 < targets index cached)
    (bounded : ∀ index cached, targets index cached ≤ Basic.quarterRadius 1 index)
    (produced : { value : Program (operations original source targets) //
      value = program original source targets positive bounded } :=
        ⟨program original source targets positive bounded, rfl⟩) :
    NamedEquivalent (original.mul source.output).name produced.val.output.name := by
  let entries := retainedEntries original source targets positive bounded produced
  let observed := requestApproximation original source targets entries bounded
  let named := Name.Coherent.CoherentNamed.ofApproximation observed.toApproximation
  have agrees := request_equivalent original source targets entries bounded
  let replaced := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    original named source.output source.output agrees.symm (NamedEquivalent.refl _)
  have samples (index : Nat) : produced.val.approximation.sample index =
      observed.toApproximation.sample index * source.approximation.sample index := by
    let actual := entries index
    have sourceSample := congrArg (fun value : CachedModel sourceOperations => value.sample) actual.1.property
    exact (retainedEntries_sample original source targets positive bounded produced index).symm.trans
      (congrArg (fun value => actual.2.reading.value * value) sourceSample)
  have product := Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
    observed.toApproximation source.approximation produced.val.approximation samples
  exact replaced.trans product

end Purelib.Integration.CertifiedProgram.Observation

end
