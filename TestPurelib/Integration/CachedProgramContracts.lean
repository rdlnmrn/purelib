module

-- Complete former selected-output procedure requires access to its original opaque body.
import all Purelib.Integration.CertifiedProgram.Comparison
-- The complete former balanced producer is compared through the original generic arithmetic body.
import all Purelib.Integration.CertifiedProgram.Arithmetic
-- Complete former comparison agreement unfolds the one original finite geometric traversal.
import all Purelib.Approximation.Gaussian.Geometric.Comparison
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

import Purelib.Integration.CCL.Program
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Program.Gaussian

/-! Cached-program readbacks preserve finite models, samples and allowances.
The reference views check cache identities, refinement semantics and geometric
certificates against the certified program interface. -/

namespace TestPurelib.Integration.CachedProgramContracts

/-- The exact canonical rational scalar type. -/
private abbrev Coordinate := Fraction.Rational
/-- The exact canonical Gaussian-rational carrier. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The reference finite polynomial path model type. -/
private abbrev PathModel := Path.Basic.PathModel
/-- The reference certified Gaussian path-refinement program type. -/
private abbrev RefinementProgram := Basic.RefinementProgram
/-- The finite Gaussian approximation sequence with its retained bounds. -/
private abbrev Approximation := Gaussian.Sequence.ApproximationData
/-- The current cached Gaussian refinement-program type. -/
private abbrev ActualProgram := Cached.Basic.CachedProgram

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

set_option genInjectivity false in
/-- The reference finite path model with cached integral sample and aggregate allowance readbacks.

Both cached readings remain linked to the same finite path model by
exact sample and allowance equalities. These fields retain the reference layout. -/
private structure RetainedModel where
  /-- The reference retained finite path model. -/ model : PathModel
  /-- The cached exact Gaussian integral sample. -/ sample : Gaussian
  /-- The cached sample is exactly the reference model's integral sample. -/ sample_eq : sample = model.integralSample
  /-- The cached reference aggregate allowance. -/ allowance : Coordinate
  /-- The allowance is exactly the reference model's aggregate allowance. -/ allowance_eq : allowance =
    model.aggregateAllowance

constructive_injectivity RetainedModel

set_option genInjectivity false in
/-- The reference cached stage sequence with geometric error, cross-stage closeness and sample magnitude certificates.

The reference stage sequence supplies each retained model and cache.
Separate geometric, pairwise-distance and magnitude certificates accompany it. -/
private structure RetainedProgram where
  /-- The retained finite path model and scalar caches at each reference stage. -/ stage : Nat → RetainedModel
  /-- The reference nonnegative scale of the geometric squared-error allowance. -/ errorScale : Coordinate
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 ≤ errorScale
  /-- Every cached stage allowance fits its reference geometric quarter-radius bound. -/ modelAllowance_le : ∀ index,
    (stage index).allowance ≤ Basic.quarterRadius errorScale index
  /-- Later cached samples remain within the earlier stage's retained squared-error bound. -/ later_close : ∀ {earlier
    later : Nat}, earlier ≤ later →
    normSq ((stage later).sample - (stage earlier).sample) ≤
      Basic.quarterRadius errorScale earlier
  /-- The reference common bound on squared sample magnitude. -/ centerBound : Coordinate
  /-- The retained sample-magnitude bound is nonnegative. -/ centerBound_nonneg : 0 ≤ centerBound
  /-- Every reference cached sample satisfies the retained magnitude bound. -/ sample_bounded : ∀ index,
    normSq (stage index).sample ≤ centerBound

constructive_injectivity RetainedProgram

/-- Read the current cached program into the exact retained reference layout, preserving every cache and certificate. -/
private def retainProgram (program : ActualProgram) : RetainedProgram where
  stage index :=
    { model := (program.stage index).model
      sample := (program.stage index).sample
      sample_eq := (program.stage index).sample_eq
      allowance := (program.stage index).allowance
      allowance_eq := (program.stage index).allowance_eq }
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := program.later_close
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- Cache one reference finite path model's integral sample and aggregate allowance with reflexive readbacks. -/
private def retainedCanonical (model : PathModel) : RetainedModel :=
  { model := model
    sample := model.integralSample
    sample_eq := rfl
    allowance := model.aggregateAllowance
    allowance_eq := rfl }

/-- Expose the retained cached samples as their reference geometrically bounded approximation sequence. -/
private def retainedApproximation (program : RetainedProgram) : Approximation where
  sample index := (program.stage index).sample
  radiusSq := Basic.quarterRadius program.errorScale
  radiusSq_nonneg := Basic.quarterRadius_nonneg program.errorScale_nonneg
  later_close := program.later_close
  refineIndex current target _ := Search.firstQuarterBelow program.errorScale current target
  refineIndex_ge current target _ := Search.firstQuarterBelow_ge program.errorScale current target
  refineIndex_accurate := Search.firstQuarterBelow_accurate program.errorScale program.errorScale_nonneg
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- The cached sample readbacks transport cross-stage closeness to the exact reference finite-model integrals. -/
private theorem retainedLaterClose (program : RetainedProgram)
    {earlier later : Nat} (order : earlier ≤ later) :
    Data.Gaussian.Basic.Canonical.normSq
      ((program.stage later).model.integralSample -
        (program.stage earlier).model.integralSample) ≤
      Basic.quarterRadius program.errorScale earlier := by
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
    ← (program.stage later).sample_eq, ← (program.stage earlier).sample_eq]
  exact program.later_close (earlier := earlier) (later := later) order

/-- Recover the reference refinement program from its retained model sequence and cache certificates. -/
private def retainedSemantics (program : RetainedProgram) : RefinementProgram where
  model index := (program.stage index).model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [← (program.stage index).allowance_eq]
    exact program.modelAllowance_le index
  later_close := retainedLaterClose program
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
      ← (program.stage index).sample_eq]
    exact program.sample_bounded index

/-- The retained approximation sample equals the refinement program's exact model-integral sample. -/
private theorem retainedSampleSemantics (program : RetainedProgram) (index : Nat) :
    (retainedApproximation program).sample index = (retainedSemantics program).approximation.sample index :=
  (program.stage index).sample_eq

/-- Cache the reference refinement program's selected finite models without changing their integral samples or
allowances. -/
private def retainedOfProgram (program : RefinementProgram) : RetainedProgram where
  stage index := retainedCanonical (program.model index)
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    change normSq
      ((program.model later).integralSample - (program.model earlier).integralSample) ≤
        Basic.quarterRadius program.errorScale earlier
    exact (Data.Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le
      (program.later_close (earlier := earlier) (later := later) order)
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    change normSq
      (program.model index).integralSample ≤ program.centerBound
    exact (Data.Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le
      (program.sample_bounded index)

-- The reverse adapter exposes exactly the cache's actual selected model.
/-- Retaining the cached program and recovering its semantics preserves the exact referencely selected finite model. -/
example (program : ActualProgram) (index : Nat) :
    (retainedSemantics (retainProgram program)).model index = (program.stage index).model := rfl

-- The old semantic sample equality is precisely the retained cache readback.
/-- The cached program and recovered semantics expose the same exact approximation sample. -/
example (program : ActualProgram) (index : Nat) :
    program.approximation.sample index =
      (retainedSemantics (retainProgram program)).approximation.sample index :=
  retainedSampleSemantics (retainProgram program) index

/-- The retained reference program layout preserves the exact cached allowance. -/
example (program : ActualProgram) (index : Nat) :
    ((retainProgram program).stage index).allowance = (program.stage index).allowance := rfl

-- The new view retains the same producer and reference model/sample/allowance.
/-- The certified cached view retains the identical reference refinement producer. -/
example (program : RefinementProgram) : program.certifiedView.producer = program := rfl

/-- The retained reference adapter and current certified view select the same finite model. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).model =
      (program.certifiedView.program.stage index).model := rfl

/-- The retained reference adapter and current certified view retain the same cached sample. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).sample =
      (program.certifiedView.program.stage index).sample := rfl

/-- The retained reference adapter and current certified view retain the same cached allowance. -/
example (program : RefinementProgram) (index : Nat) :
    ((retainedOfProgram program).stage index).allowance =
      (program.certifiedView.program.stage index).allowance := rfl

/-- The retained reference adapter and current certified view preserve the same geometric error scale. -/
example (program : RefinementProgram) :
    (retainedOfProgram program).errorScale = program.certifiedView.program.errorScale := rfl

/-- Caching and recovering a refinement program preserves its exact selected model at each reference index. -/
example (program : RefinementProgram) (index : Nat) :
    (retainedSemantics (retainedOfProgram program)).model index = program.model index := rfl

/-- The complete former selected-output comparison before the optional saved-programme view. -/
private def formerSelectionComparison {Model : Type u} {operations : CertifiedProgram.ModelOperations Model}
    (program : CertifiedProgram.Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) :=
  program.output_equivalent_of_samples_close (program.selectStages indices floor)
    program.errorScale program.errorScale_nonneg (by
      intro index
      rewrite [CertifiedProgram.Program.selectStages_stage, Data.Gaussian.Norm.Bounds.normSq_sub_symm]
      exact program.later_close (floor index))

/-- Every original source and schedule retain the complete former default output-comparison procedure. -/
private theorem selection_default {Model : Type u} {operations : CertifiedProgram.ModelOperations Model}
    (program : CertifiedProgram.Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) :
    program.selectedStages_output_equivalent indices floor = formerSelectionComparison program indices floor := by
  unfold CertifiedProgram.Program.selectedStages_output_equivalent formerSelectionComparison
  rfl

section Four

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

/-- The complete balanced four-input producer previously embedded in the original cap loop owner. -/
private def formerFour {First : Type u} {Second : Type v}
    {firstOperations : CertifiedProgram.ModelOperations First}
    {secondOperations : CertifiedProgram.ModelOperations Second}
    {Third : Type w} {Fourth : Type x}
    {thirdOperations : CertifiedProgram.ModelOperations Third}
    {fourthOperations : CertifiedProgram.ModelOperations Fourth}
    (first : CertifiedProgram.Program firstOperations) (second : CertifiedProgram.Program secondOperations)
    (third : CertifiedProgram.Program thirdOperations) (fourth : CertifiedProgram.Program fourthOperations) :
    (produced : CertifiedProgram.Program
      ((firstOperations.add secondOperations).add (thirdOperations.add fourthOperations))) ×
      NamedEquivalent ((first.output.add second.output).add (third.output.add fourth.output)).name
        produced.output.name := by
  let earlier := first.add second
  let later := third.add fourth
  let produced := earlier.add later
  have firstPair := first.add_output_equivalent second ⟨earlier, rfl⟩
  have lastPair := third.add_output_equivalent fourth ⟨later, rfl⟩
  have pairs := Congruence.coherentAdd_respects
    (first.output.add second.output) earlier.output
    (third.output.add fourth.output) later.output firstPair lastPair
  exact ⟨produced, pairs.trans (earlier.add_output_equivalent later ⟨produced, rfl⟩)⟩

/-- The shared operation preserves the complete original programme-and-comparison pair for every four inputs. -/
private theorem four_default : @CertifiedProgram.Program.addFour = @formerFour := by
  unfold CertifiedProgram.Program.addFour formerFour
  rfl

end Four

section OutputComparison

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Nat.Order (le_max_left le_max_right)

variable {Model : Type u} {operations : CertifiedProgram.ModelOperations Model}
  {OtherModel : Type v} {otherOperations : CertifiedProgram.ModelOperations OtherModel}

/-- The complete former original same-stage sample/output comparison procedure. -/
private def formerOutputComparison (first : CertifiedProgram.Program operations)
    (last : CertifiedProgram.Program otherOperations)
    (bridge : CertifiedProgram.Coordinate) (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq ((first.stage index).sample - (last.stage index).sample) ≤
      Basic.quarterRadius bridge index) : NamedEquivalent first.output.name last.output.name := by
  let scale := 2 * (first.errorScale + 2 * (bridge + last.errorScale))
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg first.errorScale_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg nonnegative last.errorScale_nonneg)))
  have equivalent : Equivalence.Equivalent first.approximation last.approximation := by
    refine ⟨?_⟩
    intro leftStart rightStart target positive
    let common := Search.firstQuarterBelow scale (max leftStart rightStart) target
    have paid := Search.firstQuarterBelow_accurate scale scaleNonnegative (max leftStart rightStart) target positive
    refine
      { leftIndex := common
        rightIndex := common
        left_ge := (le_max_left _ _).trans (Search.firstQuarterBelow_ge _ _ _)
        right_ge := (le_max_right _ _).trans (Search.firstQuarterBelow_ge _ _ _)
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have left := first.later_close leftOrder
    have middle := distance common
    have right := last.later_close rightOrder
    rewrite [Norm.Bounds.normSq_sub_symm] at right
    have bounded := Norm.Bounds.normSq_sub_le_weighted_sum
      (first.stage leftLater).sample (first.stage common).sample
      (last.stage common).sample (last.stage rightLater).sample
      (Basic.quarterRadius first.errorScale common) (Basic.quarterRadius bridge common)
      (Basic.quarterRadius last.errorScale common) left middle right
    exact (bounded.trans_eq (Basic.quarterRadius_weighted_sum first.errorScale bridge last.errorScale common)).trans_lt
      paid
  exact Sequence.Name.Equivalence.approximationEquivalent_toNamed equivalent

/-- Every original model, cache, scale and distance certificate retains the complete former output procedure. -/
private theorem output_default :
    @CertifiedProgram.Program.output_equivalent_of_samples_close = @formerOutputComparison := by
  unfold CertifiedProgram.Program.output_equivalent_of_samples_close formerOutputComparison
    Geometric.GeometricApproximation.equivalentOfSamplesClose Geometric.GeometricApproximation.compareSamples
    Equivalence.Equivalent.withSamples Equivalence.Comparison.withSamples Equivalence.Comparison.weaken
  rfl

/-- The complete former original stage selection, including its literal original whole cache producer. -/
private def formerStageSelection (program : CertifiedProgram.Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) : CertifiedProgram.Program operations where
  stage index := program.stage (indices index)
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := fun index => (program.modelAllowance_le (indices index)).trans
    (Basic.quarterRadius_antitone program.errorScale_nonneg (floor index))
  later_close := by
    intro earlier later ordered
    if forward : indices earlier ≤ indices later then
      exact (program.later_close forward).trans
        (Basic.quarterRadius_antitone program.errorScale_nonneg (floor earlier))
    else
      have reverse : indices later ≤ indices earlier := Nat.le_of_lt (Nat.lt_of_not_ge forward)
      rewrite [Norm.Bounds.normSq_sub_symm]
      exact (program.later_close reverse).trans
        (Basic.quarterRadius_antitone program.errorScale_nonneg (ordered.trans (floor later)))
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := fun index => program.sample_bounded (indices index)

/-- Sharing the schedule proof preserves the complete former selected programme for every input and schedule. -/
private theorem stage_selection_default : @CertifiedProgram.Program.selectStages = @formerStageSelection := by
  unfold CertifiedProgram.Program.selectStages formerStageSelection
  rfl

end OutputComparison

end TestPurelib.Integration.CachedProgramContracts
