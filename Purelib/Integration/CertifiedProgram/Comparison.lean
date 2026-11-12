module

public import Purelib.Integration.CCL.Program
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Geometric.Comparison
import Purelib.Data.Rat.SmallWidth
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Bounded changes of actual certified-program samples

The original cache carriers and operations remain distinct. A proved
same-stage geometric distance bound supplies both the new programme's
Cauchy certificate and an executable comparison of the original outputs.
-/

public section

namespace Purelib.Integration.CertifiedProgram.Program

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Nat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

variable {Model : Type u} {operations : ModelOperations Model}
  {OtherModel : Type v} {otherOperations : ModelOperations OtherModel}

/-- Read the same retained certified samples with their original geometric movement and center bounds.

The view consumes the original stage caches directly, retaining the exact
error scale and center ceiling. It does not sample a rewrapped output,
select another model index or construct replacement integration models.
-/
@[expose] def geometric (program : Program operations) : Geometric.GeometricApproximation where
  sample index := (program.stage index).sample
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  later_close := program.later_close
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

/-- The geometric view reads the complete original cache's saved sample at exactly the same stage. -/
theorem geometric_sample (program : Program operations) (index : Nat) :
    program.geometric.sample index = (program.stage index).sample := rfl

/-- Compare the original certified output with the coherent name of its same-sample geometric view.

Both actual approximation owners are retained. Their exact cached samples
agree at every original index, so the existing finite sample comparison
supplies the operational agreement without assuming an output identity.
-/
@[expose] def output_equivalent_geometric (program : Program operations) :
    NamedEquivalent program.output.name (CoherentNamed.ofApproximation program.geometric.toApproximation).name := by
  simpa only [CoherentNamed.ofApproximation, output] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed
      (Sequence.Equivalence.approximationEquivalentOfSamplesEq
        program.approximation program.geometric.toApproximation (fun _ => rfl))

/-- The exact three-leg Cauchy scale of a geometric change to the original sample caches. -/
@[expose] def perturbationScale (program : Program operations) (bridge : Coordinate) : Coordinate :=
  2 * (bridge + 2 * (program.errorScale + bridge))

/-- The original nonnegative movement scale and bridge bound give a nonnegative changed-sample scale. -/
theorem perturbationScale_nonnegative (program : Program operations) (bridge : Coordinate)
    (nonnegative : 0 ≤ bridge) : 0 ≤ program.perturbationScale bridge :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg nonnegative (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg program.errorScale_nonneg nonnegative)))

/-- Certify supplied actual model caches from a proved geometric distance to one original programme.

The supplied stage function retains its own complete models and sample
caches. The original programme's actual Cauchy and center bounds derive
the new certificates; only its displayed local model allowances require
their own proof. No completed value or Cauchy certificate is assumed for
the new stage family.
-/
def perturb (program : Program operations) (stage : Nat → CachedModel otherOperations)
    (bridge : Coordinate) (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq ((stage index).sample - (program.stage index).sample) ≤
      Basic.quarterRadius bridge index)
    (allowances : Allowances stage (program.perturbationScale bridge)) : Program otherOperations where
  stage := stage
  errorScale := program.perturbationScale bridge
  errorScale_nonneg := program.perturbationScale_nonnegative bridge nonnegative
  modelAllowance_le := allowances
  later_close := by
    intro earlier later ordered
    have first := (distance later).trans (Basic.quarterRadius_antitone nonnegative ordered)
    have middle := program.later_close ordered
    have last := distance earlier
    rewrite [Norm.Bounds.normSq_sub_symm] at last
    have actual := Norm.Bounds.normSq_sub_le_weighted_sum
      (stage later).sample (program.stage later).sample (program.stage earlier).sample (stage earlier).sample
      (Basic.quarterRadius bridge earlier) (Basic.quarterRadius program.errorScale earlier)
      (Basic.quarterRadius bridge earlier) first middle last
    exact actual.trans_eq (Basic.quarterRadius_weighted_sum bridge program.errorScale bridge earlier)
  centerBound := 2 * (bridge + program.centerBound)
  centerBound_nonneg := Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg nonnegative program.centerBound_nonneg)
  sample_bounded := by
    intro index
    have paid := (distance index).trans (Basic.quarterRadius_le_scale nonnegative index)
    have original := program.sample_bounded index
    have identity : (stage index).sample =
        ((stage index).sample - (program.stage index).sample) + (program.stage index).sample := by ring1
    rewrite [identity]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct paid original) (by decide))

/-- The changed programme retains the complete supplied cache producer literally at every original stage. -/
theorem perturb_stage (program : Program operations) (stage : Nat → CachedModel otherOperations)
    (bridge : Coordinate) (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq ((stage index).sample - (program.stage index).sample) ≤
      Basic.quarterRadius bridge index)
    (allowances : Allowances stage (program.perturbationScale bridge)) (index : Nat) :
    ((program.perturb stage bridge nonnegative distance allowances).stage index) = stage index := by
  unfold perturb
  rfl

/-- Proved same-stage geometric distances yield an actual finite comparison of two original certified outputs.

The finite search pays both original movement scales and the displayed
bridge scale above both independently requested starts. The returned
comparison retains those paid indices and bounds every permitted later
pair of original cached samples.
-/
def output_equivalent_of_samples_close (first : Program operations) (last : Program otherOperations)
    (bridge : Coordinate) (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq ((first.stage index).sample - (last.stage index).sample) ≤
      Basic.quarterRadius bridge index) : NamedEquivalent first.output.name last.output.name := by
  let equivalent := Geometric.GeometricApproximation.equivalentOfSamplesClose first.geometric last.geometric
    bridge nonnegative distance
  exact Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (equivalent.withSamples first.approximation last.approximation (fun _ => rfl) (fun _ => rfl))

/-- Compare an original certified output to an actual geometric target with a retained uniform sample offset.

The original same-sample output bridge and bounded geometric comparison
pay both independently requested starts. The uniform offset remains in
the squared tolerance. No Cauchy certificate, vanishing error or equality
of the two outputs is assumed beyond the displayed actual sample bound.
-/
def compareGeometric (first : Program operations) (last : Geometric.GeometricApproximation)
    (offset bridge : Coordinate) (nonnegative : 0 ≤ bridge)
    (distance : ∀ index, Norm.Basic.normSq ((first.stage index).sample - last.sample index) ≤
      offset + Basic.quarterRadius bridge index)
    (leftStart rightStart : Nat) (target : Coordinate) (positive : 0 < target) :
    Equivalence.Comparison (Name.Sampling.approximation first.output.name)
      (Name.Sampling.approximation last.toApproximation.toNamed) leftStart rightStart (32 * offset + target) := by
  let precision := SmallWidth.shrinkingWidth 4 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Coordinate) ≤ 4) positive
  let original := first.output_equivalent_geometric.compare leftStart 0 precision precisionPositive
  let changed := first.geometric.compareNames last offset bridge nonnegative distance
    0 rightStart precision precisionPositive
  let compared := original.trans changed
  have scale : 2 * (precision + (16 * offset + precision)) = 32 * offset + 4 * precision := by ring1
  exact compared.weaken (32 * offset + target)
    (scale.trans_lt (Arithmetic.add_lt_add_left_direct paid _)).le

/-- Select the literal original stage caches at supplied indices above their actual requested stage floors.

The indices need not increase. Comparing the two selected source indices
in their actual order derives the original Cauchy bound; both indices
remain above the earlier requested floor. The source error and center
scales and the complete supplied source cache values are retained.
-/
def selectStages (program : Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) : Program operations where
  stage index := program.stage (indices index)
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := fun index => (program.modelAllowance_le (indices index)).trans
    (Basic.quarterRadius_antitone program.errorScale_nonneg (floor index))
  later_close := Geometric.GeometricApproximation.selectedSamples_close program.geometric indices floor
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := fun index => program.sample_bounded (indices index)

/-- Selection returns the complete literal original source cache at that same actual selected index. -/
theorem selectStages_stage (program : Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index) (index : Nat) :
    ((program.selectStages indices floor).stage index) = program.stage (indices index) := by
  unfold selectStages
  rfl

/-- Pay the original geometric error to compare a stage-selected programme with the same original source output.

The comparison keeps both original output owners and pays both requested
starts. It consumes the supplied whole selected programme and uses the source
Cauchy bound at each actual selected index. The default is the original
stage-selection procedure; no monotonic schedule or output identity is assumed.
-/
def selectedStages_output_equivalent (program : Program operations) (indices : Nat → Nat)
    (floor : ∀ index, index ≤ indices index)
    (selected : { value : Program operations // value = program.selectStages indices floor } :=
      ⟨program.selectStages indices floor, rfl⟩) :
    NamedEquivalent program.output.name selected.val.output.name :=
  program.output_equivalent_of_samples_close selected.val
    program.errorScale program.errorScale_nonneg (by
      intro index
      have same := (congrArg (fun value => (value.stage index).sample) selected.property).trans
        (congrArg (fun value => value.sample) (selectStages_stage program indices floor index))
      rewrite [same, Norm.Bounds.normSq_sub_symm]
      exact program.later_close (floor index))

end Purelib.Integration.CertifiedProgram.Program

end
