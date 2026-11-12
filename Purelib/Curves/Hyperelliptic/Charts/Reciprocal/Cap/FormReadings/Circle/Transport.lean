module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.Integration.CertifiedProgram.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Same-model negative-sheet cap integration programmes

Each new model retains its actual source model cache, the once-built signed
reading bank and its coefficient comparisons, and the original target stage.
Finite singleton partitions compare their actual same-mesh samples before
the original perturbation construction certifies the target programme.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Integration

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential reference : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}

namespace Model

/-- The exact nonnegative uniform allowance scale of the same-mesh signed observation comparison. -/
abbrev evenNegativeBudget : { value : Fraction.Rational // 0 ≤ value } := ⟨272, by decide +kernel⟩

/-- A retained source model, actual signed bank comparisons and original target stage, with its whole constructor law.

This existing Sigma view preserves both original model owners and the
actual coefficient comparisons. The target stage uses the same retained
edge cache; its supplied bank is the projection of those saved comparisons.
-/
abbrev EvenNegative (differential reference : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (left right : Endpoint)
    (referenceBudget : { value : Fraction.Rational // 0 ≤ value }) :=
  (source : CertifiedProgram.CachedModel
    (operations (differential := reference) (cap := cap) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) left right referenceBudget)) ×
  (bank : Readings.EvenNegative differential reference cap base unitBound collarBound actual
    source.model.1 left right (Basic.quarterRadius 1 source.model.1) source.model.2.1) ×
    { target : Model differential cap base unitBound collarBound actual left right evenNegativeBudget
        source.model.1 (fun _ => -1) //
      target = Stage.ofReadings (Readings.EvenNegative.readings bank)
        (some ⟨evenNegativeBudget.val * Basic.quarterRadius 1 source.model.1,
          Arithmetic.mul_nonneg_direct evenNegativeBudget.property
            (Basic.quarterRadius_nonneg (by decide) source.model.1)⟩) source.model.2.2.1 }

namespace EvenNegative

variable {left right : Endpoint} {referenceBudget : { value : Fraction.Rational // 0 ≤ value }}

/-- Read the target's same saved path through the original factor-indexed model operations. -/
def operations : CertifiedProgram.ModelOperations
    (EvenNegative differential reference cap base unitBound collarBound actual left right referenceBudget) where
  sample retained :=
    (Circle.operations left right evenNegativeBudget (fun _ => -1)).sample
      ⟨retained.1.model.1, retained.2.2.val⟩
  allowance retained :=
    (Circle.operations left right evenNegativeBudget (fun _ => -1)).allowance
      ⟨retained.1.model.1, retained.2.2.val⟩

/-- The signed operation reads the identical original target path's retained integral sample. -/
theorem sample_path
    (retained : EvenNegative differential reference cap base unitBound collarBound actual left right referenceBudget) :
    (operations (differential := differential) (reference := reference)).sample retained =
      retained.2.2.val.2.2.val.integralSample := by
  unfold operations
  exact Circle.operations_sample left right evenNegativeBudget
    ⟨retained.1.model.1, retained.2.2.val⟩

/-- Construct and retain one actual negative stage from the supplied whole source model cache.

The original source cache is not reacquired. Its bank is mapped once to
negative observations and their comparisons, and that projected bank feeds
the original stage constructor with the same exact stored edge cache.
-/
def build (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (source : CertifiedProgram.CachedModel
      (Circle.operations (differential := reference) (cap := cap) (base := base) (unitBound := unitBound)
        (collarBound := collarBound) (actual := actual) left right referenceBudget)) :
    EvenNegative differential reference cap base unitBound collarBound actual left right referenceBudget :=
  let bank := Readings.evenNegative differential reference cap pairs referencePairs sameNumerator oppositeScale
    base nonzero unitBound collarBound actual parity source.model.1 left right
    (Basic.quarterRadius 1 source.model.1) (Basic.quarterRadius_pos (by decide) source.model.1) source.model.2.1
  let readings := Readings.EvenNegative.readings bank
  let target := Stage.ofReadings readings
    (some ⟨evenNegativeBudget.val * Basic.quarterRadius 1 source.model.1,
      Arithmetic.mul_nonneg_direct evenNegativeBudget.property
        (Basic.quarterRadius_nonneg (by decide) source.model.1)⟩) source.model.2.2.1
  ⟨source, bank, ⟨target, rfl⟩⟩

/-- The signed model retains the complete supplied source model cache without reconstruction. -/
theorem build_source (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (source : CertifiedProgram.CachedModel
      (Circle.operations (differential := reference) (cap := cap) (base := base) (unitBound := unitBound)
        (collarBound := collarBound) (actual := actual) left right referenceBudget)) :
    (build nonzero pairs referencePairs sameNumerator oppositeScale parity source).1 = source := (rfl)

/-- The actual target path allowance is bounded at the source model's unchanged dyadic index. -/
theorem allowance_le
    (retained : EvenNegative differential reference cap base unitBound collarBound actual left right referenceBudget) :
    operations.allowance retained ≤ evenNegativeBudget.val * Basic.quarterRadius 1 retained.1.model.1 := by
  exact (Circle.operations_allowance left right evenNegativeBudget
    ⟨retained.1.model.1, retained.2.2.val⟩).trans_le
    (model_allowance_le left right evenNegativeBudget retained.1.model.1 retained.2.2.val)

/-- The actual saved target and source samples obey the finite same-mesh signed observation comparison. -/
theorem distance_le
    (retained : EvenNegative differential reference cap base unitBound collarBound actual left right referenceBudget) :
    Norm.Basic.normSq (operations.sample retained - retained.1.sample) ≤
      272 * Basic.quarterRadius 1 retained.1.model.1 := by
  let sourceAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨referenceBudget.val * Basic.quarterRadius 1 retained.1.model.1,
      Arithmetic.mul_nonneg_direct referenceBudget.property
        (Basic.quarterRadius_nonneg (by decide) retained.1.model.1)⟩
  have first := retained.1.sample_eq.trans
    (operations_sample left right referenceBudget retained.1.model)
  have source := first.trans (Stage.sample retained.1.model.2)
  have target := congrArg (fun value : Model differential cap base unitBound collarBound actual
      left right evenNegativeBudget retained.1.model.1 (fun _ => -1) => value.1)
    retained.2.2.property
  change retained.2.2.val.1 = Readings.EvenNegative.readings retained.2.1 at target
  have observed := sample_path retained
  rewrite [observed, source, Stage.sample retained.2.2.val, target]
  exact Readings.EvenNegative.integralSample_distance_le retained.2.1 (some sourceAllowance)
    (Basic.quarterRadius_pos (by decide) retained.1.model.1)

end EvenNegative

end Model

namespace Program

/-- Certify the actual negative even-sheet programme and compare its output with the supplied opposite-scale programme.

Every new stage retains the original source cache, signed observations and
actual comparisons. Its finite path difference pays the original geometric
perturbation and output-comparison procedures. The supplied index law only
identifies the original model's dyadic index with its requested stage.
-/
def evenNegative (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (left right : Endpoint) (referenceBudget : { value : Fraction.Rational // 0 ≤ value })
    (source : CertifiedProgram.Program
      (operations (differential := reference) (cap := cap) (base := base) (unitBound := unitBound)
        (collarBound := collarBound) (actual := actual) left right referenceBudget))
    (indices : ∀ index, (source.stage index).model.1 = index) :
    (target : CertifiedProgram.Program (Model.EvenNegative.operations
      (differential := differential) (reference := reference) (cap := cap) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) (left := left) (right := right)
      (referenceBudget := referenceBudget))) ×
        NamedEquivalent target.output.name source.output.name := by
  let stage := fun index => CertifiedProgram.CachedModel.canonical (operations := Model.EvenNegative.operations)
    (Model.EvenNegative.build nonzero pairs referencePairs sameNumerator oppositeScale parity (source.stage index))
  have distance : ∀ index, Norm.Basic.normSq ((stage index).sample - (source.stage index).sample) ≤
      Basic.quarterRadius 272 index := by
    intro index
    have bound := Model.EvenNegative.distance_le
      (Model.EvenNegative.build nonzero pairs referencePairs sameNumerator oppositeScale parity (source.stage index))
    rewrite [Model.EvenNegative.build_source] at bound
    exact bound.trans_eq (by
      rewrite [indices index, Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1)
  have allowances : CertifiedProgram.Allowances stage (source.perturbationScale 272) := by
    intro index
    have bound := Model.EvenNegative.allowance_le
      (Model.EvenNegative.build nonzero pairs referencePairs sameNumerator oppositeScale parity (source.stage index))
    rewrite [Model.EvenNegative.build_source] at bound
    have budgetFor (bridge : Fraction.Rational) (nonnegative : 0 ≤ bridge) :
        bridge ≤ source.perturbationScale bridge := by
      have extra := Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 5) nonnegative)
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
          source.errorScale_nonneg)
      rewrite [_root_.add_zero] at extra
      have reserve := Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl bridge) extra
      rewrite [_root_.add_zero] at reserve
      exact reserve.trans_eq (by unfold CertifiedProgram.Program.perturbationScale; ring1)
    have budget := budgetFor 272 Model.evenNegativeBudget.property
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct budget
      (Basic.quarterRadius_nonneg (by decide : (0 : Fraction.Rational) ≤ 1) index)
    exact (bound.trans_eq (by rewrite [indices index]; rfl)).trans
      (scaled.trans_eq (by rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]; ring1))
  let target := source.perturb stage 272 (by decide +kernel) distance allowances
  have equivalent := CertifiedProgram.Program.output_equivalent_of_samples_close target source 272 (by decide +kernel)
    (by
      intro index
      have saved := congrArg (fun cached => cached.sample)
        (CertifiedProgram.Program.perturb_stage source stage 272 (by decide +kernel) distance allowances index)
      rewrite [saved]
      exact distance index)
  exact ⟨target, equivalent⟩

end Program

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end
