module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Refinement
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Retained integration programs for the actual cap form on one stored circle

The original whole reading banks and once-built path models remain the
models of the original certified program. Finite compatible refinements
supply its Cauchy estimate; the numerical coarse bank supplies its common
scale before any later-stage production lambda is built.
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
open Purelib.Riemann.Normalization
open Purelib.Approximation.Rational.Geometric
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Sequential (SequentialCompatibleConstantRefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement
  (comparisonAllowance)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}

/-- The original whole-bank stage with its original quarter-radius target and retained cell budget. -/
abbrev Model (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (base : Canonical)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base }) (left right : Endpoint)
    (budget : { value : Fraction.Rational // 0 ≤ value }) (index : Nat)
    (factors : Canonical → Canonical :=
      fun parameter => parameter ^ HyperellipticReciprocal.originOrder curve) :=
  Stage differential cap base unitBound collarBound actual index left right (Basic.quarterRadius 1 index)
    (some ⟨budget.val * Basic.quarterRadius 1 index,
      Arithmetic.mul_nonneg_direct budget.property (Basic.quarterRadius_nonneg (by decide) index)⟩)
    factors

/-- The original path sample and allowance readbacks on the same retained whole stage. -/
def operations (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (factors : Canonical → Canonical :=
      fun parameter => parameter ^ HyperellipticReciprocal.originOrder curve) :
    CertifiedProgram.ModelOperations
      (Σ index, Model differential cap base unitBound collarBound actual left right budget index factors) where
  sample model := model.2.2.2.val.integralSample
  allowance model := model.2.2.2.val.aggregateAllowance

/-- The operation reads the actual retained original path sample without rebuilding its bank or cells. -/
theorem operations_sample {factors : Canonical → Canonical}
    (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (model : Σ index, Model differential cap base unitBound collarBound actual left right budget index factors) :
    (operations left right budget factors).sample model = model.2.2.2.val.integralSample := by unfold operations; rfl

/-- The operation reads the same retained original path allowance. -/
theorem operations_allowance {factors : Canonical → Canonical}
    (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (model : Σ index, Model differential cap base unitBound collarBound actual left right budget index factors) :
    (operations left right budget factors).allowance model = model.2.2.2.val.aggregateAllowance := by
  unfold operations
  rfl

/-- Every actual retained model meets its scale times the original stage quarter radius. -/
theorem model_allowance_le {factors : Canonical → Canonical}
    (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (index : Nat) (model : Model differential cap base unitBound collarBound actual left right budget index factors) :
    model.2.2.val.aggregateAllowance ≤ budget.val * Basic.quarterRadius 1 index := by
  let allowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨budget.val * Basic.quarterRadius 1 index,
      Arithmetic.mul_nonneg_direct budget.property (Basic.quarterRadius_nonneg (by decide) index)⟩
  have count : model.2.2.val.cells.length = 2 ^ index := by
    rewrite [Stage.cells model]
    exact Readings.model_count model.1 (some allowance)
  have bounds := Readings.cells_bounds model.1 none allowance (Basic.quarterRadius 1 index)
    (dyadicEdges_parameterSquare_le index left right)
  rewrite [← Stage.cells model] at bounds
  exact (PathModel.uniform_aggregateAllowance_le model.2.2.val index 1 allowance.val (by decide) count bounds).trans_eq
    (Fraction.Field.one_mul _)

/-- The same actual retained bank family has the original compatible consecutive refinement. -/
private def steps
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (budgetSource : budget.val = Readings.allowanceScale cached bounds anchor)
    (family : ∀ index, Model differential cap base unitBound collarBound actual left right budget index)
    (canonical : ∀ index, (family index).1 = readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)) (index : Nat) :
    PathModel.CompatibleConstantPathRefinement (family index).2.2.val.cells (family (index + 1)).2.2.val.cells := by
  let precision := Basic.quarterRadius 1 index
  have positive := Basic.quarterRadius_pos (by decide : (0 : Fraction.Rational) < 1) index
  have next : Basic.quarterRadius 1 (index + 1) = precision / 4 := by
    dsimp only [precision]
    rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, pow_succ]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  let fine := (family (index + 1)).1.transportTarget next
  have fineCanonical : fine = readings differential cap base nonzero unitBound collarBound actual
      (index + 1) left right (precision / 4) (Fraction.Order.Field.div_pos_direct positive (by decide)) :=
    (congrArg (fun stored => stored.transportTarget next) (canonical (index + 1))).trans
      (Readings.transportTarget_readings differential cap base nonzero unitBound collarBound actual
        (index + 1) left right _ _ _ _ next)
  let refinement := Readings.compatible cached nonzero pairs degreeBound bounds anchor anchorCanonical
    precision positive (Basic.quarterRadius_le_scale (by decide) index) index left right
    (dyadicEdges_parameterSquare_le index left right) (family index).1 fine (canonical index) fineCanonical
  let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨budget.val * precision, Arithmetic.mul_nonneg_direct budget.property positive.le⟩
  let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨budget.val * Basic.quarterRadius 1 (index + 1), Arithmetic.mul_nonneg_direct budget.property
      (Basic.quarterRadius_nonneg (by decide) (index + 1))⟩
  have firstAllowance : parentAllowance =
      ⟨Readings.allowanceScale cached bounds anchor * precision,
        Arithmetic.mul_nonneg_direct
          (Readings.allowanceScale_nonnegative cached nonzero bounds anchor) positive.le⟩ :=
    Subtype.ext (congrArg (fun value => value * precision) budgetSource)
  have lastAllowance : childAllowance =
      ⟨Readings.allowanceScale cached bounds anchor * (precision / 4),
        Arithmetic.mul_nonneg_direct
          (Readings.allowanceScale_nonnegative cached nonzero bounds anchor)
          (Fraction.Order.Field.div_pos_direct positive (by decide)).le⟩ :=
    Subtype.ext (by change budget.val * Basic.quarterRadius 1 (index + 1) = _; rewrite [budgetSource, next]; rfl)
  rewrite [Stage.cells, Stage.cells]
  change PathModel.CompatibleConstantPathRefinement
    ((family index).1.cells none (some parentAllowance)) ((family (index + 1)).1.cells none (some childAllowance))
  rewrite [firstAllowance, lastAllowance, ← Readings.cells_transportTarget (family (index + 1)).1 next]
  exact refinement

/-- Derive the original sequential refinement program from the same complete canonical stage family. -/
private def sequential
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    (left right : Endpoint) (budget : { value : Fraction.Rational // 0 ≤ value })
    (budgetSource : budget.val = Readings.allowanceScale cached bounds anchor)
    (family : ∀ index, Model differential cap base unitBound collarBound actual left right budget index)
    (canonical : ∀ index, (family index).1 = readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)) :
    SequentialCompatibleConstantRefinementProgram where
  model index := (family index).2.2.val
  steps := steps cached nonzero pairs degreeBound bounds anchor anchorCanonical left right budget budgetSource
    family canonical
  stepScale := 3 * budget.val
  stepScale_nonneg := Arithmetic.mul_nonneg_direct (by decide) budget.property
  initialAllowance_le := by
    have initial := model_allowance_le left right budget 0 (family 0)
    have zeroPrecision : Basic.quarterRadius 1 0 = (1 : Fraction.Rational) := by
      rewrite [Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    have scalar := congrArg (fun value => budget.val * value) zeroPrecision
    have paid := initial.trans_eq (scalar.trans (Fraction.Field.mul_one_direct _))
    have payment := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (1 : Fraction.Rational) ≤ 4 * 3) budget.property
    exact paid.trans ((show budget.val = 1 * budget.val from (Fraction.Field.one_mul _).symm).trans_le
      (payment.trans_eq (by ring1)))
  comparisonAllowance_le index := by
    have next : Basic.quarterRadius 1 (index + 1) = Basic.quarterRadius 1 index / 4 := by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow, pow_succ]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    have bound := Readings.comparisonAllowance_le budget index left right
      ⟨Basic.quarterRadius 1 (index + 1), Basic.quarterRadius_nonneg (by decide) (index + 1)⟩ next
      (family index).1 (family (index + 1)).1 (Stage.cells (family index)) (Stage.cells (family (index + 1)))
      (steps cached nonzero pairs degreeBound bounds anchor anchorCanonical left right budget budgetSource
        family canonical index)
    exact bound.trans_eq (by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1)

/-- Retain the original coarse bank and produce the same canonical whole-bank family at every requested depth.

The original supplied anchor, edge cache and inner budget remain literal
inputs. The zero case keeps that same transported anchor; every positive
case is the original stage factory at its displayed depth and target.
-/
private def models
    (nonzero : base ≠ 0) (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)
    (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges })
    (budget : { value : Fraction.Rational // 0 ≤ value }) :
    ∀ index, Model differential cap base unitBound collarBound actual left right budget index := by
  have oneToZero : (1 : Fraction.Rational) = Basic.quarterRadius 1 0 := by decide +kernel
  let initialBank := anchor.val.transportTarget oneToZero
  let initialStage : Model differential cap base unitBound collarBound actual left right budget 0 :=
    ⟨initialBank, cachedEdges,
      ⟨initialBank.model (some ⟨budget.val * Basic.quarterRadius 1 0,
        Arithmetic.mul_nonneg_direct budget.property
          (Basic.quarterRadius_nonneg (by decide) 0)⟩) cachedEdges, rfl⟩⟩
  let family : ∀ index, Model differential cap base unitBound collarBound actual left right budget index :=
    fun index => match index with
      | 0 => initialStage
      | depth + 1 => stage differential cap base nonzero unitBound collarBound actual (depth + 1) left right
          (Basic.quarterRadius 1 (depth + 1)) (Basic.quarterRadius_pos (by decide) (depth + 1))
          (some ⟨budget.val * Basic.quarterRadius 1 (depth + 1),
            Arithmetic.mul_nonneg_direct budget.property
              (Basic.quarterRadius_nonneg (by decide) (depth + 1))⟩)
  exact family

/-- The original retained family uses the complete canonical reading bank at each actual indexed request.

The zero case consumes the supplied anchor's whole factory equality and
original target transport. Positive cases use the original stage reading
readback, preserving both original cache parents at every occurrence.
-/
private theorem models_canonical
    (nonzero : base ≠ 0) (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)
    (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges })
    (budget : { value : Fraction.Rational // 0 ≤ value }) (index : Nat) :
    (models nonzero left right cachedEdges anchor budget index).1 =
      readings differential cap base nonzero unitBound collarBound actual
        index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index) := by
  have oneToZero : (1 : Fraction.Rational) = Basic.quarterRadius 1 0 := by decide +kernel
  let initialBank := anchor.val.transportTarget oneToZero
  cases index with
  | zero =>
      change initialBank = _
      have produced := (congrArg (fun stored => stored.transportTarget oneToZero) anchor.property).trans
        (Readings.transportTarget_readings differential cap base nonzero unitBound collarBound actual
          0 left right 1 (Basic.quarterRadius 1 0) (by decide)
          (Basic.quarterRadius_pos (by decide) 0) oneToZero cachedEdges)
      exact produced.trans (Readings.readings_cachedEdges differential cap base nonzero unitBound collarBound actual
        0 left right (Basic.quarterRadius 1 0) (Basic.quarterRadius_pos (by decide) 0) cachedEdges)
  | succ depth =>
      exact stage_readings differential cap base nonzero unitBound collarBound actual (depth + 1) left right
        (Basic.quarterRadius 1 (depth + 1)) (Basic.quarterRadius_pos (by decide) (depth + 1)) _

/-- Retain certified sample and allowance caches over the same actual canonical whole-bank stages. -/
private def certify
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)
    (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges })
    (budget : { value : { value : Fraction.Rational // 0 ≤ value } //
      value.val = Readings.allowanceScale cached bounds anchor.val }) :
    CertifiedProgram.Program (operations (differential := differential) (cap := cap) (base := base)
      (unitBound := unitBound) (collarBound := collarBound) (actual := actual) left right budget.val) := by
  let family := models nonzero left right cachedEdges anchor budget.val
  let initialStage := family 0
  have canonical : ∀ index, (family index).1 = readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index) :=
    models_canonical nonzero left right cachedEdges anchor budget.val
  let initialCache : CertifiedProgram.CachedModel
      (operations (differential := differential) (cap := cap) (base := base)
        (unitBound := unitBound) (collarBound := collarBound) (actual := actual) left right budget.val) :=
    .canonical ⟨0, initialStage⟩
  let caches : Nat → CertifiedProgram.CachedModel
      (operations (differential := differential) (cap := cap) (base := base)
        (unitBound := unitBound) (collarBound := collarBound) (actual := actual) left right budget.val) :=
    fun index => match index with
      | 0 => initialCache
      | depth + 1 => .canonical ⟨depth + 1, family (depth + 1)⟩
  have samples : ∀ index, (caches index).sample = (family index).2.2.val.integralSample := by
    intro index
    cases index <;> rfl
  have allowances : ∀ index, (caches index).allowance = (family index).2.2.val.aggregateAllowance := by
    intro index
    cases index <;> rfl
  have anchorCanonical := anchor.property.trans
    (Readings.readings_cachedEdges differential cap base nonzero unitBound collarBound actual 0 left right 1
      (by decide) cachedEdges)
  let witness := sequential cached nonzero pairs degreeBound bounds anchor.val anchorCanonical
    left right budget.val budget.property family canonical
  let errorScale := 4 * (3 * budget.val.val)
  let centerBound := 2 * (Norm.Basic.normSq initialCache.sample + errorScale)
  have initialSample : initialCache.sample = (family 0).2.2.val.integralSample := samples 0
  exact
    { stage := caches
      errorScale := errorScale
      errorScale_nonneg := Arithmetic.mul_nonneg_direct (by decide)
        (Arithmetic.mul_nonneg_direct (by decide) budget.val.property)
      modelAllowance_le := by
        intro index
        rewrite [allowances index]
        exact witness.modelAllowance_le index
      later_close := by
        intro earlier later order
        rewrite [samples later, samples earlier]
        exact witness.later_close order
      centerBound := centerBound
      centerBound_nonneg := Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (Norm.Basic.normSq_nonneg initialCache.sample)
          (Arithmetic.mul_nonneg_direct (by decide)
            (Arithmetic.mul_nonneg_direct (by decide) budget.val.property)))
      sample_bounded := by
        intro index
        rewrite [samples index]
        change Norm.Basic.normSq (family index).2.2.val.integralSample ≤
          2 * (Norm.Basic.normSq initialCache.sample + errorScale)
        rewrite [initialSample]
        exact witness.sample_bounded index }

/-- Read the complete original canonical bank in the actual certified cache at the same displayed index. -/
private theorem certify_stage_readings
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)
    (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges })
    (budget : { value : { value : Fraction.Rational // 0 ≤ value } //
      value.val = Readings.allowanceScale cached bounds anchor.val }) (index : Nat) :
    HEq (((certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget).stage index).model).2.1
      (readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)) := by
  have bankEq : HEq
      (((certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget).stage index).model).2.1
      (models nonzero left right cachedEdges anchor budget.val index).1 := by
    unfold certify
    cases index <;> rfl
  exact bankEq.trans (heq_of_eq (models_canonical nonzero left right cachedEdges anchor budget.val index))

/-- Read the actual certified sample through its same complete canonical bank and original retained budget. -/
private theorem certify_stage_sample
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)
    (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges })
    (budget : { value : { value : Fraction.Rational // 0 ≤ value } //
      value.val = Readings.allowanceScale cached bounds anchor.val }) (index : Nat) :
    ((certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget).stage index).sample =
      ((readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)).model
        (some ⟨budget.val.val * Basic.quarterRadius 1 index,
        Arithmetic.mul_nonneg_direct budget.val.property
          (Basic.quarterRadius_nonneg (by decide) index)⟩)).integralSample := by
  have sampleEq :
      ((certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget).stage index).sample =
      (models nonzero left right cachedEdges anchor budget.val index).2.2.val.integralSample := by
    unfold certify
    cases index <;> rfl
  have canonical := models_canonical nonzero left right cachedEdges anchor budget.val index
  have sample := congrArg
    (fun bank : Readings differential cap base unitBound collarBound actual
        index left right (Basic.quarterRadius 1 index) => (bank.model
        (some ⟨budget.val.val * Basic.quarterRadius 1 index,
        Arithmetic.mul_nonneg_direct budget.val.property
          (Basic.quarterRadius_nonneg (by decide) index)⟩)).integralSample) canonical
  exact sampleEq.trans ((Stage.sample (models nonzero left right cachedEdges anchor budget.val index)).trans sample)

/-- The original certified program retains its actual coarse bank and the once-computed common budget.

Both retained caches carry their original defining equations. The program
uses the existing indexed stage and original cached-model owners; this
view introduces no alternate path, observation or program datatype.
-/
abbrev Program
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right) :=
  (anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
    value = readings differential cap base nonzero unitBound collarBound actual
      0 left right 1 (by decide) cachedEdges }) ×
  (budget : { value : { value : Fraction.Rational // 0 ≤ value } //
    value.val = Readings.allowanceScale cached bounds anchor.val }) ×
    CertifiedProgram.Program (operations (differential := differential) (cap := cap) (base := base)
      (unitBound := unitBound) (collarBound := collarBound) (actual := actual) left right budget.val)

/-- Construct the actual total-form integration program from its retained numerical and polynomial bounds.

The original dyadic edge cache and whole coarse observation bank are
materialized once. Their budget and initial sample are retained outside
all later-stage lambdas; each produced stage keeps its same whole bank,
path, sample and allowance in the original certified-program cache.
-/
def program
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint)
    (cachedEdges : DyadicEdges 0 left right := ⟨dyadicEdges 0 left right, rfl⟩) :
    Program (differential := differential) (cap := cap) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) cached nonzero bounds left right cachedEdges :=
  let stored := readings differential cap base nonzero unitBound collarBound actual
    0 left right 1 (by decide) cachedEdges
  let anchor : { value : Readings differential cap base unitBound collarBound actual 0 left right 1 //
      value = readings differential cap base nonzero unitBound collarBound actual
        0 left right 1 (by decide) cachedEdges } := ⟨stored, rfl⟩
  let scale := Readings.allowanceScale cached bounds stored
  let budget : { value : { value : Fraction.Rational // 0 ≤ value } //
      value.val = Readings.allowanceScale cached bounds anchor.val } :=
    ⟨⟨scale, Readings.allowanceScale_nonnegative cached nonzero bounds stored⟩, rfl⟩
  ⟨anchor, budget, certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget⟩

section

variable {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
  (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
  {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
  (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
  (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right)

/-- Every actual cached stage retains its original requested dyadic depth as its model index. -/
theorem program_stage_index (index : Nat) :
    (((program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges).2.2.stage index).model).1 = index := by
  unfold program certify
  cases index <;> rfl

/-- Every actual certified stage retains the whole canonical bank at its same original depth and request.

The heterogeneous equality preserves the complete original bank when its
source index is projected through the cached-model owner. The original
coarse target transport and every later canonical stage remain retained.
-/
theorem program_stage_readings (index : Nat) :
    HEq (((program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges).2.2.stage index).model).2.1
      (readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)) := by
  unfold program
  exact certify_stage_readings cached nonzero pairs degreeBound bounds left right cachedEdges _ _ index

/-- The original certified sample is the sample of its same actual canonical bank with its retained budget.

The original stage path and its actual bank supply the existing sample
readback. The canonical-family certificate transports only that scalar
readback; it does not rebuild observations or replace the source program.
-/
theorem program_stage_sample (index : Nat) :
    let retained := program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges
    (retained.2.2.stage index).sample =
      ((readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)).model
        (some ⟨retained.2.1.val.val * Basic.quarterRadius 1 index,
          Arithmetic.mul_nonneg_direct retained.2.1.val.property
            (Basic.quarterRadius_nonneg (by decide) index)⟩)).integralSample := by
  unfold program
  exact certify_stage_sample cached nonzero pairs degreeBound bounds left right cachedEdges _ _ index

/-- The initial actual cached model retains the same whole supplied coarse bank, including all paid requests. -/
theorem program_initial_readings :
    let retained := program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges
    HEq ((retained.2.2.stage 0).model).2.1 retained.1.val := by
  unfold program certify
  dsimp only [CertifiedProgram.CachedModel.canonical]
  exact Readings.transportTarget_heq _ _

end

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end
