module

-- Verification-only former bodies reduce the original private certifier and its scalar proof providers.
import all Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.Tactic.Ring

/-! # Complete original cap programme defaults after factoring its retained family -/

namespace TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.ProgramDefaults

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

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

/-- Verification-only complete historical certifier, with its original body retained literally. -/
private def formerCertify
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
  have oneToZero : (1 : Fraction.Rational) = Basic.quarterRadius 1 0 := by decide +kernel
  let initialBank := anchor.val.transportTarget oneToZero
  let initialStage : Model differential cap base unitBound collarBound actual left right budget.val 0 :=
    ⟨initialBank, cachedEdges,
      ⟨initialBank.model (some ⟨budget.val.val * Basic.quarterRadius 1 0,
        Arithmetic.mul_nonneg_direct budget.val.property
          (Basic.quarterRadius_nonneg (by decide) 0)⟩) cachedEdges, rfl⟩⟩
  let family : ∀ index, Model differential cap base unitBound collarBound actual left right budget.val index :=
    fun index => match index with
      | 0 => initialStage
      | depth + 1 => stage differential cap base nonzero unitBound collarBound actual (depth + 1) left right
          (Basic.quarterRadius 1 (depth + 1)) (Basic.quarterRadius_pos (by decide) (depth + 1))
          (some ⟨budget.val.val * Basic.quarterRadius 1 (depth + 1),
            Arithmetic.mul_nonneg_direct budget.val.property
              (Basic.quarterRadius_nonneg (by decide) (depth + 1))⟩)
  have canonical : ∀ index, (family index).1 = readings differential cap base nonzero unitBound collarBound actual
      index left right (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index) := by
    intro index
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

/-- The complete current certifier equals the complete historical record at every original input. -/
private theorem certify_whole_default
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
    certify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget =
      formerCertify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget := (rfl)

/-- Verification-only complete historical programme, consuming that same historical certifier. -/
private def formerProgram
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
  ⟨anchor, budget, formerCertify cached nonzero pairs degreeBound bounds left right cachedEdges anchor budget⟩

/-- The complete current programme equals its historical record, including anchor, budget and all executable caches. -/
private theorem program_whole_default
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint)
    (cachedEdges : DyadicEdges 0 left right := ⟨dyadicEdges 0 left right, rfl⟩) :
    program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges =
    formerProgram (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
      cached nonzero pairs degreeBound bounds left right cachedEdges := (rfl)

end TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.ProgramDefaults
