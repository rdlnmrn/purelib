module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Jet
public import Purelib.Integration.CertifiedProgram.Comparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Bounds
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order

/-! # Operational finite Laurent expansion of the original total-form programme -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings.Jets

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }} {left right : Endpoint}
  {budget : { value : Fraction.Rational // 0 ≤ value }}

/-- The original factor-preparation operation at actual points of the same retained circle and numerical sheet.

Each result is the original guarded Prepared certificate at the supplied
whole numerical presentation and jet reading. The operation retains no
assumed expansion, integral comparison, vanishing remainder or regularity.
-/
private abbrev Factors (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) :=
  (time : Fraction.Rational) → {target : Fraction.Rational} →
  (reading : Reading differential cap (actual.val.point time)
    (point_inside base unitBound collarBound actual time) target) →
  (coefficientCache : { value : Canonical //
    value = Evaluation.eval jet.val (Primitives.point curve (actual.val.point time)) }) →
    Division.Prepared (origin.certificate.value.add
      (reading.1.1.certificate.value.mul (Coherence.exact coefficientCache.val)))

/-- The actual source-stage cache and its finite expansion bank with both original parents retained.

The exact source programme and stage index remain correctness-bearing
parents. Every expansion entry is indexed by the actual whole source
reading; the supplied original principal and guarded error owners remain
inside their original dependent cache types.
-/
abbrev Model (source : CertifiedProgram.Program (Circle.operations (differential := differential)
    (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) left right budget))
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (polynomial : { value : Dense.Basic.DensePolynomial Canonical //
      value = Dense.Gaussian.Reciprocal.padded differential.numerator (2 * genus) })
    (retained : jet.Principal polynomial.val differential.scale)
    (primitive : Antiderivative.ReciprocalPrimitive retained.val genus) :=
  (index : Nat) ×
  (original : { cache : CertifiedProgram.CachedModel (Circle.operations (differential := differential)
    (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) left right budget) // cache = source.stage index }) ×
    Jets original.val.model.2.1 origin jet remainder polynomial retained primitive
      (Basic.quarterRadius 1 original.val.model.1) (Basic.quarterRadius 1 original.val.model.1)

variable {source : CertifiedProgram.Program (Circle.operations (differential := differential)
    (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound)
      (actual := actual) left right budget)}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {polynomial : { value : Dense.Basic.DensePolynomial Canonical //
    value = Dense.Gaussian.Reciprocal.padded differential.numerator (2 * genus) }}
  {retained : jet.Principal polynomial.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}

/-- The retained whole source cache has the same original dyadic index as its enclosing expansion model. -/
theorem Model.source_index (model : Model source origin jet remainder polynomial retained primitive)
    (indexed : ∀ index, (source.stage index).model.1 = index) :
    model.2.1.val.model.1 = model.1 :=
  (congrArg (fun value => value.model.1) model.2.1.property).trans (indexed model.1)

/-- Sample and allowance operations on the same retained original stage and actual expansion bank. -/
def operations :
    CertifiedProgram.ModelOperations (Model source origin jet remainder polynomial retained primitive) where
  sample model := (model.2.2.model false ⟨0, Fraction.Order.Basic.le_refl _⟩).integralSample
  allowance model := (model.2.2.model false ⟨0, Fraction.Order.Basic.le_refl _⟩).aggregateAllowance

/-- The actual expanded model's original path supplies its sample literally. -/
theorem operations_sample (model : Model source origin jet remainder polynomial retained primitive) :
    operations.sample model = (model.2.2.model false ⟨0, Fraction.Order.Basic.le_refl _⟩).integralSample := by
  unfold operations
  rfl

/-- The actual expanded model's same retained path supplies its allowance literally. -/
theorem operations_allowance (model : Model source origin jet remainder polynomial retained primitive) :
    operations.allowance model = (model.2.2.model false ⟨0, Fraction.Order.Basic.le_refl _⟩).aggregateAllowance := by
  unfold operations
  rfl

/-- Build one expansion stage from the complete actual source cache and the same supplied setup handler. -/
private def stage (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (factors : Factors (differential := differential) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) origin jet) (index : Nat) :
    CertifiedProgram.CachedModel (operations (source := source) (origin := origin) (jet := jet)
      (remainder := remainder) (polynomial := polynomial) (retained := retained) (primitive := primitive)) :=
  let original := source.stage index
  let stored := original.model.2.1
  let target := Basic.quarterRadius 1 original.model.1
  have positive := Basic.quarterRadius_pos (by decide : (0 : Fraction.Rational) < 1) original.model.1
  let expanded := stored.jets nonzero pairs bound origin jet remainder polynomial retained primitive
    (fun occurrence reading => factors
      ((dyadicEdges original.model.1 left right)[occurrence.val]'occurrence.isLt).left.parameter reading)
    target positive target positive
  .canonical ⟨index, ⟨original, rfl⟩, expanded⟩

/-- Every actual stage allowance is zero-bounded by its retained same-curve exact cell allowances. -/
private theorem stage_allowance (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (factors : Factors (differential := differential) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) origin jet) (index : Nat) :
    (stage (source := source) (remainder := remainder) (polynomial := polynomial)
      (retained := retained) (primitive := primitive) nonzero pairs bound factors index).allowance ≤ 0 := by
  let cached := stage (source := source) (remainder := remainder) (polynomial := polynomial)
    (retained := retained) (primitive := primitive) nonzero pairs bound factors index
  exact (cached.allowance_eq.trans (operations_allowance cached.model)).trans_le
    (cached.model.2.2.model_allowance_le false ⟨0, Fraction.Order.Basic.le_refl _⟩)

/-- The actual expanded stage meets the geometric distance to its same original source sample.

The index law concerns the actual source cache producer. The finite
coefficient comparison and actual circle geometry derive the bridge;
no integral equality or successful output comparison is an input.
-/
private theorem stage_distance (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (factors : Factors (differential := differential) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) origin jet)
    (indexed : ∀ index, (source.stage index).model.1 = index) (index : Nat) :
    Norm.Basic.normSq ((stage (source := source) (remainder := remainder) (polynomial := polynomial)
      (retained := retained) (primitive := primitive) nonzero pairs bound factors index).sample -
        (source.stage index).sample) ≤ Basic.quarterRadius (144 * Norm.Basic.normSq base) index := by
  let cached := stage (source := source) (remainder := remainder) (polynomial := polynomial)
    (retained := retained) (primitive := primitive) nonzero pairs bound factors index
  let original := cached.model.2.1
  let expanded := cached.model.2.2
  let sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value } :=
    some ⟨budget.val * Basic.quarterRadius 1 original.val.model.1,
      Fraction.Order.Arithmetic.mul_nonneg_direct budget.property
        (Basic.quarterRadius_nonneg (by decide) original.val.model.1)⟩
  have pathSample := Stage.sample original.val.model.2
  have actualSample := original.val.sample_eq.trans
    ((Circle.operations_sample left right budget original.val.model).trans pathSample)
  have sourceSample : (source.stage cached.model.1).sample =
      (original.val.model.2.1.model sourceAllowance).integralSample :=
    (congrArg (fun value => value.sample) original.property).symm.trans actualSample
  have outputSample := cached.sample_eq.trans (operations_sample cached.model)
  have paid := expanded.model_distance_geometric rfl rfl rfl sourceAllowance
    ⟨0, Fraction.Order.Basic.le_refl _⟩
  have indexEq : original.val.model.1 = cached.model.1 := Model.source_index cached.model indexed
  have stageIndex : cached.model.1 = index := by unfold cached stage; rfl
  have radiusEq := congrArg (Basic.quarterRadius (144 * Norm.Basic.normSq base)) (indexEq.trans stageIndex)
  have scalar := congrArg₂ (fun first last : Canonical => first - last) outputSample sourceSample
  have result := (congrArg Norm.Basic.normSq scalar).trans_le
    ((Norm.Bounds.normSq_sub_symm _ _).trans_le paid)
  exact result.trans_eq radiusEq

/-- Certify the actual finite Laurent expansion programme and compare its output with the original total-form programme.

Each stage retains the original complete source cache, its actual expansion
bank and one original certified sample/allowance cache. The proved finite
observation estimates derive geometric Cauchy and output comparisons.
The actual error channels remain in the programme; this does not assert
that their integrals vanish or identify a physical residue.
-/
private def program (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (factors : Factors (differential := differential) (base := base) (unitBound := unitBound)
      (collarBound := collarBound) (actual := actual) origin jet)
    (indexed : ∀ index, (source.stage index).model.1 = index) :
    (expanded : CertifiedProgram.Program (operations (source := source) (origin := origin) (jet := jet)
      (remainder := remainder) (polynomial := polynomial) (retained := retained) (primitive := primitive))) ×
        NamedEquivalent source.output.name expanded.output.name := by
  let produced := stage (source := source) (remainder := remainder) (polynomial := polynomial)
    (retained := retained) (primitive := primitive) nonzero pairs bound factors
  let bridge := 144 * Norm.Basic.normSq base
  have nonnegative : 0 ≤ bridge := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 144) (by decide)).le (Norm.Basic.normSq_nonneg base)
  have distance := stage_distance (source := source) (remainder := remainder) (polynomial := polynomial)
    (retained := retained) (primitive := primitive) nonzero pairs bound factors indexed
  have allowances : CertifiedProgram.Allowances produced (source.perturbationScale bridge) := by
    intro index
    exact (stage_allowance (source := source) (remainder := remainder) (polynomial := polynomial)
      (retained := retained) (primitive := primitive) nonzero pairs bound factors index).trans
        (Basic.quarterRadius_nonneg (source.perturbationScale_nonnegative bridge nonnegative) index)
  let changed := source.perturb produced bridge nonnegative distance allowances
  have close (index : Nat) : Norm.Basic.normSq ((source.stage index).sample - (changed.stage index).sample) ≤
      Basic.quarterRadius bridge index := by
    have cacheEq := CertifiedProgram.Program.perturb_stage source produced bridge nonnegative distance allowances index
    have actual := congrArg (fun value => value.sample) cacheEq
    exact (congrArg (fun value => Norm.Basic.normSq ((source.stage index).sample - value)) actual).trans_le
      ((Norm.Bounds.normSq_sub_symm _ _).trans_le (distance index))
  exact ⟨changed, source.output_equivalent_of_samples_close changed bridge nonnegative close⟩

/-- Compute the original bounded factor setup once for all actual observations on the retained circle.

The same original root bounds, finite jet Horner cache and origin guard
remain outside the observation handler. A displayed base-quadrance bound
places every actual chart coordinate in that computed square. The Point
is the unchanged nominal parent, while the actual supplied whole numerical
preparation feeds the point handler without constructing its winding attachment.
-/
private def prepareFactors
    (root : Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model)
    (bounds : Riemann.Normalization.InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (jetBounds : jet.Bounds collar.box)
    (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor :=
        ⟨RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor, rfl⟩) :
    (radius : { value : Fraction.Rational // 0 < value }) ×
      (Norm.Basic.normSq base ≤ radius.val ^ 2 →
        Factors (differential := differential) (base := base) (unitBound := unitBound)
          (collarBound := collarBound) (actual := actual) origin jet) := by
  let prepared := setup.val
  refine ⟨prepared.1, ?_⟩
  intro radiusBound time target reading coefficientCache
  let point := Primitives.point curve (actual.val.point time)
  have quadrance : Norm.Basic.normSq (actual.val.point time) = Norm.Basic.normSq base := by
    rewrite [actual.property]
    exact point_normSq base time
  have inside := Primitives.point_in_square curve (actual.val.point time)
    (quadrance.trans_le unitBound) prepared.1.val prepared.1.property.le (quadrance.trans_le radiusBound)
  exact prepared.2 point (point_inside base unitBound collarBound actual time) reading.1.1 coefficientCache inside

/-- The original local square and actual source-indexed finite-expansion programme with its output comparison.

The source, original origin, finite jet/residual, retained principal table
and primitive remain the original correctness-bearing parents. The result
is the unchanged dependent pair returned by prepare, including the actual
base-quadrance condition and output-comparison procedure.
-/
@[expose] def Preparation :=
    (radius : { value : Fraction.Rational // 0 < value }) ×
      (Norm.Basic.normSq base ≤ radius.val ^ 2 →
        (expanded : CertifiedProgram.Program (operations (source := source) (origin := origin) (jet := jet)
          (remainder := remainder) (polynomial := polynomial) (retained := retained) (primitive := primitive))) ×
            NamedEquivalent source.output.name expanded.output.name)

/-- Prepare an actual finite-expansion programme and its comparison with the supplied original total-form programme.

The supplied original factor setup retains its computed positive local
square and actual point handler. On a circle whose displayed base quadrance
pays that square, the same setup produces every guarded factor and the
actual programme comparison. The default is the original setup producer.
The original source stage-index law, principal product, primitive, finite
jet, residual and optional original setup caches are retained inputs.
-/
def prepare (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (indexed : ∀ index, (source.stage index).model.1 = index)
    (root : Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model :=
      Riemann.Normalization.InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model)
    (bounds : Riemann.Normalization.InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial :=
      Riemann.Normalization.InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial)
    (jetBounds : jet.Bounds collar.box := jet.bounds collar.box)
    (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet) :=
      RootCoordinates.originJetFactor_prepared origin jet)
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor :=
        ⟨RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor, rfl⟩) :
    Preparation (source := source) (origin := origin) (jet := jet) (remainder := remainder)
      (polynomial := polynomial) (retained := retained) (primitive := primitive) :=
  let prepared := prepareFactors (differential := differential) (base := base) (unitBound := unitBound)
    (collarBound := collarBound) (actual := actual) (origin := origin) root bounds jetBounds anchor setup
  ⟨prepared.1, fun radiusBound => program nonzero pairs bound (prepared.2 radiusBound) indexed⟩

/-- The original expansion preparation retains the complete positive radius from its supplied whole factor setup. -/
theorem prepare_radius (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (indexed : ∀ index, (source.stage index).model.1 = index)
    (root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor) :
    (prepare (source := source) (origin := origin) (jet := jet) (remainder := remainder)
      (polynomial := polynomial) (retained := retained) (primitive := primitive)
      nonzero pairs bound indexed root bounds jetBounds anchor setup).1 = setup.val.1 := by
  unfold prepare prepareFactors
  rfl

/-- Every prepared expansion stage retains its original requested index in the same supplied source model. -/
theorem prepare_stage_index (nonzero : base ≠ 0) (pairs : differential.denominatorPairs = 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (indexed : ∀ index, (source.stage index).model.1 = index)
    (root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (near : Norm.Basic.normSq base ≤
      (prepare (source := source) (origin := origin) (jet := jet) (remainder := remainder)
        (polynomial := polynomial) (retained := retained) (primitive := primitive)
        nonzero pairs bound indexed root bounds jetBounds anchor setup).1.val ^ 2)
    (index : Nat) :
    (((prepare (source := source) (origin := origin) (jet := jet) (remainder := remainder)
      (polynomial := polynomial) (retained := retained) (primitive := primitive)
      nonzero pairs bound indexed root bounds jetBounds anchor setup).2 near).1.stage index).model.1 = index := by
  unfold prepare program
  rewrite [CertifiedProgram.Program.perturb_stage]
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings.Jets

end
