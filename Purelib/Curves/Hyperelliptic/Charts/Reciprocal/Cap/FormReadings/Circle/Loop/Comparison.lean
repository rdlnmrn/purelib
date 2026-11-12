module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Principal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Jet
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Jet
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Bounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent.Program
import Purelib.Integration.CertifiedProgram.Comparison
import Purelib.Integration.CertifiedProgram.Observation
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Rat.SmallWidth
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring

/-! # Actual four-quarter total-form and retained principal programme comparisons -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List (DependentProduct)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational.Geometric
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical} {nonzero : base ≠ 0}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {data : Polynomials differential} {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {retained : jet.Principal data.1.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}

variable (circuit : Integral.Circuit base nonzero) (cached : data.Bounds base)
  (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
  (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
  (edges : DyadicEdges 0 start finish)
  (stored : Built (unitBound := unitBound) (collarBound := collarBound)
    circuit.1 cached pairs degreeBound bounds edges)
  (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
  (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
  (prepared : { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored.val //
    value = expand circuit.1 cached pairs degreeBound bounds edges stored jetBounds anchor setup })
  (near : Norm.Basic.normSq base ≤ setup.val.1.val ^ 2)
  (expanded : { value : Expanded (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored.val //
    value = realize circuit.1 cached pairs degreeBound bounds edges stored jetBounds anchor setup prepared near })

/-- The actual realized expansion and its complete retained original source cache have the same requested mesh index. -/
theorem realized_indices (index : Fin Integral.quarters.length) (depth : Nat) :
    (((expanded.val.get index).1.stage depth).model.1 = depth) ∧
      (((expanded.val.get index).1.stage depth).model.2.1.val.model.1 = depth) := by
  have outer := (congrArg (fun bank : Expanded (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored.val =>
    ((bank.get index).1.stage depth).model.1) expanded.property).trans
      (realize_stage_index circuit.1 cached pairs degreeBound bounds edges stored jetBounds anchor setup
        prepared near index depth)
  exact ⟨outer, (Readings.Jets.Model.source_index ((expanded.val.get index).1.stage depth).model
    (stored.stage_index index)).trans outer⟩

/-- The combined quarter estimate separates its scalar tail and original geometric observation term. -/
private theorem quarter_bound_eq (quadrance tail : Fraction.Rational) (depth : Nat) :
    2 * (2 * ((4 * quadrance) * (16 * (Basic.quarterRadius 1 depth + Basic.quarterRadius 1 depth) +
      4 * Basic.quarterRadius 1 depth) + (4 * quadrance) * tail) +
      (4 * quadrance) * (32 * (Basic.quarterRadius 1 depth + Basic.quarterRadius 1 depth) +
        4 * Basic.quarterRadius 1 depth)) =
    16 * quadrance * tail + Basic.quarterRadius (1120 * quadrance) depth := by
  rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Balanced addition of the four same-mesh quarter estimates retains their common weighted tail offset. -/
private theorem loop_bound_eq (quadrance tail : Fraction.Rational) (depth : Nat) :
    let bound := 16 * quadrance * tail + Basic.quarterRadius (1120 * quadrance) depth
    2 * (2 * (bound + bound) + 2 * (bound + bound)) =
      256 * quadrance * tail + Basic.quarterRadius (17920 * quadrance) depth := by
  dsimp only
  rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
  ring1

/-- The three paid output legs keep the radius-weighted tail explicit in their final squared tolerance. -/
private theorem comparison_bound_lt (quadrance tail precision target : Fraction.Rational)
    (paid : 10 * precision < target) :
    2 * (precision + 2 * (32 * (256 * quadrance * tail) + precision + precision)) <
      32768 * quadrance * tail + target := by
  have grouped : 2 * (precision + 2 * (32 * (256 * quadrance * tail) + precision + precision)) =
      32768 * quadrance * tail + 10 * precision := by ring1
  exact grouped.trans_lt (Arithmetic.add_lt_add_left_direct paid _)

/-- Two paid output comparisons retain the same explicit radius-weighted coefficient tail. -/
private theorem logarithmic_bound_lt (quadrance tail precision target : Fraction.Rational)
    (paid : 4 * precision < target) :
    2 * (32768 * quadrance * tail + precision + precision) < 65536 * quadrance * tail + target := by
  have grouped : 2 * (32768 * quadrance * tail + precision + precision) =
      65536 * quadrance * tail + 4 * precision := by ring1
  exact grouped.trans_lt (Arithmetic.add_lt_add_left_direct paid _)

/-- The original velocity budget pays the full output tail after its exact finite comparison scale. -/
private theorem weighted_tail_lt (quadrance tail precision : Fraction.Rational) (nonnegative : 0 ≤ quadrance)
    (paid : (4 * quadrance) * (1 + tail) < precision / 16384) :
    65536 * quadrance * tail < precision := by
  have positive : (0 : Fraction.Rational) < 16384 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 16384) (by decide)
  have final := (Fraction.Order.Field.lt_div_iff_pos positive).mp paid
  have plusOne := Arithmetic.add_le_add_direct (by decide : (0 : Fraction.Rational) ≤ 1)
    (Fraction.Order.Basic.le_refl tail)
  rewrite [Fraction.Field.zero_add] at plusOne
  have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct plusOne
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) nonnegative)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct bounded positive.le
  have grouped : ((4 * quadrance) * tail) * 16384 = 65536 * quadrance * tail := by ring1
  exact (grouped.symm.trans_le scaled).trans_lt final

include expanded

/-- One actual total-form quarter sample has a velocity-weighted tail offset and a paid geometric principal error.

The original whole source cache and expansion retain the same derived
mesh index. Exact quarter transport uses the supplied whole reciprocal
Request and its same original reading. The finite form/principal and
principal/parameter estimates are composed before the numerical tail
ceiling is weakened to one. The radius factor remains in the offset.
-/
theorem quarter_distance_le (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (nearError : Norm.Basic.normSq base ≤ errorBounds.1.1.val ^ 2)
    (parameterCached : ParameterPrimitives retained circuit) (index : Fin Integral.quarters.length) (depth : Nat)
    (reciprocal : Equivalence.Observation.Request
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (Readings.Jets.principalTarget cached jetBounds (Basic.quarterRadius 1 depth))) :
    Norm.Basic.normSq (((stored.val.get index).2.2.stage depth).sample -
      reciprocal.reading.value * (Integral.Dyadic.model
        (Integral.quarterBase base (Integral.quarters[index.val]'index.isLt)) (circuit.1.get index).1
        (ParameterPrimitives.Program.coefficient parameterCached) depth start finish).integralSample) ≤
      16 * Norm.Basic.normSq base * errorBounds.readingUpper 1 +
        Basic.quarterRadius (1120 * Norm.Basic.normSq base) depth := by
  let quarter := Integral.quarters[index.val]'index.isLt
  let source := (stored.val.get index).2.2
  let actual := (expanded.val.get index).1.stage depth
  let original := actual.model.2.1
  let precision := Basic.quarterRadius 1 original.val.model.1
  let allowance : { value : Fraction.Rational // 0 ≤ value } := ⟨0, Fraction.Order.Basic.le_refl _⟩
  let sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value } :=
    some ⟨(stored.val.get index).2.1.val.val * precision,
      Arithmetic.mul_nonneg_direct (stored.val.get index).2.1.val.property
        (Basic.quarterRadius_nonneg (by decide) original.val.model.1)⟩
  have indices := realized_indices circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded index depth
  have whole : original.val = source.stage depth := original.property.trans (congrArg source.stage indices.1)
  have pathSample := original.val.sample_eq.trans
    ((Circle.operations_sample start finish (stored.val.get index).2.1.val original.val.model).trans
      (Stage.sample original.val.model.2))
  have sourceSample : (source.stage depth).sample =
      (original.val.model.2.1.model sourceAllowance).integralSample :=
    (congrArg (fun value => value.sample) whole).symm.trans pathSample
  have sameTarget := ((Readings.Jets.principalTarget_onQuarter cached jetBounds quarter precision).trans
    (congrArg (fun value => Readings.Jets.principalTarget cached jetBounds (Basic.quarterRadius 1 value))
      indices.2)).symm
  let request := reciprocal.transportTarget sameTarget
  have precisionPositive : 0 < precision := Basic.quarterRadius_pos (by decide) original.val.model.1
  have close := Readings.Jets.ErrorBounds.model_parameter_distance_le (cached.onQuarter quarter) jetBounds
    (Integral.quarterBase_ne_zero base nonzero quarter) degreeBound errorBounds actual.model.2.2 parameterCached
    precisionPositive precisionPositive precisionPositive
    ((Integral.quarterBase_normSq base quarter).trans_le nearError)
    precisionPositive precisionPositive request sourceAllowance allowance
  have requestValue := congrArg (fun value => value.value) (reciprocal.transportTarget_reading sameTarget)
  have pathValue := congrArg (fun value =>
    (Integral.Dyadic.model (Integral.quarterBase base quarter) (circuit.1.get index).1
      (ParameterPrimitives.Program.coefficient parameterCached) value start finish).integralSample) indices.2
  have productValue := congrArg₂ (fun first last : Canonical => first * last) requestValue pathValue
  have quantity := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    sourceSample productValue.symm
  have upper := errorBounds.readingUpper_mono (Basic.quarterRadius_le_scale
    (by decide : (0 : Fraction.Rational) ≤ 1) original.val.model.1)
  have factorNonnegative : 0 ≤ 4 * Norm.Basic.normSq (Integral.quarterBase base quarter) :=
    Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg _)
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct upper factorNonnegative
  have first := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl ((4 * Norm.Basic.normSq (Integral.quarterBase base quarter)) *
        (16 * (precision + precision) + 4 * precision))) paid)
    (by decide : (0 : Fraction.Rational) ≤ 2)
  have last := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct first
      (Fraction.Order.Basic.le_refl ((4 * Norm.Basic.normSq (Integral.quarterBase base quarter)) *
        (32 * (precision + precision) + 4 * precision))))
    (by decide : (0 : Fraction.Rational) ≤ 2)
  have grouped := quarter_bound_eq (Norm.Basic.normSq (Integral.quarterBase base quarter))
    (errorBounds.readingUpper 1) original.val.model.1
  have unchanged := congrArg₂ (fun value current => 16 * value * errorBounds.readingUpper 1 +
    Basic.quarterRadius (1120 * value) current) (Integral.quarterBase_normSq base quarter) indices.2
  exact (quantity.trans_le close).trans (last.trans_eq (grouped.trans unchanged))

/-- The actual closed total-form programme obeys the same four-quarter weighted principal estimate.

All four original quarter caches are compared at the same derived mesh
and use the same supplied reciprocal reading. The original concatenation
readback and finite dyadic circuit readback preserve the balanced source
order. The numerical tail stays multiplied by the actual base quadrance.
-/
theorem loop_distance_le
    (supplied : { value : stored.val.Result // value = stored.val.concatenate })
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (nearError : Norm.Basic.normSq base ≤ errorBounds.1.1.val ^ 2)
    (parameterCached : ParameterPrimitives retained circuit) (depth : Nat)
    (reciprocal : Equivalence.Observation.Request
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
      (Readings.Jets.principalTarget cached jetBounds (Basic.quarterRadius 1 depth))) :
    Norm.Basic.normSq ((supplied.val.1.stage depth).sample - reciprocal.reading.value *
      (circuit.1.dyadicModel (ParameterPrimitives.Program.coefficient parameterCached) depth).integralSample) ≤
      256 * Norm.Basic.normSq base * errorBounds.readingUpper 1 +
        Basic.quarterRadius (17920 * Norm.Basic.normSq base) depth := by
  let sample (index : Fin Integral.quarters.length) := ((stored.val.get index).2.2.stage depth).sample
  let reference (index : Fin Integral.quarters.length) := reciprocal.reading.value *
    (Integral.Dyadic.model (Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
      (circuit.1.get index).1 (ParameterPrimitives.Program.coefficient parameterCached)
      depth start finish).integralSample
  let bound := 16 * Norm.Basic.normSq base * errorBounds.readingUpper 1 +
    Basic.quarterRadius (1120 * Norm.Basic.normSq base) depth
  have quarters (index : Fin Integral.quarters.length) : Norm.Basic.normSq (sample index - reference index) ≤ bound :=
    quarter_distance_le circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup prepared near
      expanded errorBounds nearError parameterCached index depth reciprocal
  have first := quarters ⟨0, by decide +kernel⟩
  have second := quarters ⟨1, by decide +kernel⟩
  have third := quarters ⟨2, by decide +kernel⟩
  have fourth := quarters ⟨3, by decide +kernel⟩
  have earlier := (Norm.Bounds.normSq_add_sub_add_le
    (sample ⟨0, by decide +kernel⟩) (sample ⟨1, by decide +kernel⟩)
    (reference ⟨0, by decide +kernel⟩) (reference ⟨1, by decide +kernel⟩)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct first second) (by decide))
  have later := (Norm.Bounds.normSq_add_sub_add_le
    (sample ⟨2, by decide +kernel⟩) (sample ⟨3, by decide +kernel⟩)
    (reference ⟨2, by decide +kernel⟩) (reference ⟨3, by decide +kernel⟩)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct third fourth) (by decide))
  have close := (Norm.Bounds.normSq_add_sub_add_le
    (sample ⟨0, by decide +kernel⟩ + sample ⟨1, by decide +kernel⟩)
    (sample ⟨2, by decide +kernel⟩ + sample ⟨3, by decide +kernel⟩)
    (reference ⟨0, by decide +kernel⟩ + reference ⟨1, by decide +kernel⟩)
    (reference ⟨2, by decide +kernel⟩ + reference ⟨3, by decide +kernel⟩)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct earlier later) (by decide))
  have sourceSample := (congrArg (fun value : stored.val.Result => (value.1.stage depth).sample)
    supplied.property).trans (stored.val.concatenate_sample depth)
  have targetSample : reciprocal.reading.value *
      (circuit.1.dyadicModel (ParameterPrimitives.Program.coefficient parameterCached) depth).integralSample =
      (reference ⟨0, by decide +kernel⟩ + reference ⟨1, by decide +kernel⟩) +
        (reference ⟨2, by decide +kernel⟩ + reference ⟨3, by decide +kernel⟩) := by
    rewrite [Integral.Entries.dyadicModel_sample]
    unfold reference
    rewrite [start_eq, finish_eq]
    ring1
  have quantity := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    sourceSample targetSample
  have grouped := loop_bound_eq (Norm.Basic.normSq base) (errorBounds.readingUpper 1) depth
  exact (quantity.trans_le close).trans_eq grouped

section Output

variable
  (supplied : { value : stored.val.Result // value = stored.val.concatenate })
  (logarithmic : { value :
    (program : CertifiedProgram.Program (Integral.Logarithmic.operations circuit)) ×
      Equivalence.NamedEquivalent circuit.channel.name program.output.name //
    value = Integral.Logarithmic.program circuit })
  (parameterCached : ParameterPrimitives retained circuit)
  (polar : { value : (program : RefinementProgram) ×
    Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.polarEdges.val.concatenate parameterCached.polar_count,
      parameterCached.polarEdges.val.concatenate_zero parameterCached.polar_count⟩ })
  (regular : { value : (program : RefinementProgram) ×
    Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.regularEdges.val.concatenate parameterCached.regular_count,
      parameterCached.regularEdges.val.concatenate_zero parameterCached.regular_count⟩ })
  (principalSource : ParameterPrimitives.Program.View logarithmic parameterCached polar regular)
  (weighted : { value : _ // value = Principal.build logarithmic parameterCached polar regular principalSource
    (origin := origin) cached jetBounds })
  (selected : { value : stored.val.Result // value = selectLogarithmic stored.val logarithmic supplied })

/-- The saved adaptive schedule and actual weighted principal stage satisfy the four-quarter estimate at each index.

The supplied weighted stage retains its original scalar source and actual
reciprocal Request. Their whole producer identities derive the retained
logarithmic depth, exact sample and target. Both programmes therefore use
the same original dyadic depth, whose proved floor pays the requested
geometric allowance without identifying independently chosen meshes.
-/
theorem selected_weighted_distance_le (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (nearError : Norm.Basic.normSq base ≤ errorBounds.1.1.val ^ 2) (index : Nat) :
    Norm.Basic.normSq ((selected.val.1.stage index).sample - (weighted.val.1.stage index).sample) ≤
      256 * Norm.Basic.normSq base * errorBounds.readingUpper 1 +
        Basic.quarterRadius (17920 * Norm.Basic.normSq base) index := by
  let actual := weighted.val.1.stage index
  let original := actual.model.2.1
  have outer : actual.model.1 = index :=
    (congrArg (fun value => (value.1.stage index).model.1) weighted.property).trans
      (congrArg (fun value => value.model.1)
        (Principal.build_stage logarithmic parameterCached polar regular principalSource
          (origin := origin) cached jetBounds index))
  have logCache := Principal.source_logarithmic logarithmic parameterCached polar regular principalSource
    actual.model.1 original
  have actualDepth := (congrArg (fun value : CertifiedProgram.CachedModel (Integral.Logarithmic.operations circuit) =>
    value.model.1) logCache).trans
      ((congrArg (fun value => (logarithmic.val.1.stage value).model.1) outer).trans
        (ParameterPrimitives.Program.depth_stage logarithmic index))
  have target := (Principal.targets_value logarithmic parameterCached polar regular principalSource
    cached jetBounds actual.model.1 original).trans
      (congrArg (fun value => Readings.Jets.principalTarget cached jetBounds (Basic.quarterRadius 1 value)) actualDepth)
  let reciprocal := actual.model.2.2.transportTarget target
  have requestValue := congrArg (fun value => value.value) (actual.model.2.2.transportTarget_reading target)
  have scalarSample := (Principal.source_sample logarithmic parameterCached polar regular principalSource
    actual.model.1 original).trans
      (congrArg (fun value => (circuit.1.dyadicModel
        (ParameterPrimitives.Program.coefficient parameterCached) value).integralSample) actualDepth)
  have actualSample := actual.sample_eq.trans
    (CertifiedProgram.Observation.operations_sample _ _ _ actual.model)
  have weightedSample := actualSample.trans
    (congrArg₂ (fun first last : Canonical => first * last) requestValue.symm scalarSample)
  have selectedSample := (congrArg (fun value : stored.val.Result => (value.1.stage index).sample)
    selected.property).trans
      (congrArg (fun value => value.sample) (selectLogarithmic_stage stored.val logarithmic supplied index))
  have close := loop_distance_le circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded supplied errorBounds nearError parameterCached
    (ParameterPrimitives.Program.depth logarithmic index) reciprocal
  have quantity := congrArg₂ (fun first last : Canonical => Norm.Basic.normSq (first - last))
    selectedSample weightedSample
  have scaleNonnegative : 0 ≤ 17920 * Norm.Basic.normSq base :=
    Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 17920) (by decide)).le (Norm.Basic.normSq_nonneg base)
  exact (quantity.trans_le close).trans (Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl _) (Basic.quarterRadius_antitone scaleNonnegative
      (ParameterPrimitives.Program.depth_ge logarithmic index)))

/-- Pay an actual bounded output comparison from the supplied whole total-form loop to its weighted principal programme.

The actual saved schedule comparison, bounded same-stage estimate and
weighted programme's geometric output comparison pay both requested
starts. The tail offset remains in the returned squared tolerance; this
does not assert equivalence at a fixed nonzero circle radius.
-/
def comparePrincipal (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (nearError : Norm.Basic.normSq base ≤ errorBounds.1.1.val ^ 2)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison (Name.Sampling.approximation supplied.val.1.output.name)
      (Name.Sampling.approximation weighted.val.1.output.name) leftStart rightStart
      (32768 * Norm.Basic.normSq base * errorBounds.readingUpper 1 + target) := by
  let precision := SmallWidth.shrinkingWidth 10 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 10) positive
  let original := (supplied.val.2.symm.trans selected.val.2).compare leftStart 0 precision precisionPositive
  have scaleNonnegative : 0 ≤ 17920 * Norm.Basic.normSq base :=
    Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 17920) (by decide)).le (Norm.Basic.normSq_nonneg base)
  let changed := selected.val.1.compareGeometric weighted.val.1.geometric
    (256 * Norm.Basic.normSq base * errorBounds.readingUpper 1) (17920 * Norm.Basic.normSq base)
    scaleNonnegative
    (selected_weighted_distance_le circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
      prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
      errorBounds nearError) 0 0 precision precisionPositive
  let final := weighted.val.1.output_equivalent_geometric.symm.compare 0 rightStart precision precisionPositive
  let compared := original.trans (changed.trans final)
  exact compared.weaken _ (comparison_bound_lt (Norm.Basic.normSq base) (errorBounds.readingUpper 1)
    precision target paid).le

/-- Pay the actual total-form output against the same retained guarded logarithmic candidate.

The supplied weighted programme carries the original comparison with the
origin reciprocal, finite pivot and actual logarithmic circuit channel.
Composing that saved procedure with the same-mesh whole-loop comparison
retains the coefficient-tail offset and both requested starting indices.
-/
def compareLogarithmic (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (nearError : Norm.Basic.normSq base ≤ errorBounds.1.1.val ^ 2)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison (Name.Sampling.approximation supplied.val.1.output.name)
      (Name.Sampling.approximation ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
        ((Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
          (parameterOrder curve))).mul circuit.channel)).name) leftStart rightStart
      (65536 * Norm.Basic.normSq base * errorBounds.readingUpper 1 + target) := by
  let precision := SmallWidth.shrinkingWidth 4 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 4) positive
  let original := comparePrincipal circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
    errorBounds nearError leftStart 0 precision precisionPositive
  let final := weighted.val.2.symm.compare 0 rightStart precision precisionPositive
  exact (original.trans final).weaken _ (logarithmic_bound_lt (Norm.Basic.normSq base)
    (errorBounds.readingUpper 1) precision target paid).le

/-- A computed squared-radius payment makes the actual total-form output close to its retained logarithmic candidate.

The original error-bound request supplies the root square and a strict
velocity-weighted tail payment. The saved actual programmes, reciprocal
Request stream and independently paid logarithmic schedule then yield
this comparison at the requested starts. The result concerns the actual
loop output and does not assert equality at a fixed nonzero radius.
-/
def compareShrinking (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (small : Norm.Basic.normSq base ≤
      errorBounds.baseBudget (SmallWidth.shrinkingWidth 2 target / 16384)) :
    Equivalence.Comparison (Name.Sampling.approximation supplied.val.1.output.name)
      (Name.Sampling.approximation ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
        ((Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
          (parameterOrder curve))).mul circuit.channel)).name) leftStart rightStart target := by
  let precision := SmallWidth.shrinkingWidth 2 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have denominatorPositive : (0 : Fraction.Rational) < 16384 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 16384) (by decide)
  have budgetPositive := Fraction.Order.Field.div_pos_direct precisionPositive denominatorPositive
  have budget := errorBounds.baseBudget_paid budgetPositive small
  have tail := weighted_tail_lt (Norm.Basic.normSq base) (errorBounds.readingUpper 1) precision
    (Norm.Basic.normSq_nonneg base) budget.2
  let compared := compareLogarithmic circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
    errorBounds budget.1 leftStart rightStart precision precisionPositive
  have doubled := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 2) positive
  have margin := (Arithmetic.add_lt_add_right_direct tail precision).trans_eq
    (show precision + precision = 2 * precision by ring1)
  exact compared.weaken target (margin.trans doubled).le

end Output

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs

end
