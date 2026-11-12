module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Data.Rat.SmallWidth
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Normalization.InverseModelRootSamples
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation.Rational.Geometric

section

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)
open Purelib.Riemann.Normalization.InverseModelRootSamples (RootSamples)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (parameter_nonzero)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)

variable {polynomial : Polynomial} {box : Box} {model : Model polynomial box} {point : Gaussian}

@[expose] public section

/-!
# Certified operational roots of a retained polynomial model

The finite Newton samples themselves supply the square law and the selected
root channel. Attaching a winding owner preserves that channel. This makes
the root occurrence agree with the polynomial used by downstream primitives,
without identifying an independently prepared continuation by its residual.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootChannels

namespace RootSamples

open Purelib.Approximation in
open Purelib.Data in
/-- A coherent finite approximation of the squared retained root samples.

The original residual scale supplies the shrinking comparison radius and finite refinement procedure, while the retained
root bound controls every squared reading. -/
def squareApproximation (data : RootSamples model point) (inside : box.Contains point) :
    Gaussian.Sequence.ApproximationData where
  sample := fun index => let root := data.sample index; root * root
  radiusSq := quarterRadius (4 * data.residualScale)
  radiusSq_nonneg := Basic.quarterRadius_nonneg
    (Arithmetic.mul_nonneg_direct (by decide) data.residualScale_nonnegative)
  later_close := by
    intro earlier later order
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    have identity : data.sample later * data.sample later - data.sample earlier * data.sample earlier =
        (data.sample later * data.sample later - data.parameter) -
          (data.sample earlier * data.sample earlier - data.parameter) := by ring1
    rw [identity]
    calc
      _ ≤ 2 * (normSq (data.sample later * data.sample later - data.parameter) +
          normSq (data.sample earlier * data.sample earlier - data.parameter)) := (by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using (Gaussian.Norm.Bounds.normSq_sub_le_two _ _))
      _ ≤ 2 * (quarterRadius data.residualScale earlier +
        quarterRadius data.residualScale earlier) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct
            ((data.residual_bound inside later).trans
              (quarterRadius_antitone data.residualScale_nonnegative order))
            (data.residual_bound inside earlier)) (by decide)
      _ = _ := by rw [Basic.quarterRadius_eq_mul_pow,
        Basic.quarterRadius_eq_mul_pow]; ring1
  refineIndex := fun current target _ => Search.firstQuarterBelow (4 * data.residualScale) current
    target
  refineIndex_ge := fun current target _ => Search.firstQuarterBelow_ge _ current target
  refineIndex_accurate := fun current target positive =>
    Search.firstQuarterBelow_accurate _
      (Arithmetic.mul_nonneg_direct (by decide) data.residualScale_nonnegative) current target
        positive
  centerBound := data.bound ^ 2
  centerBound_nonneg := Arithmetic.sq_nonneg_direct _
  sample_bounded := fun index => by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    rw [normSq_mul, pow_two]
    exact Arithmetic.mul_le_mul_direct (data.sample_bounded inside index)
      (data.sample_bounded inside index) (normSq_nonneg _) data.bound_nonnegative

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Compare the squared sample approximation with the original polynomial value.

A finite geometric search gives one common tail beyond both requested stages for every positive error. -/
def squareEquivalent (data : RootSamples model point) (inside : box.Contains point) :
    Equivalent (squareApproximation data inside)
      (Gaussian.Sequence.Constant.constantApproximation data.parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let index := Search.firstQuarterBelow data.residualScale start target
    have late := Search.firstQuarterBelow_ge data.residualScale start target
    have leftBound : leftStart ≤ start := by
      change leftStart ≤ max leftStart rightStart
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_left _ _
    have rightBound : rightStart ≤ start := by
      change rightStart ≤ max leftStart rightStart
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_right _ _
    refine ⟨index, index, leftBound.trans late, rightBound.trans late, ?_⟩
    intro left right leftLater _rightLater
    simpa only [squareApproximation,
      Gaussian.Sequence.Constant.constantApproximation, Gaussian.Norm.Basic.normSq_eq_canonical] using
      (data.residual_bound inside left).trans_lt
      ((quarterRadius_antitone data.residualScale_nonnegative leftLater).trans_lt
        (Search.firstQuarterBelow_accurate data.residualScale data.residualScale_nonnegative
          start target positive))

open Purelib.Riemann in
open Purelib.Approximation in
/-- Certify the retained raw root channel's square law from its actual polynomial samples.

The finite residual bound identifies the product channel with the exact polynomial value at the contained point. -/
def square (data : RootSamples model point) (small : model.bound ≤ 1 / 256) (inside : box.Contains point) :
    SquareIdentity (CoherentNamed.ofApproximation (data.approximation small inside))
      data.parameter := by
  let source := data.approximation small inside
  let product := squareApproximation data inside
  have actualToProduct : NamedEquivalent
      (Gaussian.Name.Basic.Named.mul source.toNamed source.toNamed) product.toNamed :=
    Gaussian.Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise source source product (by
      intro index; rfl)
  have productToConstant := Gaussian.Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (squareEquivalent data inside)
  exact actualToProduct.trans (productToConstant.trans
    (Gaussian.Sequence.Name.Exact.exact_toConstantNamed data.parameter).symm)

end RootSamples

open Purelib.Data in
/-- The polynomial value of a retained inverse model is nonzero in its box.

A zero parameter would make its inverse-root residual have quadrance one,
contradicting the original retained bound of at most one sixteenth. -/
theorem parameter_nonzero (model : Model polynomial box) (point : Gaussian) (inside : box.Contains point) :
    polynomial.eval point ≠ 0 := by
  intro zero
  have residual := (model.residualBound point inside).trans model.bound_small
  rw [model.residual_eq,
      zero, Gaussian.Basic.zero_mul, Gaussian.Basic.sub_zero, normSq_one] at residual
  exact (not_lt_of_ge residual) (by decide : (1 / 16 : Coordinate) < 1)

open Purelib.Riemann in
open Purelib.Approximation in
set_option genInjectivity false in
/-- An operational root channel tied to one retained inverse-polynomial sample bank.

The record keeps the model tolerance, containment, prepared denominator, square law and winding-owner attachment for the
same original polynomial value. -/
structure RootChannel (model : Model polynomial box) (point : Gaussian) where
  /-- The inverse model meets the root-sample tolerance of 1/256. -/ small : model.bound ≤ 1 / 256
  /-- The original point lies in the retained model box. -/ inside : box.Contains point
  /-- The retained polynomial root-sample bank at that point. -/ samples : RootSamples model point
  /-- The prepared apart denominator equivalent to the retained sample channel. -/ prepared :
    Gaussian.Division.Prepared (CoherentNamed.ofApproximation
    (samples.approximation small inside))
  /-- The prepared denominator squares to the original polynomial value. -/ square : SquareIdentity prepared.denominator
    (polynomial.eval point)
  /-- The winding-owner attachment for the same prepared root channel. -/ attachment :
    RootContinuation.SquareRootChannelOwnership.Attachment prepared.denominator (polynomial.eval point)

constructive_injectivity RootChannel

end Purelib.Riemann.Normalization.InverseModelRootChannels

end

public section

namespace Purelib.Riemann.Normalization.InverseModelRootChannels.RootChannel

open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Riemann.RootContinuation

/-- The original sample bank, its apart preparation and its same-polynomial square certificate.

This exact dependent pair retains the numerical fields of the original root
channel at the original model, point, tolerance and containment. A winding
attachment is a later construction on this same prepared denominator.
-/
abbrev Preparation (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) :=
  (samples : RootSamples model point) ×
    (prepared : Prepared
      (CoherentNamed.ofApproximation (samples.approximation small inside))) ×
      SquareIdentity prepared.denominator (polynomial.eval point)

namespace Preparation

/-- Read the whole original sample bank of the supplied numerical preparation. -/
@[expose] def samples {small : model.bound ≤ 1 / 256} {inside : box.Contains point}
    (cached : Preparation model small point inside) : RootSamples model point := cached.1

/-- Read the same prepared apart denominator indexed by the supplied original sample bank. -/
@[expose] def prepared {small : model.bound ≤ 1 / 256} {inside : box.Contains point}
    (cached : Preparation model small point inside) :
    Prepared
      (CoherentNamed.ofApproximation ((samples cached).approximation small inside)) := cached.2.1

/-- Read the actual square comparison of the supplied original prepared denominator. -/
@[expose] def square {small : model.bound ≤ 1 / 256} {inside : box.Contains point}
    (cached : Preparation model small point inside) :
    SquareIdentity (prepared cached).denominator (polynomial.eval point) := cached.2.2

/-- Package the same actual numerical root, apartness and square comparison without computing a winding attachment. -/
@[expose] def certificate {small : model.bound ≤ 1 / 256} {inside : box.Contains point}
    (cached : Preparation model small point inside) :
    CertifiedSquareRoot.Certificate (polynomial.eval point) :=
  ⟨(prepared cached).denominator, (prepared cached).apart, square cached⟩

open Purelib.Approximation

/-- Compare the actual retained model samples with their same prepared numerical root on finite tails. -/
@[expose] def samples_equivalent {small : model.bound ≤ 1 / 256} {inside : box.Contains point}
    (cached : Preparation model small point inside) :
    Equivalent (cached.samples.approximation small inside)
      (Gaussian.Name.Sampling.approximation cached.certificate.value.name) :=
  (Equivalent.toNamed_sampling (cached.samples.approximation small inside)).symm.trans cached.prepared.equivalent

section SpatialComparison

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

/-- Compare the same model's two actual prepared numerical roots without constructing winding attachments.

The actual point caches and their original containment and small-residual
indices feed the original sample comparisons. Independent starting stages
and the retained product-derivative ceiling determine the same finite
spatial comparison procedure as the complete root-channel view.
-/
@[expose] def comparePoints {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} {firstSmall lastSmall : model.bound ≤ 1 / 256}
    {firstInside : box.Contains start} {lastInside : box.Contains finish}
    (first : Preparation model firstSmall start firstInside) (last : Preparation model lastSmall finish lastInside)
    (leftStart rightStart : Nat) (accuracy : Coordinate) (positive : 0 < accuracy) :
    Equivalence.Comparison (Name.Sampling.approximation last.certificate.value.name)
      (Name.Sampling.approximation first.certificate.value.name) leftStart rightStart
      (32 * bounds.bound * Basic.Canonical.normSq (finish - start) + accuracy) := by
  let precision := accuracy / 16
  have precisionPositive : 0 < precision := Fraction.Order.Field.div_pos_direct positive (by decide)
  let left := last.samples_equivalent.symm.compare leftStart 0 precision precisionPositive
  let right := first.samples_equivalent.symm.compare rightStart 0 precision precisionPositive
  let middle := first.samples.comparePoints bounds last.samples lastSmall firstInside lastInside
    left.rightIndex right.rightIndex precision precisionPositive
  let combined := left.trans (middle.trans right.symm)
  have ordered : 2 * (precision + 2 *
      (8 * bounds.bound * Basic.Canonical.normSq (finish - start) + precision + precision)) ≤
      32 * bounds.bound * Basic.Canonical.normSq (finish - start) + accuracy := by
    have paid : 2 * (precision + 2 *
        (8 * bounds.bound * Basic.Canonical.normSq (finish - start) + precision + precision)) =
        32 * bounds.bound * Basic.Canonical.normSq (finish - start) + (10 / 16 : Coordinate) * accuracy := by
      dsimp only [precision]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rewrite [paid]
    have fraction := Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide +kernel : (10 / 16 : Coordinate) < 1) positive
    rewrite [Fraction.Field.one_mul] at fraction
    exact (Arithmetic.add_lt_add_left_direct fraction _).le
  exact combined.weaken _ ordered

end SpatialComparison

section ScaledComparison

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

/-- Compare an actually scaled model root with the original root at another displayed coordinate.

Both numerical preparations retain the same original model and sample ownership.
The bound separates spatial displacement from the exact coefficient's
departure from one. Its multipliers use the exact coefficient sampler's
magnitude and the fixed original reference root sampler's magnitude. The
original product bridges and actual paid operand comparisons are consumed
once; a finite scalar request pays their combined error.
-/
@[expose] def compareScaled {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} {firstSmall lastSmall : model.bound ≤ 1 / 256}
    {firstInside : box.Contains start} {lastInside : box.Contains finish}
    (first : Preparation model firstSmall start firstInside) (last : Preparation model lastSmall finish lastInside)
    (coefficient : Gaussian) (leftStart rightStart : Nat) (accuracy : Coordinate) (positive : 0 < accuracy) :
    let magnitude := (Name.Sampling.approximation (Coherence.exact coefficient).name).centerBound
    let reference := (Name.Sampling.approximation first.certificate.value.name).centerBound
    Equivalence.Comparison
      (Name.Sampling.approximation (last.certificate.value.mul (Coherence.exact coefficient)).name)
      (Name.Sampling.approximation first.certificate.value.name) leftStart rightStart
      (128 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq (finish - start) +
        4 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + accuracy) := by
  let magnitude := (Name.Sampling.approximation (Coherence.exact coefficient).name).centerBound
  let reference := (Name.Sampling.approximation first.certificate.value.name).centerBound
  let allowance := 14 + 8 * (magnitude + reference)
  have allowanceNonnegative : 0 ≤ allowance :=
    add_nonneg (by decide : (0 : Coordinate) ≤ 14)
      (Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (Name.Sampling.approximation (Coherence.exact coefficient).name).centerBound_nonneg
          (Name.Sampling.approximation first.certificate.value.name).centerBound_nonneg))
  let precision := SmallWidth.shrinkingWidth allowance accuracy
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos allowanceNonnegative positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt allowanceNonnegative positive
  let firstBridge := (Bridge.coherentMul_toSampled last.certificate.value (Coherence.exact coefficient)).compare
    leftStart 0 precision precisionPositive
  let lastBridge := ((Bridge.coherentMul_toSampled first.certificate.value (Coherence.exact 1)).symm.trans
    (Arithmetic.Mul.coherentMul_one_right first.certificate.value)).compare 0 rightStart precision precisionPositive
  let rootComparison := (first.comparePoints bounds last 0 0 precision precisionPositive).weaken
    (32 * bounds.bound * Norm.Basic.normSq (finish - start) + precision) (by
      rewrite [Norm.Basic.normSq_eq_canonical]
      exact Fraction.Order.Basic.le_refl _)
  let coefficientComparison := Equivalence.Comparison.of_constant_samples
    (Name.Sampling.approximation (Coherence.exact coefficient).name)
    (Name.Sampling.approximation (Coherence.exact 1).name) coefficient 1
    (Sequence.Name.Exact.exactNamedSample coefficient) (Sequence.Name.Exact.exactNamedSample 1)
    0 0 precision precisionPositive
  let product := Sequence.Arithmetic.Product.Congruence.pointwiseComparison rootComparison coefficientComparison
    (Sequence.Arithmetic.Product.sampledProductApproximation_sample last.certificate.value.name
      (Coherence.exact coefficient).name)
    (Sequence.Arithmetic.Product.sampledProductApproximation_sample first.certificate.value.name
      (Coherence.exact 1).name)
  let combined := firstBridge.trans (product.trans lastBridge)
  have same : 2 * (precision + 2 *
      (2 * ((32 * bounds.bound * Norm.Basic.normSq (finish - start) + precision) * magnitude +
        reference * (Norm.Basic.normSq (coefficient - 1) + precision)) +
        (32 * bounds.bound * Norm.Basic.normSq (finish - start) + precision) +
        (Norm.Basic.normSq (coefficient - 1) + precision) + precision)) =
      128 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq (finish - start) +
        4 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + allowance * precision := by
    dsimp only [allowance]
    ring1
  exact combined.weaken _ (by
    change 2 * (precision + 2 *
      (2 * ((32 * bounds.bound * Norm.Basic.normSq (finish - start) + precision) * magnitude +
        reference * (Norm.Basic.normSq (coefficient - 1) + precision)) +
        (32 * bounds.bound * Norm.Basic.normSq (finish - start) + precision) +
        (Norm.Basic.normSq (coefficient - 1) + precision) + precision)) ≤ _
    rewrite [same]
    exact (Arithmetic.add_lt_add_left_direct paid _).le)

end ScaledComparison

end Preparation

/-- Prepare the original point samples and certified apart root from the same retained polynomial model.

The actual sample bank is computed once. Its finite residual comparison
prepares that same numerical root and its square law; no independent root
or winding owner is selected by this numerical phase.
-/
@[expose] def prepare (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) : Preparation model small point inside := by
  let samples := RootSamples.build model point
  let square := RootSamples.square samples small inside
  let prepared := SquareRootProvenance.prepared_of_square square
    (parameter_nonzero model point inside)
  have preparedSquare : SquareIdentity prepared.denominator (polynomial.eval point) :=
    (Congruence.coherentMul_respects prepared.denominator
      (CoherentNamed.ofApproximation (samples.approximation small inside)) prepared.denominator
      (CoherentNamed.ofApproximation (samples.approximation small inside))
      prepared.equivalent.symm prepared.equivalent.symm).trans square
  exact ⟨samples, prepared, preparedSquare⟩

section PreparationBounds

open Purelib.Riemann.Branches
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

/-- The original numerical preparation retains the square-residual constructor's exact whole-ball lower floor. -/
theorem prepare_lowerSq (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) :
    (prepare model small point inside).prepared.apart.certificate.lowerSq =
      SquareRootSheets.sampleNormLower (polynomial.eval point) / 8 := rfl

/-- The numerical preparation preserves the center ceiling of its actual cached original root samples. -/
theorem prepare_centerBound (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) :
    (prepare model small point inside).certificate.value.name.process.centerBound =
      2 * (1 + (prepare model small point inside).samples.bound) := rfl

/-- The original regional polynomial clearance gives a uniform positive floor for every canonical prepared root.

The actual pointwise denominator retains its original residual floor.
Monotonicity of the clipped polynomial quadrance bounds that same floor
from the retained clearance; no independent root or new preparation is made.
-/
theorem prepare_lower_bound (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (clearance : RegionClearance polynomial box) (point : Gaussian) (inside : box.Contains point) :
    min 1 (clearance.bound / 4) / 8 ≤ (prepare model small point inside).prepared.apart.certificate.lowerSq := by
  rewrite [prepare_lowerSq]
  have lower := clearance.lower point inside
  rewrite [Norm.Basic.normSq_eq_canonical] at lower
  have divided := Fraction.Order.Field.divide_mono lower (by decide : (0 : Coordinate) < 4)
  have clipped := Fraction.Order.Basic.min_le_min (Fraction.Order.Basic.le_refl (1 : Coordinate)) divided
  have floor := clipped.trans (Fraction.Order.Basic.le_max_left _ (SquareRootSheets.coordinateNormLower
    (polynomial.eval point) / 2))
  exact Fraction.Order.Field.divide_mono floor (by decide)

/-- A bound on the same actual polynomial value bounds the retained numerical root process's center ceiling. -/
theorem prepare_centerBound_le (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (upper : Coordinate)
    (bounded : Norm.Basic.normSq (polynomial.eval point) ≤ upper) :
    (prepare model small point inside).certificate.value.name.process.centerBound ≤ 2 * (1 + (4 + upper)) := by
  rewrite [prepare_centerBound]
  rewrite [Norm.Basic.normSq_eq_canonical] at bounded
  change 2 * (1 + (4 + normSq (polynomial.eval point))) ≤ _
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Coordinate))
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (4 : Coordinate)) bounded)) (by decide)

/-- Canonical resampling preserves the same uniform center ceiling of the supplied prepared numerical root. -/
theorem prepare_samplerBound_le (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (upper : Coordinate)
    (bounded : Norm.Basic.normSq (polynomial.eval point) ≤ upper) :
    (Purelib.Approximation.Gaussian.Name.Sampling.approximation
      (prepare model small point inside).certificate.value.name).centerBound ≤ 2 * (1 + 2 * (1 + (4 + upper))) := by
  change 2 * (1 + (prepare model small point inside).certificate.value.name.process.centerBound) ≤ _
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (1 : Coordinate))
      (prepare_centerBound_le model small point inside upper bounded)) (by decide)

end PreparationBounds

/-- Retain the complete numerical fields of an original root channel as their exact preparation view. -/
@[expose] def preparation (channel : RootChannel model point) :
    Preparation model channel.small point channel.inside :=
  ⟨channel.samples, channel.prepared, channel.square⟩

/-- An exact whole numerical preparation indexed by its original complete root channel.

The equality retains the original sample bank, apart preparation and square
certificate together. Its value may be supplied before winding attachment;
the original channel remains the nominal parent of the view.
-/
abbrev PreparationView (channel : RootChannel model point) :=
  { cached : Preparation model channel.small point channel.inside // cached = channel.preparation }

/-- Construct the original complete root channel from its retained numerical preparation.

The supplied cache feeds every original numerical field and the unchanged
winding-attachment constructor. Omitting it retains the literal former
sample, square and apart preparation as the default.
-/
@[expose] def build (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point)
    (cached : Preparation model small point inside := prepare model small point inside) :
    RootChannel model point :=
  let samples := Preparation.samples cached
  let prepared := Preparation.prepared cached
  let preparedSquare := Preparation.square cached
  let certificate := Preparation.certificate cached
  ⟨small, inside, samples, prepared, preparedSquare,
    SquareRootChannelOwnership.attach certificate⟩

/-- Building the complete root channel preserves the whole supplied numerical preparation. -/
theorem build_preparation (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (cached : Preparation model small point inside) :
    (build model small point inside cached).preparation = cached := by
  cases cached with
  | mk samples tail => cases tail; rfl

end Purelib.Riemann.Normalization.InverseModelRootChannels.RootChannel

end

@[expose] public section

namespace Purelib.Riemann.Normalization.InverseModelRootChannels

namespace RootChannel

open Purelib.Riemann in
/-- Read the certified square-root value, apartness and square law from the retained channel. -/
def certificate (channel : RootChannel model point) : RootContinuation.CertifiedSquareRoot.Certificate (polynomial.eval
  point) :=
  ⟨channel.prepared.denominator, channel.prepared.apart, channel.square⟩

open Purelib.Approximation
/-- Compare the actual polynomial samples with the certified channel on finite common tails.

The comparison reuses the original prepared denominator's equivalence for every positive requested error. -/
def samples_equivalent (channel : RootChannel model point) :
    Equivalent (channel.samples.approximation channel.small channel.inside)
      (Gaussian.Name.Sampling.approximation channel.certificate.value.name) :=
  Preparation.samples_equivalent channel.preparation

/-- The retained winding owner names the root determined by the original polynomial samples. -/
def owner_equivalent (channel : RootChannel model point) :
    NamedEquivalent
      (channel.attachment.owner.certificate channel.attachment.owner.parameterNonzero).value.name
        channel.certificate.value.name :=
  channel.attachment.equivalent.symm

section SpatialComparison

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

/-- Compare two actual certified root channels of the same model at nearby displayed coordinates.

The comparison composes the two existing channel-to-sample certificates
with the same retained product-derivative cache. Both original names,
independent requested starts, supplied point caches and actual refined
indices remain in the returned finite comparison.
-/
def comparePoints {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} (first : RootChannel model start) (last : RootChannel model finish)
    (leftStart rightStart : Nat) (accuracy : Coordinate) (positive : 0 < accuracy) :
    Equivalence.Comparison (Name.Sampling.approximation last.certificate.value.name)
      (Name.Sampling.approximation first.certificate.value.name) leftStart rightStart
      (32 * bounds.bound * Basic.Canonical.normSq (finish - start) + accuracy) :=
  Preparation.comparePoints bounds first.preparation last.preparation leftStart rightStart accuracy positive

end SpatialComparison

section ScaledComparison

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

/-- Compare an actually scaled model root with the original root at another displayed coordinate.

Both root channels retain the same original model and sample ownership.
The bound separates spatial displacement from the exact coefficient's
departure from one. Its multipliers use the exact coefficient sampler's
magnitude and the fixed original reference root sampler's magnitude. The
original product bridges and actual paid operand comparisons are consumed
once; a finite scalar request pays their combined error.
-/
def compareScaled {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} (first : RootChannel model start) (last : RootChannel model finish)
    (coefficient : Gaussian) (leftStart rightStart : Nat) (accuracy : Coordinate) (positive : 0 < accuracy) :
    let magnitude := (Name.Sampling.approximation (Coherence.exact coefficient).name).centerBound
    let reference := (Name.Sampling.approximation first.certificate.value.name).centerBound
    Equivalence.Comparison
      (Name.Sampling.approximation (last.certificate.value.mul (Coherence.exact coefficient)).name)
      (Name.Sampling.approximation first.certificate.value.name) leftStart rightStart
      (128 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq (finish - start) +
        4 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + accuracy) :=
  Preparation.compareScaled bounds first.preparation last.preparation coefficient leftStart rightStart accuracy positive

end ScaledComparison

end RootChannel
end Purelib.Riemann.Normalization.InverseModelRootChannels

end

end
