module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian

public section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.SquareRoot.Radius
open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational.Box.Square
open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.AlignedInverseRootSeed
open Purelib.Riemann.Normalization.ContinuedInverseRoot
open Purelib.Riemann.Normalization.InverseRootPrimitive
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods
open Purelib.Riemann.Topology

/-!
# Local reciprocal primitives on the retained exterior occurrence

The primitive patch is seeded by the reciprocal owner attached to the actual
prepared source root. Its negative, reversed differential coefficient is
compared with the persisted source coefficient, paying both the inverse-root
model error and the source model allowance. The comparison concerns actual
primitive increments; it does not identify an inverted arc with its chord.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples (Attachment ownerCoefficient
  coefficientAllowance)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {boundary :
    ParentOnBoundary parent
    (Ambient curve)}

/-- Reuse the existing semantic neighborhood cache; the source name is the attached owner's actual program, not a newly
isolated square root. -/
abbrev Patch (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (attached : Attachment parent boundary) (count : Nat) :=
  TracedPrimitiveNeighborhood.NeighborhoodData (HyperellipticReciprocal.polynomial curve)
    (parent.edge.point 0)⁻¹ count (OwnerTraceReadings.ownerName attached.owner)
    (fun patch => OwnerTraceReadings.ownerName patch.base.seed.owner)

namespace Patch

variable {attached : Attachment parent boundary}

/-- The continued neighborhood retains exactly the supplied aligned inverse-root seed. -/
theorem ofAligned_seed {polynomial : ClearPath.GaussianPolynomial}
    (site : PreparedObservationNeighborhoods.ObservationNeighborhood polynomial count)
    {owner : SquareRootContinuationChain.Owner (polynomial.eval site.center)}
    (aligned : AlignedInverseRootSeed.AlignedSeed owner) :
    (ContinuedNeighborhood.ofAligned site aligned).base.seed = aligned.seed := rfl

/-- The aligned seed channel is operationally equivalent to the original owner channel by retained initial refinement.
-/
def alignedEquivalent {parameter : Data.Gaussian.Basic.Canonical} (owner : SquareRootContinuationChain.Owner parameter)
    (aligned : AlignedInverseRootSeed.AlignedSeed owner) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner) (OwnerTraceReadings.ownerName
      aligned.seed.owner) :=
  PreparedPrimitiveSheets.rootEquivalent_of_initial_refines owner.parameterNonzero
    owner.track aligned.seed.owner.track aligned.refines

/-- Build a reciprocal primitive patch from the original attached owner and its aligned seed.

The cached neighborhood remains centered at the exact reciprocal start, with operational equivalence to the same
retained owner channel. -/
@[expose] def build (attached : Attachment parent boundary) (count : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary attached count := by
  let site := ObservationNeighborhood.ofPoint (HyperellipticReciprocal.polynomial curve)
    count (parent.edge.point 0)⁻¹ attached.owner.parameterNonzero
  let aligned := AlignedSeed.ofOwner attached.owner
  let neighborhood := ContinuedNeighborhood.ofAligned site aligned
  refine ⟨neighborhood, rfl, ?_⟩
  change Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName attached.owner)
    (OwnerTraceReadings.ownerName (ContinuedNeighborhood.ofAligned site aligned).base.seed.owner)
  rw [ofAligned_seed]
  exact alignedEquivalent attached.owner aligned

/-- The original reciprocal starting point belongs to its retained primitive patch. -/
theorem start_inside (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary
  attached count) :
    patch.patch.box.Contains (parent.edge.point 0)⁻¹ := by
  have inside := patch.patch.center_inside
  rw [patch.center_eq] at inside
  exact inside

/-- At the retained center, the point certificate channel is equivalent to the original patch seed channel. -/
def seedPointEquivalent {polynomial : ClearPath.GaussianPolynomial}
    (patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count) {point : Data.Gaussian.Basic.Canonical}
    (equal : patch.base.site.center = point) (sample : ContinuedNeighborhood.Point patch point) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName patch.base.seed.owner)
      sample.certificate.value.name := by
  cases equal
  exact PreparedPrimitiveSheets.rootEquivalent_of_initial_refines sample.owner.parameterNonzero
    patch.base.seed.owner.track sample.owner.track sample.refines

/-- The retained center-point certificate represents the same channel as the original attached owner. -/
@[expose] def pointEquivalent (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent
  boundary attached count)
    (sample : ContinuedNeighborhood.Point patch.patch (parent.edge.point 0)⁻¹) :
    Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName attached.owner) sample.certificate.value.name :=
  patch.seedEquivalent.trans (seedPointEquivalent patch.patch patch.center_eq sample)

/-- The original attached reciprocal coefficient is equivalent to the negatively oriented retained primitive coefficient
samples. -/
private def coefficientComparison (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch
  parent boundary attached count)
    (sample : ContinuedNeighborhood.Point patch.patch (parent.edge.point 0)⁻¹) (index : Nat) :
    Gaussian.Equivalence.Equivalent (Sampling.approximation (ownerCoefficient attached).name)
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (Coherence.exact (-1)).name
        (PreparedPrimitiveEquivalence.coefficient (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
          sample index (HyperellipticReciprocal.reversedDifferential differential)).name) := by
  let certificate := attached.owner.certificate attached.owner.parameterNonzero
  let based := PreparedPrimitiveEquivalence.basedRoot (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    sample index
  let apart := PreparedPrimitiveEquivalence.basedApart (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    sample index
  let coefficient := PreparedPrimitiveEquivalence.coefficient (curve := HyperellipticReciprocalCurve.reciprocalCurve
    curve)
    sample index (HyperellipticReciprocal.reversedDifferential differential)
  have roots := (patch.pointEquivalent sample).trans (sample.certificate.value.basedEquivalent (sample.readingState
    index))
  have same := Value.differentialValue_respects_sheet
    (HyperellipticReciprocal.reversedDifferential differential) (parent.edge.point 0)⁻¹
    certificate.value based certificate.apart apart roots
  have signed := Congruence.coherentMul_respects (Coherence.exact (-1)) (Coherence.exact (-1)) _ _
    (NamedEquivalent.refl _) same
  exact Equivalent.trans (signed.trans (Bridge.coherentMul_toNamed (Coherence.exact (-1)) coefficient))
    (Equivalent.toNamed_sampling (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (Coherence.exact
      (-1)).name coefficient.name))

/-- A source allowance is still charged: a persisted rational coefficient is not asserted to equal the differential's
operational value. -/
@[expose] def coefficientError (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent
  boundary attached count) (index : Nat) : Fraction.Rational :=
  2 * Data.Gaussian.Norm.Basic.normSq ((PreparedPrimitiveSamples.differentialNumerator
    (HyperellipticReciprocal.reversedDifferential differential)).eval
      (parent.edge.point 0)⁻¹) * Geometric.Basic.quarterRadius patch.patch.inverseErrorScale index +
    2 * coefficientAllowance parent parent.edge.modelErrorAllowance

/-- The signed inverse-polynomial coefficient at the original center satisfies the retained source allowance and
inverse-model error bound. -/
theorem coefficient_center_le (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent
  boundary attached count) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (-((PreparedPrimitiveSamples.differentialNumerator
      (HyperellipticReciprocal.reversedDifferential differential)).eval
        (parent.edge.point 0)⁻¹ * (patch.patch.base.refine index).value.eval (parent.edge.point 0)⁻¹) -
      (PreparedExteriorReciprocal.parentSample parent boundary).coefficient) ≤ patch.coefficientError index := by
  let sample := ContinuedNeighborhood.Point.acquire patch.patch (parent.edge.point 0)⁻¹ patch.start_inside
  let coefficient := PreparedPrimitiveEquivalence.coefficient (curve := HyperellipticReciprocalCurve.reciprocalCurve
    curve)
    sample index (HyperellipticReciprocal.reversedDifferential differential)
  let equivalent := Equivalent.trans (patch.coefficientComparison sample index).symm
    (PreparedReciprocalSamples.centerComparison parent boundary attached)
  let comparison := equivalent.compare 0 0 parent.edge.modelErrorAllowance parent.edge.modelErrorAllowance_positive
  let value := (Sampling.approximation coefficient.name).sample comparison.leftIndex
  let later := parent.center.laterValue comparison.rightIndex
  let multiplier := -(parent.edge.point 0 ^ 2)
  have close : Data.Gaussian.Norm.Basic.normSq (-value - multiplier * later) ≤ parent.edge.modelErrorAllowance
    := by
    have bound := (comparison.close (Nat.le_refl _) (Nat.le_refl _)).le
    change Data.Gaussian.Norm.Basic.normSq ((-1 : Data.Gaussian.Basic.Canonical) * value - multiplier * later)
      ≤ _ at bound
    have scalar : (-1 : Data.Gaussian.Basic.Canonical) * value = -value := by ring1
    rewrite [scalar] at bound
    exact bound
  have modeled := PreparedPrimitiveEquivalence.coefficient_possible_bound
    (curve := HyperellipticReciprocalCurve.reciprocalCurve curve) sample patch.start_inside index
    (HyperellipticReciprocal.reversedDifferential differential) _
    (Gaussian.Process.Sampling.witnessAt_possible coefficient.name.process coefficient.name.state comparison.leftIndex)
  simp only [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at modeled
  have centerBound : Data.Gaussian.Norm.Basic.normSq (multiplier * later - multiplier * parent.center.value) ≤
      Data.Gaussian.Norm.Basic.normSq (parent.edge.point 0) ^ 2 * parent.edge.modelErrorAllowance := by
    rw [← mul_sub, Data.Gaussian.Norm.Basic.normSq_mul]
    dsimp only [multiplier]
    rw [Data.Gaussian.Norm.Basic.normSq_neg, Power.normSq_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parent.center.laterValue_sub_value_lt comparison.rightIndex).le (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have sourceBound : Data.Gaussian.Norm.Basic.normSq (-value - multiplier * parent.center.value) ≤
      coefficientAllowance parent parent.edge.modelErrorAllowance :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ (multiplier * later) _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add close centerBound) (by decide))
  let polynomialValue := (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential
    differential)).eval
    (parent.edge.point 0)⁻¹ * (patch.patch.base.refine index).value.eval (parent.edge.point 0)⁻¹
  have signedModeled : Data.Gaussian.Norm.Basic.normSq (-polynomialValue - -value) ≤
      Data.Gaussian.Norm.Basic.normSq ((PreparedPrimitiveSamples.differentialNumerator
        (HyperellipticReciprocal.reversedDifferential differential)).eval
        (parent.edge.point 0)⁻¹) * Geometric.Basic.quarterRadius patch.patch.inverseErrorScale index := by
    rw [show -polynomialValue - -value = -(polynomialValue - value) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact modeled
  have ideal : (PreparedExteriorReciprocal.parentSample parent boundary).coefficient = multiplier * parent.center.value
    := by
    rw [PreparedExteriorReciprocal.parentSample_coefficient]
    dsimp only [multiplier]
    ring1
  rw [ideal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via (-polynomialValue) (-value) _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add signedModeled sourceBound) (by
      decide)).trans_eq
      (by
          dsimp only [coefficientError];
          ring1))

end Patch

/-- Truncate the retained constant source model without preparing a new root or changing its coefficient, allowance, or
observation cache. -/
@[expose] def prefixCell (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (fraction :
  Fraction.Rational) :
    Cell.Basic.CellModel := { parent.model with finish := parent.edge.point fraction }

/-- The complete source prefix is exactly the original constant cell model. -/
theorem prefixCell_one (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) :
  prefixCell parent 1 = parent.model := rfl

/-- The retained source prefix sample is its exact displacement times the original cached center coefficient. -/
theorem prefixCell_integralSample (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (fraction :
  Fraction.Rational) :
    (prefixCell parent fraction).integralSample =
      (parent.edge.point fraction - parent.edge.point 0) * parent.center.value :=
  Cell.Basic.CellModel.integralSample_constant
    (prefixCell parent fraction) parent.center.value
      rfl

/-- The source comparator is exactly the corresponding fraction of the original retained cell sample, not a separately
constructed period program. -/
theorem prefixCell_integralSample_eq_scale (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
  (fraction : Fraction.Rational) :
    (prefixCell parent fraction).integralSample =
      Scale.scale fraction parent.model.integralSample := by
  rw [prefixCell_integralSample,
    Cell.Basic.CellModel.integralSample_constant parent.model parent.center.value rfl]
  change (parent.edge.localSegment.pointAt fraction - parent.edge.localSegment.pointAt 0) * parent.center.value =
    Scale.scale fraction ((parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) *
      parent.center.value)
  apply Data.Gaussian.Basic.ext <;>
    simp only [ClearSegment.pointAt, Scale.scale_re, Scale.scale_im,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1

/-- Construct the reciprocal comparator of the original constant prefix using its retained endpoint nonvanishing
certificates. -/
private def prefixSample (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) : ReciprocalPathSamples.Cell
      (prefixCell parent fraction) :=
  ReciprocalPathSamples.Cell.build ⟨parent.center.value, rfl⟩
    (PreparedExteriorReciprocal.parent_point_nonzero boundary parent.edge.baseInside)
    (PreparedExteriorReciprocal.parent_point_nonzero boundary inside)

namespace Patch

variable {attached : Attachment parent boundary} {patch :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary attached count}
  {index : Nat}

/-- The retained inverse-model and source-allowance coefficient error is nonnegative. -/
theorem coefficientError_nonnegative (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch
  parent boundary attached count) (index : Nat) :
    0 ≤ patch.coefficientError index := by
  unfold coefficientError coefficientAllowance
  exact add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
      (Geometric.Basic.quarterRadius_nonneg patch.patch.inverseErrorScale_positive.le index))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg parent.edge.modelErrorAllowance_positive.le
          (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
            parent.edge.modelErrorAllowance_positive.le))))

/-- The orientation sign belongs to the primitive itself. -/
@[expose] def increment (model : InverseRootPrimitive.PrimitiveModel patch.patch index
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)))
      (fraction : Fraction.Rational) : Gaussian :=
  -(model.primitive.value.eval (parent.edge.point fraction)⁻¹ - model.primitive.value.eval (parent.edge.point 0)⁻¹)

/-- The retained reciprocal primitive increment differs from the exact constant-prefix comparator by its Taylor
remainder and paid coefficient error. -/
private theorem ideal_increment_error (model : InverseRootPrimitive.PrimitiveModel patch.patch index
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)))
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (finishInside : patch.patch.box.Contains (parent.edge.point fraction)⁻¹) :
    Data.Gaussian.Norm.Basic.normSq
      (increment model fraction -
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixSample parent boundary fraction
      inside).sample) ≤
      2 * model.primitive.remainderBound * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
        parent.edge.point 0) ^ 2 +
        2 * patch.coefficientError index * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
          parent.edge.point 0) := by
  let reading := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixSample parent boundary
    fraction inside
  let delta := (parent.edge.point fraction)⁻¹ - (parent.edge.point 0)⁻¹
  let coefficient := model.coefficient.eval (parent.edge.point 0)⁻¹
  let remainder := model.primitive.value.eval (parent.edge.point fraction)⁻¹ -
    model.primitive.value.eval (parent.edge.point 0)⁻¹ - coefficient * delta
  have taylor : Data.Gaussian.Norm.Basic.normSq remainder ≤ model.primitive.remainderBound *
    Data.Gaussian.Norm.Basic.normSq delta ^ 2 :=
    model.primitive.increment_bound patch.start_inside finishInside
  have coefficientBound : Data.Gaussian.Norm.Basic.normSq (-coefficient - reading.coefficient) ≤
    patch.coefficientError index := by
    dsimp only [coefficient]
    rw [model.coefficient_eq]
    exact patch.coefficient_center_le index
  have identity : increment model fraction -
    reading.sample = -remainder + (-coefficient - reading.coefficient) * delta := by
    rw [reading.sample_eq, reading.start_eq, reading.finish_eq]
    change -(model.primitive.value.eval (parent.edge.point fraction)⁻¹ - model.primitive.value.eval (parent.edge.point
      0)⁻¹) -
      delta * reading.coefficient = _
    dsimp only [remainder]
    ring1
  have distance : Data.Gaussian.Norm.Basic.normSq delta ≤ Data.Gaussian.Norm.Basic.normSq
    (parent.edge.point fraction - parent.edge.point 0) :=
    PreparedReciprocalSamples.inverse_movement_between (boundary.point parent.edge.baseInside) (boundary.point inside)
  rw [identity]
  calc
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (-remainder) + Data.Gaussian.Norm.Basic.normSq
      ((-coefficient - reading.coefficient) * delta)) := Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (model.primitive.remainderBound * Data.Gaussian.Norm.Basic.normSq delta ^ 2 +
      patch.coefficientError index * Data.Gaussian.Norm.Basic.normSq delta) := by
      rw [Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientBound
          (Data.Gaussian.Norm.Basic.normSq_nonneg _))) (by decide)
    _ ≤ 2 * (model.primitive.remainderBound * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
      parent.edge.point 0) ^ 2 +
        patch.coefficientError index * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
          parent.edge.point 0)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) distance 2)
            model.primitive.remainderBound_nonnegative)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance (patch.coefficientError_nonnegative
          index))) (by decide)
    _ = _ := by ring1

/-- Compare the actual reciprocal primitive increment to the original retained source model. The non-affine inversion
remainder is paid separately from the primitive Taylor error and operational coefficient discrepancy. -/
theorem increment_error (model : InverseRootPrimitive.PrimitiveModel patch.patch index
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)))
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (finishInside : patch.patch.box.Contains (parent.edge.point fraction)⁻¹) :
    Data.Gaussian.Norm.Basic.normSq
      (increment model fraction -
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent fraction).integralSample) ≤
      (4 * model.primitive.remainderBound + 2 * Data.Gaussian.Norm.Basic.normSq parent.center.value) *
          Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction - parent.edge.point 0) ^ 2 +
        4 * patch.coefficientError index * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
          parent.edge.point 0) := by
  let reading := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixSample parent boundary
    fraction inside
  have inversion := reading.error_bound (density := Data.Gaussian.Norm.Basic.normSq parent.center.value) (lower
    := 1)
    (by decide) le_rfl (PreparedExteriorReciprocal.boundary_norm_lower (boundary.point inside))
  have divideOne : Data.Gaussian.Norm.Basic.normSq parent.center.value / 1 =
    Data.Gaussian.Norm.Basic.normSq parent.center.value :=
    (show Data.Gaussian.Norm.Basic.normSq parent.center.value / 1 = (Data.Gaussian.Norm.Basic.normSq
      parent.center.value / 1) * 1 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  rw [divideOne] at inversion
  have reverse : Data.Gaussian.Norm.Basic.normSq (reading.sample -
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent fraction).integralSample) ≤
      Data.Gaussian.Norm.Basic.normSq parent.center.value * Data.Gaussian.Norm.Basic.normSq
        (parent.edge.point fraction - parent.edge.point 0) ^ 2 := by
    rw [show reading.sample - (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent
      fraction).integralSample =
      -((Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent fraction).integralSample
        - reading.sample) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact inversion
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via
    (increment model fraction) reading.sample
    _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (ideal_increment_error model
        fraction inside finishInside) reverse) (by decide)).trans_eq (by ring1))

set_option genInjectivity false in
/-- The entire rational image of a positive source prefix lies in this patch. This is stronger than checking its
endpoint chord. -/
structure CoveredPrefix (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent
  boundary attached count) where
  /-- The retained positive fraction of the original source parent. -/ fraction : Fraction.Rational
  /-- The retained source-prefix fraction is strictly positive. -/ positive : 0 < fraction
  /-- The retained source-prefix fraction is at most one. -/ upper : fraction ≤ 1
  /-- Every original source parameter up to the retained fraction maps into the same reciprocal primitive patch. -/
    contains : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ fraction →
    patch.patch.box.Contains (parent.edge.point parameter)⁻¹

constructive_injectivity CoveredPrefix

namespace CoveredPrefix

/-- The original source prefix movement squared norm is its parameter squared times the full retained displacement
squared norm. -/
theorem source_movement (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (parameter :
  Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point 0) = parameter ^ 2 *
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement := by
  change Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt parameter -
    parent.edge.localSegment.pointAt 0) =
    parameter ^ 2 * Data.Gaussian.Norm.Basic.normSq (parent.edge.localSegment.pointAt 1 -
      parent.edge.localSegment.pointAt 0)
  rw [parent.edge.localSegment.normSq_pointAt_sub_pointAt parameter 0,
    parent.edge.localSegment.normSq_pointAt_sub_pointAt 1 0]
  ring1

/-- The finite square-radius scan uses the original displacement and the already cached continuation radius. No root
continuation is rerun to explain or test the coverage, and a zero-length source is permitted. -/
@[expose] def build (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary
  attached count) : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.CoveredPrefix patch := by
  let scale := Data.Gaussian.Norm.Basic.normSq parent.model.displacement + 1
  have scalePositive : 0 < scale := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
  let target := patch.patch.radius ^ 2 / scale
  have targetPositive : 0 < target := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct patch.patch.radius_positive 2) scalePositive
  let fraction := Geometric.dyadicSquareRadius target
  have positive := Geometric.dyadicSquareRadius_positive target
  have upper := Dyadic.dyadicSquareRadius_le_one target
  refine ⟨fraction, positive, upper, ?_⟩
  intro parameter inside
  have interval : 0 ≤ parameter ∧ parameter ≤ 1 := ⟨inside.1, inside.2.trans upper⟩
  have distance := PreparedReciprocalSamples.inverse_movement_between
    (boundary.point parent.edge.baseInside) (boundary.point interval)
  have paid : Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ - (parent.edge.point 0)⁻¹) ≤
    patch.patch.radius ^ 2 := by
    calc
      _ ≤ Data.Gaussian.Norm.Basic.normSq (parent.edge.point parameter - parent.edge.point 0) := distance
      _ = parameter ^ 2 * Data.Gaussian.Norm.Basic.normSq parent.model.displacement := source_movement parent
        parameter
      _ ≤ fraction ^ 2 * scale := Fraction.Order.Arithmetic.mul_le_mul_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2)
        (le_add_of_nonneg_right (by decide : (0 : Fraction.Rational) ≤ 1))
        (Data.Gaussian.Norm.Basic.normSq_nonneg _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ ≤ target * scale := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Geometric.dyadicSquareRadius_sq_lt targetPositive).le scalePositive.le
      _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ scalePositive.ne'
  rw [patch.patch.box_eq, patch.center_eq]
  exact Centered.centeredBox_contains_of_normSq_sub_le patch.patch.radius_positive.le paid

/-- The retained covered prefix endpoint belongs to the original primitive patch. -/
theorem finish_inside (covered : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.CoveredPrefix
  patch) : patch.patch.box.Contains (parent.edge.point covered.fraction)⁻¹ :=
  covered.contains covered.fraction ⟨covered.positive.le, le_rfl⟩

end CoveredPrefix

set_option genInjectivity false in
/-- Executable local data with cached source and primitive samples and an exactly certified error. `inverseTarget`
controls the inverse-root model, not the entire path integral: source model error is still paid below. -/
structure Prepared (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary
  attached count) (inverseTarget : Fraction.Rational) where
  /-- The retained inverse-root refinement index selected for the original positive target. -/ index : Nat
  /-- The retained inverse-model geometric error is strictly below the original request target. -/ inverse_accurate :
    Geometric.Basic.quarterRadius patch.patch.inverseErrorScale index < inverseTarget
  /-- The cached primitive polynomial at the retained inverse-root refinement index. -/ model :
    InverseRootPrimitive.PrimitiveModel patch.patch index (PreparedPrimitiveSamples.differentialNumerator
    (HyperellipticReciprocal.reversedDifferential differential))
  /-- The retained positive source prefix whose entire reciprocal image belongs to the original patch. -/ covered :
    CoveredPrefix patch
  /-- The cached negatively oriented reciprocal primitive increment over the retained prefix. -/ value :
    Data.Gaussian.Basic.Canonical
  /-- The cached value equals the original retained primitive increment. -/ value_eq : value =
    increment model covered.fraction
  /-- The cached original constant-cell sample on the retained source prefix. -/ source : Data.Gaussian.Basic.Canonical
  /-- The cached source value equals the original prefix-cell integral sample. -/ source_eq : source =
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent
    covered.fraction).integralSample
  /-- The cached quantitative primitive and source comparison allowance. -/ error : Fraction.Rational
  /-- The cached allowance is exactly the Taylor, inversion and coefficient-error expression on the original prefix
    movement. -/ error_eq : error = (4 * model.primitive.remainderBound + 2 * Data.Gaussian.Norm.Basic.normSq
    parent.center.value) *
      Data.Gaussian.Norm.Basic.normSq (parent.edge.point covered.fraction - parent.edge.point 0) ^ 2 +
    4 * patch.coefficientError index * Data.Gaussian.Norm.Basic.normSq (parent.edge.point covered.fraction -
      parent.edge.point 0)
  /-- The cached primitive and source samples differ within the retained squared-norm allowance. -/ close :
    Data.Gaussian.Norm.Basic.normSq (value - source) ≤ error

constructive_injectivity Prepared

namespace Prepared

/-- Both the inverse polynomial and the actual covered prefix are acquired internally from the attached occurrence. No
successful scan, exact root or caller endpoint-containment certificate is required. -/
@[expose] def build (patch : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch parent boundary
  attached count) (inverseTarget : Fraction.Rational) (positive : 0 < inverseTarget) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.Prepared patch inverseTarget := by
  let index := patch.patch.requestIndex inverseTarget
  let model := PrimitiveModel.ofIndex patch.patch index
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))
  let covered := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.CoveredPrefix.build patch
  let movement := Data.Gaussian.Norm.Basic.normSq (parent.edge.point covered.fraction - parent.edge.point 0)
  exact
    { index := index
      inverse_accurate := patch.patch.requestIndex_accurate inverseTarget positive
      model := model
      covered := covered
      value := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.increment model
        covered.fraction
      value_eq := rfl
      source := (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.prefixCell parent
        covered.fraction).integralSample
      source_eq := rfl
      error := (4 * model.primitive.remainderBound + 2 * Data.Gaussian.Norm.Basic.normSq parent.center.value) *
        movement ^ 2 +
        4 * patch.coefficientError index * movement
      error_eq := rfl
      close := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.increment_error model
        covered.fraction ⟨covered.positive.le, covered.upper⟩ covered.finish_inside }

end Prepared
end Patch

/-- The same primitive also compares directly with the cached reciprocal owner reading. Its numerical readback allowance
is paid without reacquiring either the owner or the observation. -/
theorem reading_increment_error {target : Fraction.Rational}
    (reading : PreparedReciprocalSamples.Reading parent boundary target)
    {patch : Patch parent boundary reading.1 count}
      {index : Nat}
    (model : InverseRootPrimitive.PrimitiveModel patch.patch index (PreparedPrimitiveSamples.differentialNumerator
      (HyperellipticReciprocal.reversedDifferential differential)))
    (positive : 0 < target) (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (finishInside : patch.patch.box.Contains (parent.edge.point fraction)⁻¹) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.increment model fraction -
      ((parent.edge.point fraction)⁻¹ - (parent.edge.point 0)⁻¹) * reading.2.value) ≤
      4 * model.primitive.remainderBound * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
        parent.edge.point 0) ^ 2 +
        (4 * patch.coefficientError index + 2 * coefficientAllowance parent target) *
          Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction - parent.edge.point 0) := by
  let ideal := prefixSample parent boundary fraction
    inside
  let delta := (parent.edge.point fraction)⁻¹ - (parent.edge.point 0)⁻¹
  have allowanceNonnegative : 0 ≤ coefficientAllowance parent target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg positive.le (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct _) parent.edge.modelErrorAllowance_positive.le))
  have readback : Data.Gaussian.Norm.Basic.normSq (ideal.sample - delta * reading.2.value) ≤
      coefficientAllowance parent target * Data.Gaussian.Norm.Basic.normSq (parent.edge.point fraction -
        parent.edge.point 0) := by
    have identity : ideal.sample - delta * reading.2.value = delta * (ideal.coefficient - reading.2.value) := by
      rw [ideal.sample_eq, ideal.start_eq, ideal.finish_eq]
      change delta * ideal.coefficient - delta * reading.2.value = _
      ring1
    have close : Data.Gaussian.Norm.Basic.normSq (ideal.coefficient - reading.2.value) ≤ coefficientAllowance
      parent target := by
      rw [show ideal.coefficient - reading.2.value = -(reading.2.value - ideal.coefficient) by ring1,
        Data.Gaussian.Norm.Basic.normSq_neg]
      exact reading.2.close
    rw [identity, Data.Gaussian.Norm.Basic.normSq_mul, Fraction.Field.mul_comm]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct close (Data.Gaussian.Norm.Basic.normSq_nonneg
      _)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (PreparedReciprocalSamples.inverse_movement_between (boundary.point parent.edge.baseInside) (boundary.point
          inside))
        allowanceNonnegative)
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.increment model fraction) ideal.sample
    _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.ideal_increment_error model
        fraction inside finishInside) readback) (by decide)).trans_eq (by ring1))

/-- Consume a reciprocal reading already retained by the period-segment bank. In particular, preparing its primitive
does not attach another owner or choose another sheet. -/
@[expose] def prepareReading {target : Fraction.Rational} (reading : PreparedReciprocalSamples.Reading parent boundary
  target)
    (inverseTarget : Fraction.Rational) (positive : 0 < inverseTarget) :
    (patch : Patch parent boundary reading.1 genus)
      × Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.Prepared patch inverseTarget :=
  let patch := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.build reading.1 genus
  ⟨patch, Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives.Patch.Prepared.build patch inverseTarget
    positive⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalPrimitives
