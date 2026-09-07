import CCL.Riemann.PreparedDifferentialModels
import CCL.Riemann.FiniteQuotientVariation

/-!
# Shrinking constant models on prepared hyperelliptic cells

A prepared edge keeps every later square-root candidate inside one explicitly
small source box.  Combining that finite fact with the rational power and
quotient estimates produces a constant coefficient model whose allowance is
linear in the squared edge displacement and the requested root-box diameter.
-/

namespace CCL.Riemann.PreparedConstantModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev StepRequest := CCL.Riemann.PreparedSheetContinuation.StepRequest
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed

private theorem sixteen_nonnegative :
    (0 : Coordinate) <= 16 := by decide

private theorem four_le_sixteen :
    (4 : Coordinate) <= 16 := by decide

private theorem nine_le_sixteen :
    (9 : Coordinate) <= 16 := by decide

private theorem fourteen_le_sixteen :
    (14 : Coordinate) <= 16 := by decide

/-- All finite data for one accepted, diameter-prepared integration edge. -/
structure PreparedEdge {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  ambient : Box
  start : Gaussian
  finish : Gaussian
  segment : ClearSegment curve.polynomial ambient start finish
  within : segment.WithinAmbient
  left : Endpoint
  owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))
  request : StepRequest
  cached : CCL.Riemann.PreparedSheetContinuation.CachedSource segment left
    owner request
  ordered : left.parameter <= request.endpoint.parameter
  small : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared segment left owner
        request).track.initial.clearance.bound
  sheet : Fin 2

namespace PreparedEdge

theorem baseInside {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (_prepared : PreparedEdge curve differential) :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

def localSegment {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :=
  CCL.Riemann.PreparedDifferentialModels.edge curve prepared.segment
    prepared.within prepared.left prepared.request

def point {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate) :
    Gaussian :=
  prepared.localSegment.pointAt fraction

@[simp] theorem point_zero_eq_source {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.point 0 =
      prepared.segment.pointAt prepared.left.parameter := by
  unfold point localSegment CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 0).symm

def sheetValue {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :=
  CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached curve differential
    prepared.segment prepared.within prepared.left prepared.owner
      prepared.request prepared.cached prepared.ordered prepared.small
        prepared.sheet fraction inside

def coefficient {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) : CoherentNamed :=
  CCL.Riemann.PreparedDifferentialModels.coefficientAtCached curve differential
    prepared.segment prepared.within prepared.left prepared.owner
      prepared.request prepared.cached prepared.ordered prepared.small
        prepared.sheet fraction inside

/-- Productive root name queried at one local parameter of this prepared
integration edge. -/
@[irreducible] def rootName {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveTransducer.Named :=
  (CCL.Riemann.PreparedDifferentialModels.rootAtCached curve prepared.segment
    prepared.within prepared.left prepared.owner prepared.request
      prepared.cached prepared.ordered prepared.small fraction inside).value.name

/-- Productive root name of the diameter-prepared source owner. -/
@[irreducible] def preparedRootName {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.ProgressiveTransducer.Named :=
  CCL.Riemann.PreparedSheetContinuation.preparedRootName prepared.segment
    prepared.left prepared.owner prepared.request

/-- Productive root name at the transported right endpoint, before its finite
reconditioning reset. -/
@[irreducible] def transportedRootName {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.ProgressiveTransducer.Named :=
  CCL.Riemann.PreparedSheetContinuation.transportedRootName prepared.segment
    prepared.within prepared.left prepared.owner prepared.request prepared.small

/-- The direct point-query owner underlying `rootName`. -/
def directQueryOwner {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (curve.polynomial.eval (prepared.segment.pointAt
      (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
        prepared.request fraction))) :=
  CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport
    prepared.cached.preparedOwner
      (prepared.segment.pointAt_eval_ne_zero
        (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside))
      (by
        rw [prepared.cached.preparedOwner_eq]
        exact CCL.Riemann.PreparedSheetContinuation.pointNormSmall
          prepared.segment prepared.within prepared.left prepared.owner
            prepared.request prepared.ordered prepared.small fraction inside)
      (CCL.Riemann.PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)

/-- The productive point-query name is exactly the root carried by its direct
query owner. -/
theorem rootName_eq_directQueryOwnerRootName {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    prepared.rootName fraction inside =
      CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (prepared.segment.pointAt_eval_ne_zero
          (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
            prepared.request fraction)
          (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside
            prepared.left prepared.request prepared.ordered fraction inside))
        (prepared.directQueryOwner fraction inside) := by
  unfold rootName directQueryOwner
    CCL.Riemann.PreparedDifferentialModels.rootAtCached
  rfl

/-- The diameter-prepared source occurrence and its local parameter-zero
query are the same operational square root.  This is the source-independent
half of `ownerRootEquivalent_baseQuery`; callers which already compare their
source owner to the cached prepared owner need not reintroduce the original
owner merely to reach the base query. -/
def preparedRootEquivalent_baseQuery {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.OperationalEquivalence.NamedEquivalent prepared.preparedRootName
      (prepared.rootName 0 prepared.baseInside) := by
  let source := CCL.Riemann.PreparedSheetContinuation.prepared
    prepared.segment prepared.left prepared.owner prepared.request
  have sameSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (curve.polynomial.eval
              (prepared.segment.pointAt prepared.left.parameter) -
            curve.polynomial.eval
              (prepared.segment.pointAt prepared.left.parameter)) <
        source.track.initial.clearance.bound := by
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
    exact source.track.initial.clearance.positive
  have preparedToGeneric :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_advance_same
      (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
        prepared.left.inside) source sameSmall
  have genericToDirect :=
    CCL.Riemann.PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
      source
      (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
        prepared.left.inside)
      sameSmall
      (CCL.Riemann.PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)
  have equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
    preparedToGeneric genericToDirect
  unfold PreparedEdge.preparedRootName PreparedEdge.rootName
  rw [CCL.Riemann.PreparedDifferentialModels.rootAtCached_zero_name_eq_zeroMoveRootName]
  unfold CCL.Riemann.PreparedSheetContinuation.preparedRootName
    CCL.Riemann.PreparedSheetContinuation.zeroMoveRootName
  exact equivalent

/-- The inherited owner and the local parameter-zero point query name the same
source occurrence. -/
def ownerRootEquivalent_baseQuery {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
          prepared.left.inside) prepared.owner)
      (prepared.rootName 0 prepared.baseInside) := by
  unfold rootName
  have sourceToPrepared :=
    CCL.Riemann.PreparedSheetContinuation.sourceRootEquivalent
      prepared.segment prepared.left prepared.owner prepared.request
  let source := prepared.cached.preparedOwner
  let sourceNonzero := prepared.segment.pointAt_eval_ne_zero
    prepared.left.parameter prepared.left.inside
  have sourceToCached : CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.owner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        source) := by
    change CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.owner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.cached.preparedOwner)
    rw [prepared.cached.preparedOwner_eq]
    exact sourceToPrepared
  let moveSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter) -
        curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter)) <
        source.track.initial.clearance.bound := by
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter) -
        curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter)) <
        prepared.cached.preparedOwner.track.initial.clearance.bound
    rw [prepared.cached.preparedOwner_eq]
    simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
      (CCL.Riemann.PreparedSheetContinuation.pointNormSmall prepared.segment
        prepared.within prepared.left prepared.owner prepared.request
          prepared.ordered prepared.small 0 prepared.baseInside)
  have preparedToGenericZero :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_advance_same
      sourceNonzero source moveSmall
  have genericToDirectZero :=
    CCL.Riemann.PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
      source sourceNonzero moveSmall
      (CCL.Riemann.PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)
  have preparedToZero := CCL.OperationalEquivalence.NamedEquivalent.trans
    preparedToGenericZero genericToDirectZero
  have sourceToZero := CCL.OperationalEquivalence.NamedEquivalent.trans
    sourceToCached preparedToZero
  unfold CCL.Riemann.PreparedDifferentialModels.rootAtCached
  convert sourceToZero using 1
  apply
    CCL.Riemann.PreparedSheetContinuation.reservedTransportRootName_proof_irrel

/-- Operationally equal point-query roots at the same displayed rational
point induce operationally equal differential coefficients.  This separates
the sheet-occurrence obligation in a geometric refinement from all later
coefficient-center and allowance calculations. -/
def coefficientEquivalent_of_rootEquivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (point_eq : parent.point fraction = child.point 0)
    (rootEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.rootName fraction inside)
        (child.rootName 0 child.baseInside)) :
    CCL.OperationalEquivalence.NamedEquivalent
      (parent.coefficient fraction inside).name
      (child.coefficient 0 child.baseInside).name := by
  let parentRoot := CCL.Riemann.PreparedDifferentialModels.rootAtCached curve
    parent.segment parent.within parent.left parent.owner parent.request
      parent.cached parent.ordered parent.small fraction inside
  let childRoot := CCL.Riemann.PreparedDifferentialModels.rootAtCached curve
    child.segment child.within child.left child.owner child.request
      child.cached child.ordered child.small 0 child.baseInside
  have roots : CCL.OperationalEquivalence.NamedEquivalent
      parentRoot.value.name childRoot.value.name := by
    unfold rootName at rootEquivalent
    simpa only [parentRoot, childRoot] using rootEquivalent
  have coefficients := differentialValue_respects_sheet differential
    (child.point 0) parentRoot.value childRoot.value parentRoot.apart
      childRoot.apart roots
  unfold coefficient
    CCL.Riemann.PreparedDifferentialModels.coefficientAtCached
  change CCL.OperationalEquivalence.NamedEquivalent
    (differentialValue differential (parent.point fraction)
      parentRoot.value parentRoot.apart).name
    (differentialValue differential (child.point 0)
      childRoot.value childRoot.apart).name
  rw [point_eq]
  exact coefficients

/-- Squared displacement of the complete local edge. -/
def pointMovement {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
    (prepared.point 1 - prepared.point 0)

/-- The actual squared diagonal of the prepared root source cached while the
edge was accepted.  This is the sharp finite root-variation datum carried by
the edge; using the cache avoids rerunning preparation during model queries. -/
def preparedRootDiameter {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.cached.preparedOwner.track.initial.box.diagonalSq

theorem preparedRootDiameter_eq_canonical {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootDiameter =
      (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner
        prepared.request).track.initial.box.diagonalSq := by
  unfold preparedRootDiameter
  rw [prepared.cached.preparedOwner_eq]

theorem preparedRootDiameter_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.preparedRootDiameter := by
  exact CCL.Riemann.CoherentRoot.scale_positive
    prepared.cached.preparedOwner.track

theorem preparedRootDiameter_lt_requested {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootDiameter < prepared.request.rootDiameter := by
  rw [prepared.preparedRootDiameter_eq_canonical]
  exact CCL.Riemann.PreparedSheetContinuation.prepared_diagonal_lt
    prepared.segment prepared.left prepared.owner prepared.request

/-- Squared distance of one closed rational interval from zero.  Intervals
crossing zero contribute the conservative endpoint `0`.  This definition is
kept before the constant-model error bound so that the already cached
prepared-owner box can sharpen its denominator floor. -/
def intervalNormSqLower (lower upper : Coordinate) : Coordinate :=
  if _lowerNonnegative : 0 <= lower then lower ^ 2
  else if _upperNonpositive : upper <= 0 then upper ^ 2
  else 0

theorem intervalNormSqLower_nonnegative (lower upper : Coordinate) :
    0 <= intervalNormSqLower lower upper := by
  unfold intervalNormSqLower
  split <;> rename_i first
  · exact RFAP.ConstructiveFraction.sq_nonneg_direct lower
  · split <;> rename_i second
    · exact RFAP.ConstructiveFraction.sq_nonneg_direct upper
    · exact le_rfl

/-- The interval distance-to-zero endpoint bounds the square of every member
of that interval. -/
theorem intervalNormSqLower_le {lower value upper : Coordinate}
    (lowerLe : lower <= value) (valueLe : value <= upper) :
    intervalNormSqLower lower upper <= value ^ 2 := by
  unfold intervalNormSqLower
  split
  · rename_i lowerNonnegative
    exact RFAP.ConstructiveFraction.pow_le_pow_direct lowerNonnegative lowerLe 2
  · rename_i lowerNegative
    split
    · rename_i upperNonpositive
      have negOrder : -upper <= -value :=
        RFAP.ConstructiveFraction.neg_le_neg_direct valueLe
      have negUpperNonnegative : 0 <= -upper :=
        neg_nonneg.mpr upperNonpositive
      have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
        negUpperNonnegative negOrder 2
      simpa only [show (-upper) ^ 2 = upper ^ 2 by ring1,
        show (-value) ^ 2 = value ^ 2 by ring1] using squares
    · exact RFAP.ConstructiveFraction.sq_nonneg_direct value

/-- Coordinatewise squared distance of a box from the origin. -/
def boxNormSqLower (box : Box) : Coordinate :=
  intervalNormSqLower box.xLower box.xUpper +
    intervalNormSqLower box.yLower box.yUpper

theorem boxNormSqLower_nonnegative (box : Box) :
    0 <= boxNormSqLower box :=
  add_nonneg
    (intervalNormSqLower_nonnegative box.xLower box.xUpper)
    (intervalNormSqLower_nonnegative box.yLower box.yUpper)

theorem boxNormSqLower_le {box : Box} {value : Gaussian}
    (inside : box.Contains value) :
    boxNormSqLower box <=
      RFAP.ConstructiveGaussian.Gaussian.normSq value := by
  unfold boxNormSqLower RFAP.ConstructiveGaussian.Gaussian.normSq
  exact add_le_add
    (intervalNormSqLower_le inside.1 inside.2.1)
    (intervalNormSqLower_le inside.2.2.1 inside.2.2.2)

/-- Best denominator floor available without another root query.  The
segment theorem supplies unconditional positivity, while the retained
prepared-owner box is usually much sharper near a branch point. -/
def preparedDenominatorLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  max
    (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
      prepared.segment)
    (boxNormSqLower prepared.cached.preparedOwner.track.initial.box)

theorem preparedDenominatorLower_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.preparedDenominatorLower :=
  (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
    prepared.segment).trans_le (le_max_left _ _)

/-- The direct quotient-variation estimate on the complete edge. -/
def rawVariation {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  CCL.Riemann.FiniteQuotientVariation.quotientBound
    (CCL.Riemann.FiniteQuotientVariation.powerSlope
      prepared.ambient.normSqBound differential.exponent)
    (prepared.ambient.normSqBound ^ differential.exponent)
    (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSqBound
    prepared.preparedDenominatorLower
    prepared.pointMovement prepared.preparedRootDiameter

/-- A strictly positive error allowance.  The extra actual root-diameter
summand is quantitatively harmless and makes refinement requests positive
even on a stationary base edge. -/
def modelErrorAllowance {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.rawVariation + prepared.preparedRootDiameter

theorem rawVariation_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.rawVariation := by
  apply CCL.Riemann.FiniteQuotientVariation.quotientBound_nonnegative
  · exact CCL.Riemann.FiniteQuotientVariation.powerSlope_nonnegative
      prepared.ambient.normSqBound_nonneg differential.exponent
  · exact RFAP.ConstructiveFraction.pow_nonneg_direct
      prepared.ambient.normSqBound_nonneg differential.exponent
  · exact (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSqBound_nonneg
  · exact
      prepared.preparedDenominatorLower_positive.le
  · exact RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  · exact prepared.preparedRootDiameter_positive.le

theorem modelErrorAllowance_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
  0 < prepared.modelErrorAllowance :=
  add_pos_of_nonneg_of_pos prepared.rawVariation_nonnegative
    prepared.preparedRootDiameter_positive

/-- Segment-wide coefficient of squared base-point movement in the quotient
model error.  The root ambient and sampled denominator floor are independent
of the selected owner and local parameter. -/
def pointErrorCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish) :
    Coordinate :=
  (2 *
      (CCL.Riemann.FiniteQuotientVariation.powerSlope ambient.normSqBound
          differential.exponent *
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
          segment).normSqBound)) /
    (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower segment *
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower segment)

/-- Segment-wide coefficient of the actual prepared root diameter, including
the strictly positive extra summand in `modelErrorAllowance`. -/
def rootErrorCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish) :
    Coordinate :=
  (2 * ambient.normSqBound ^ differential.exponent) /
      (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower segment *
        CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower segment) +
    1

/-- Owner-specific movement coefficient using the retained prepared box. -/
def preparedPointErrorCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  (2 *
      (CCL.Riemann.FiniteQuotientVariation.powerSlope
          prepared.ambient.normSqBound differential.exponent *
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound)) /
    (prepared.preparedDenominatorLower * prepared.preparedDenominatorLower)

/-- Owner-specific root-motion coefficient, including the positive reserve. -/
def preparedRootErrorCoefficient {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  (2 * prepared.ambient.normSqBound ^ differential.exponent) /
      (prepared.preparedDenominatorLower * prepared.preparedDenominatorLower) +
    1

theorem preparedRootErrorCoefficient_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.preparedRootErrorCoefficient := by
  unfold preparedRootErrorCoefficient
  exact add_nonneg
    (RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        prepared.preparedDenominatorLower_positive.le
        prepared.preparedDenominatorLower_positive.le))
    (by decide)

theorem pointErrorCoefficient_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish) :
    0 <= pointErrorCoefficient differential segment := by
  unfold pointErrorCoefficient
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.Riemann.FiniteQuotientVariation.powerSlope_nonnegative
          ambient.normSqBound_nonneg differential.exponent)
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
          segment).normSqBound_nonneg))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
        segment).le
      (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
        segment).le)

theorem rootErrorCoefficient_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment curve.polynomial ambient start finish) :
    0 <= rootErrorCoefficient differential segment := by
  unfold rootErrorCoefficient
  exact add_nonneg
    (RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          ambient.normSqBound_nonneg differential.exponent))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
          segment).le
        (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
          segment).le))
    (by decide)

theorem preparedPointErrorCoefficient_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedPointErrorCoefficient <=
      pointErrorCoefficient differential prepared.segment := by
  apply CCL.Riemann.FiniteQuotientVariation.scaled_div_square_antitone
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (CCL.Riemann.FiniteQuotientVariation.powerSlope_nonnegative
          prepared.ambient.normSqBound_nonneg differential.exponent)
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound_nonneg)
  · exact
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
        prepared.segment
  · exact le_max_left _ _

theorem preparedRootErrorCoefficient_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootErrorCoefficient <=
      rootErrorCoefficient differential prepared.segment := by
  unfold preparedRootErrorCoefficient rootErrorCoefficient
  apply add_le_add
  · apply CCL.Riemann.FiniteQuotientVariation.scaled_div_square_antitone
    · exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent)
    · exact
        CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_positive
          prepared.segment
    · exact le_max_left _ _
  · exact le_rfl

/-- Exact owner-specific two-term presentation of the prepared error. -/
theorem modelErrorAllowance_eq_preparedLinear {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.modelErrorAllowance =
      prepared.preparedPointErrorCoefficient * prepared.pointMovement +
        prepared.preparedRootErrorCoefficient *
          prepared.preparedRootDiameter := by
  simpa only [modelErrorAllowance, rawVariation,
    preparedPointErrorCoefficient, preparedRootErrorCoefficient] using
    CCL.Riemann.FiniteQuotientVariation.quotientBound_add_rootMovement_eq_linear
      (CCL.Riemann.FiniteQuotientVariation.powerSlope
        prepared.ambient.normSqBound differential.exponent)
      (prepared.ambient.normSqBound ^ differential.exponent)
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        prepared.segment).normSqBound
      prepared.preparedDenominatorLower prepared.pointMovement
        prepared.preparedRootDiameter

/-- The cached-box denominator can only improve the older segment-wide
linear error estimate.  Keeping the segment coefficients as an upper bound
preserves the owner-independent subdivision scheduler. -/
theorem modelErrorAllowance_le_linear {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.modelErrorAllowance <=
      pointErrorCoefficient differential prepared.segment *
          prepared.pointMovement +
        rootErrorCoefficient differential prepared.segment *
          prepared.preparedRootDiameter := by
  rw [prepared.modelErrorAllowance_eq_preparedLinear]
  exact add_le_add
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      prepared.preparedPointErrorCoefficient_le
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _))
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      prepared.preparedRootErrorCoefficient_le
      prepared.preparedRootDiameter_positive.le)

/-- Independent movement and root-diameter targets preserve the exact
two-term structure of the prepared quotient estimate. -/
theorem modelErrorAllowance_le_of_separate_targets {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (pointTarget rootTarget : Coordinate)
    (pointLe : prepared.pointMovement <= pointTarget)
    (rootLe : prepared.preparedRootDiameter <= rootTarget) :
    prepared.modelErrorAllowance <=
      pointErrorCoefficient differential prepared.segment * pointTarget +
        rootErrorCoefficient differential prepared.segment * rootTarget := by
  exact prepared.modelErrorAllowance_le_linear.trans
    (add_le_add
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct pointLe
        (pointErrorCoefficient_nonnegative differential prepared.segment))
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct rootLe
        (rootErrorCoefficient_nonnegative differential prepared.segment)))

/-- Common movement and diameter targets give one explicit segment-wide
model-error target. -/
theorem modelErrorAllowance_le_of_targets {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (target : Coordinate)
    (pointTarget : prepared.pointMovement <= target)
    (rootTarget : prepared.request.rootDiameter <= target) :
    prepared.modelErrorAllowance <=
      (pointErrorCoefficient differential prepared.segment +
        rootErrorCoefficient differential prepared.segment) * target := by
  calc
    prepared.modelErrorAllowance <=
        pointErrorCoefficient differential prepared.segment * target +
          rootErrorCoefficient differential prepared.segment * target :=
      prepared.modelErrorAllowance_le_of_separate_targets target target
        pointTarget (prepared.preparedRootDiameter_lt_requested.le.trans
          rootTarget)
    _ = (pointErrorCoefficient differential prepared.segment +
          rootErrorCoefficient differential prepared.segment) * target := by
      ring1

def readingTarget {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.modelErrorAllowance / 8

theorem readingTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.readingTarget :=
  RFAP.ConstructiveFraction.div_pos_direct
    prepared.modelErrorAllowance_positive (by decide)

def readingState {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.State :=
  (prepared.coefficient fraction inside).name.process.refine
    (prepared.coefficient fraction inside).name.state prepared.readingTarget
      prepared.readingTarget_positive

def reading {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) : Gaussian :=
  ((prepared.coefficient fraction inside).name.process.witness
    (prepared.readingState fraction inside)).val

theorem reading_possible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.Possible
      (prepared.readingState fraction inside)
        (prepared.reading fraction inside) :=
  ((prepared.coefficient fraction inside).name.process.witness
    (prepared.readingState fraction inside)).property

theorem reading_radius_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    ((prepared.coefficient fraction inside).name.process.ball
      (prepared.readingState fraction inside)).radiusSq <
        prepared.readingTarget :=
  (prepared.coefficient fraction inside).name.process.accurate
    (prepared.coefficient fraction inside).name.state prepared.readingTarget
      prepared.readingTarget_positive

def baseReading {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  prepared.reading 0 prepared.baseInside

/-- A later finite state of the base-point differential process, together
with the constructive persistence evidence needed to compare its witness
with the originally prepared base reading. -/
structure CenterState {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) where
  state : (prepared.coefficient 0 prepared.baseInside).name.process.State
  cachedValue : Thunk Gaussian
  cachedValue_possible :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      state cachedValue.get
  cachedDenominator : Thunk Gaussian
  cachedDenominator_possible :
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
      state.2 cachedDenominator.get
  cachedValue_eq_power_div_denominator :
    cachedValue.get =
      prepared.point 0 ^ differential.exponent / cachedDenominator.get
  persists : forall {value : Gaussian},
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
        state value ->
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
        (prepared.readingState 0 prepared.baseInside) value
  radius_lt :
    ((prepared.coefficient 0 prepared.baseInside).name.process.ball
      state).radiusSq < prepared.readingTarget

namespace CenterState

/-- Call-by-need cache for the rational witness selected at one persisted
coefficient state.  Repeated model projections reuse the same finite
division instead of reconstructing it from the stored state. -/
def valueThunk {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State) :
    Thunk Gaussian :=
  ⟨fun _ =>
    ((prepared.coefficient 0 prepared.baseInside).name.process.witness
      state).val⟩

/-- Call-by-need cache for the square-root candidate selected alongside one
coefficient witness.  Keeping the two values together gives a static
certificate generator a finite injection boundary without changing the
canonical constructors below. -/
def denominatorThunk {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State) :
    Thunk Gaussian :=
  ⟨fun _ =>
    ((prepared.sheetValue 0 prepared.baseInside).value.name.process.witness
      state.2).val⟩

/-- Construct a persisted centre from the canonical finite witnesses at an
already selected state.  All executable values are cached once, while their
`Possible` certificates—not definitional equality to a particular witness
selection—are the downstream specification. -/
def ofState {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared := by
  let cachedValue := valueThunk prepared state
  let cachedDenominator := denominatorThunk prepared state
  exact
    { state := state
      cachedValue := cachedValue
      cachedValue_possible := by
        change (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state
            ((prepared.coefficient 0 prepared.baseInside).name.process.witness
              state).val
        exact ((prepared.coefficient 0
          prepared.baseInside).name.process.witness state).property
      cachedDenominator := cachedDenominator
      cachedDenominator_possible := by
        change
          (prepared.sheetValue 0
            prepared.baseInside).value.name.process.Possible state.2
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val
        exact ((prepared.sheetValue 0
          prepared.baseInside).value.name.process.witness state.2).property
      cachedValue_eq_power_div_denominator := by
        change
          ((namedPower
            (CCL.ProgressiveCoherence.CoherentNamed.exact
              (prepared.point 0)) differential.exponent).name.process.witness
                state.1).val /
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val =
            prepared.point 0 ^ differential.exponent /
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val
        rw [namedPower_exact_possible_eq (prepared.point 0)
          differential.exponent state.1
            ((namedPower
              (CCL.ProgressiveCoherence.CoherentNamed.exact
                (prepared.point 0)) differential.exponent).name.process.witness
                  state.1).property]
      persists := persists
      radius_lt := radius_lt }

/-- Build a persisted centre from one explicitly certified rational
coefficient and square-root candidate.  Both are untrusted finite data:
Lean checks box membership for the denominator and the exact quotient
equation for the coefficient before either cached value reaches a model. -/
def ofCertified {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (value : Gaussian)
    (denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared := by
  let numerator := namedPower
    (CCL.ProgressiveCoherence.CoherentNamed.exact (prepared.point 0))
      differential.exponent
  let numeratorWitness := numerator.name.process.witness state.1
  have numeratorEq : numeratorWitness.val =
      prepared.point 0 ^ differential.exponent :=
    namedPower_exact_possible_eq (prepared.point 0) differential.exponent
      state.1 numeratorWitness.property
  exact
    { state := state
      cachedValue := ⟨fun _ => value⟩
      cachedValue_possible := by
        change ∃ x y : Gaussian,
          numerator.name.process.Possible state.1 x ∧
            (prepared.sheetValue 0
              prepared.baseInside).value.name.process.Possible state.2 y ∧
              value = x / y
        exact ⟨numeratorWitness.val, denominator, numeratorWitness.property,
          denominatorPossible, by rw [numeratorEq, valueEq]⟩
      cachedDenominator := ⟨fun _ => denominator⟩
      cachedDenominator_possible := denominatorPossible
      cachedValue_eq_power_div_denominator := valueEq
      persists := persists
      radius_lt := radius_lt }

/-- Convenience constructor when only the rational denominator is supplied.
It remains useful for hand-written certificates; generated certificates can
use `ofCertified` to avoid recomputing the quotient in compiled clients. -/
def ofCertifiedDenominator {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        state.2 denominator)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared :=
  ofCertified prepared state
    (prepared.point 0 ^ differential.exponent / denominator) denominator
      denominatorPossible rfl persists radius_lt

/-- Replace only the two cached rational readings of an existing persisted
centre.  Its state, persistence theorem, and accuracy proof are retained
verbatim; the replacement is accepted only after its denominator membership
and exact quotient equation have been certified. -/
def recache {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    CenterState prepared :=
  ofCertified prepared center.state value denominator denominatorPossible
    valueEq center.persists center.radius_lt

@[simp] theorem recache_state {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).state =
      center.state := rfl

/-- Follow the ordinary nested finite sampling path from the already
prepared base-reading state. -/
def atIndex {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (index : Nat)
    (accurate : CCL.ProgressiveSampling.refinementTarget index <
      prepared.readingTarget) :
    CenterState prepared := by
  let state := CCL.ProgressiveSampling.stateAt
    (prepared.coefficient 0 prepared.baseInside).name.process
      (prepared.readingState 0 prepared.baseInside) index
  exact ofState prepared state
    (by
        intro value possible
        exact CCL.ProgressiveSampling.stateAt_possible_at_start
          (prepared.coefficient 0 prepared.baseInside).name.process
            (prepared.readingState 0 prepared.baseInside) index possible)
    ((CCL.ProgressiveSampling.stateAt_accurate
      (prepared.coefficient 0 prepared.baseInside).name.process
        (prepared.readingState 0 prepared.baseInside) index).trans accurate)

/-- First nested sampling index whose generic process enclosure is smaller
than the prepared model's base-reading target. -/
def canonicalIndex {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow 1 0 prepared.readingTarget

/-- Canonical initial centre at the already accurate prepared base reading.
The preparation request has proved this state smaller than `readingTarget`, so
running a second generic sampling search here would only duplicate the same
finite coefficient refinement on every subdivision edge. -/
def canonical {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : CenterState prepared := by
  let state := prepared.readingState 0 prepared.baseInside
  exact ofState prepared state (fun possible => possible)
    (prepared.reading_radius_lt 0 prepared.baseInside)

/-- The displayed rational coefficient selected at the centre state. -/
def value {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Gaussian :=
  center.cachedValue.get

theorem value_possible {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      center.state center.value := by
  exact center.cachedValue_possible

theorem value_possible_at_readingState {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      (prepared.readingState 0 prepared.baseInside) center.value :=
  center.persists center.value_possible

/-- The actual square-root candidate used by a persisted coefficient centre.
Keeping this denominator as data exposes the owner-box geometry behind a
finite `x^k/y` reading without rerunning the quotient process. -/
def denominator {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Gaussian :=
  center.cachedDenominator.get

/-- The retained denominator is an admitted candidate of the exact sheet
process at the denominator component of the coefficient state. -/
theorem denominator_possible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
      center.state.2 center.denominator :=
  center.cachedDenominator_possible

/-- A persisted coefficient centre is literally the displayed rational power
divided by its retained square-root candidate. -/
theorem value_eq_power_div_denominator {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.value =
      prepared.point 0 ^ differential.exponent / center.denominator := by
  exact center.cachedValue_eq_power_div_denominator

@[simp] theorem recache_value {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).value =
      value := rfl

@[simp] theorem recache_denominator {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).denominator =
      denominator := rfl

/-- For the genus-one unit differential `dx/y`, the retained coefficient
centre is exactly the reciprocal of its retained sheet candidate. -/
theorem value_eq_one_div_denominator_of_exponent_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    center.value = 1 / center.denominator := by
  rw [center.value_eq_power_div_denominator, exponentZero, pow_zero]

/-- Every retained denominator remains inside the one prepared quadratic
owner box attached to its accepted edge.  This is the finite bridge from
coefficient sampling to oriented box/sector estimates. -/
theorem denominator_in_prepared_box {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner prepared.request).track.initial.box.Contains
        center.denominator := by
  exact
    CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached_candidate_in_prepared_box
      curve differential prepared.segment prepared.within prepared.left
        prepared.owner prepared.request prepared.cached prepared.ordered
          prepared.small prepared.sheet 0 prepared.baseInside center.state.2
            center.denominator_possible

/-- Cached form of `denominator_in_prepared_box`.  Executable lower-bound
queries should consume this statement so they reuse the owner saved when the
edge was accepted instead of rerunning the preparation procedure. -/
theorem denominator_in_cached_prepared_box {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    prepared.cached.preparedOwner.track.initial.box.Contains
      center.denominator := by
  rw [prepared.cached.preparedOwner_eq]
  exact center.denominator_in_prepared_box

/-- The process enclosure already computed at a retained coefficient state.
Unlike `denominator`, this is wholly rational certificate data and does not
select the process witness. -/
def denominatorBall {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : CCL.ArithmeticEnclosures.Ball :=
  (prepared.sheetValue 0 prepared.baseInside).value.name.process.ball
    center.state.2

theorem denominator_in_ball {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.denominatorBall.Contains center.denominator := by
  exact
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.possible_inside
      center.denominator_possible

/-- Fixed rational half-width used to turn a sufficiently accurate process
ball into a compact denominator-sector square. -/
def denominatorSectorRadius : Coordinate := 1 / 10

theorem denominatorSectorRadius_nonnegative :
    (0 : Coordinate) <= denominatorSectorRadius := by decide

/-- Use the retained process ball when its squared radius fits the fixed
sector square, and otherwise fall back to the total cached preparation box.
The branch is a finite rational comparison. -/
def denominatorProjectionBox {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Box :=
  let ball := center.denominatorBall
  if ball.radiusSq <= denominatorSectorRadius ^ 2 then
    RFAP.AffineWinding.centeredSquare ball.center
      denominatorSectorRadius denominatorSectorRadius_nonnegative
  else
    prepared.cached.preparedOwner.track.initial.box

/-- The selected compact projection box always contains the retained sheet
candidate.  In the tight branch this follows directly from the process-ball
squared-radius certificate; no square root or completed value is used. -/
theorem denominator_in_projection_box {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.denominatorProjectionBox.Contains center.denominator := by
  unfold denominatorProjectionBox
  dsimp only
  split
  · rename_i radiusSmall
    have distanceBound :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (center.denominator - center.denominatorBall.center) <=
          denominatorSectorRadius ^ 2 :=
      center.denominator_in_ball.trans radiusSmall
    have bounds := RFAP.AffineWinding.coordinate_bounds_of_normSq_le
      denominatorSectorRadius_nonnegative distanceBound
    have realLower : -denominatorSectorRadius <=
        center.denominator.re - center.denominatorBall.center.re := by
      simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_re] using bounds.1
    have realUpper :
        center.denominator.re - center.denominatorBall.center.re <=
          denominatorSectorRadius := by
      simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_re] using bounds.2.1
    have imaginaryLower : -denominatorSectorRadius <=
        center.denominator.im - center.denominatorBall.center.im := by
      simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_im] using bounds.2.2.1
    have imaginaryUpper :
        center.denominator.im - center.denominatorBall.center.im <=
          denominatorSectorRadius := by
      simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_im] using bounds.2.2.2
    exact
      ⟨by
        calc
          center.denominatorBall.center.re - denominatorSectorRadius =
              -denominatorSectorRadius + center.denominatorBall.center.re := by
                ring1
          _ <= (center.denominator.re -
                center.denominatorBall.center.re) +
              center.denominatorBall.center.re :=
            add_le_add_left realLower center.denominatorBall.center.re
          _ = center.denominator.re := by ring1,
        by
          calc
            center.denominator.re =
                (center.denominator.re - center.denominatorBall.center.re) +
                  center.denominatorBall.center.re := by ring1
            _ <= denominatorSectorRadius +
                center.denominatorBall.center.re :=
              add_le_add_left realUpper center.denominatorBall.center.re
            _ = center.denominatorBall.center.re +
                denominatorSectorRadius := by ring1,
        by
          calc
            center.denominatorBall.center.im - denominatorSectorRadius =
                -denominatorSectorRadius +
                  center.denominatorBall.center.im := by ring1
            _ <= (center.denominator.im -
                  center.denominatorBall.center.im) +
                center.denominatorBall.center.im :=
              add_le_add_left imaginaryLower center.denominatorBall.center.im
            _ = center.denominator.im := by ring1,
        by
          calc
            center.denominator.im =
                (center.denominator.im - center.denominatorBall.center.im) +
                  center.denominatorBall.center.im := by ring1
            _ <= denominatorSectorRadius +
                center.denominatorBall.center.im :=
              add_le_add_left imaginaryUpper center.denominatorBall.center.im
            _ = center.denominatorBall.center.im +
                denominatorSectorRadius := by ring1⟩
  · exact center.denominator_in_cached_prepared_box

/-- The real projection of a Gaussian displacement times a reciprocal is the
ordinary rational dot product divided by the denominator norm-square.  This
coordinate identity is the algebraic core of the later finite sector bounds. -/
theorem mul_one_div_re (displacement denominator : Gaussian) :
    (displacement * (1 / denominator)).re =
      (displacement.re * denominator.re +
        displacement.im * denominator.im) /
          RFAP.ConstructiveGaussian.Gaussian.normSq denominator := by
  have oneDiv : (1 / denominator : Gaussian) = denominator⁻¹ := by
    change 1 * denominator⁻¹ = denominator⁻¹
    exact RFAP.ConstructiveGaussian.Gaussian.one_mul _
  rw [oneDiv]
  rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq]
  change displacement.re *
          (denominator.re /
            RFAP.ConstructiveGaussian.Gaussian.normSq denominator) -
        displacement.im *
          (-denominator.im /
            RFAP.ConstructiveGaussian.Gaussian.normSq denominator) = _
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

/-- The rebased coherent coefficient name whose current witness is the
selected centre value. -/
def named {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : CCL.ProgressiveTransducer.Named :=
  { process := (prepared.coefficient 0 prepared.baseInside).name.process
    state := center.state }

/-- Recentring at any finitely persisted state preserves the operational
coefficient value. -/
def equivalent {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    CCL.OperationalEquivalence.NamedEquivalent
      (prepared.coefficient 0 prepared.baseInside).name center.named :=
  CCL.ProgressiveCoherence.CoherentNamed.rebaseEquivalent
    (prepared.coefficient 0 prepared.baseInside) center.state

/-- The base coefficient name restarted from its already accurate prepared
reading state. -/
def baseNamed {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.ProgressiveTransducer.Named :=
  { process := (prepared.coefficient 0 prepared.baseInside).name.process
    state := prepared.readingState 0 prepared.baseInside }

def baseEquivalent {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    CCL.OperationalEquivalence.NamedEquivalent
      (prepared.coefficient 0 prepared.baseInside).name
      (baseNamed prepared) :=
  CCL.ProgressiveCoherence.CoherentNamed.rebaseEquivalent
    (prepared.coefficient 0 prepared.baseInside)
      (prepared.readingState 0 prepared.baseInside)

end CenterState

/-! ## Finite box projection bounds -/

/-- Minimum of `coefficient * value` over one displayed rational interval.
The branch is an exact rational sign decision. -/
def signedCoordinateLower (coefficient lower upper : Coordinate) : Coordinate :=
  if 0 <= coefficient then coefficient * lower else coefficient * upper

/-- The selected signed endpoint is a lower bound for multiplication by any
value in the displayed interval. -/
theorem signedCoordinateLower_le (coefficient lower value upper : Coordinate)
    (lowerLe : lower <= value) (valueLe : value <= upper) :
    signedCoordinateLower coefficient lower upper <= coefficient * value := by
  by_cases nonnegative : 0 <= coefficient
  · rw [signedCoordinateLower, if_pos nonnegative]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      lowerLe nonnegative
  · rw [signedCoordinateLower, if_neg nonnegative]
    have nonpositive : coefficient <= 0 := le_of_not_ge nonnegative
    have negNonnegative : 0 <= -coefficient := neg_nonneg.mpr nonpositive
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      valueLe negNonnegative
    calc
      coefficient * upper = -((-coefficient) * upper) := by ring1
      _ <= -((-coefficient) * value) :=
        RFAP.ConstructiveFraction.neg_le_neg_direct scaled
      _ = coefficient * value := by ring1

/-- Exact lower endpoint of the rational dot product with any point of an
axis-aligned box. -/
def boxProjectionLower (box : Box) (displacement : Gaussian) : Coordinate :=
  signedCoordinateLower displacement.re box.xLower box.xUpper +
    signedCoordinateLower displacement.im box.yLower box.yUpper

/-- Every point of a rational box lies above its computed linear-projection
lower endpoint. -/
theorem boxProjectionLower_le {box : Box} {displacement value : Gaussian}
    (inside : box.Contains value) :
    boxProjectionLower box displacement <=
      displacement.re * value.re + displacement.im * value.im := by
  exact add_le_add
    (signedCoordinateLower_le displacement.re box.xLower value.re box.xUpper
      inside.1 inside.2.1)
    (signedCoordinateLower_le displacement.im box.yLower value.im box.yUpper
      inside.2.2.1 inside.2.2.2)

/-- A lower quotient bound that chooses the correct denominator endpoint from
the sign of its numerator.  This permits useful negative cell bounds as well
as positive sector certificates. -/
def signedQuotientLower (numerator denominatorLower denominatorUpper : Coordinate) :
    Coordinate :=
  if 0 <= numerator then numerator / denominatorUpper
  else numerator / denominatorLower

/-- The sign-selected quotient is below division by every positive
denominator in the displayed interval. -/
theorem signedQuotientLower_le (numerator denominatorLower denominator
    denominatorUpper : Coordinate) (denominatorLowerPositive : 0 < denominatorLower)
    (lowerLe : denominatorLower <= denominator)
    (upperLe : denominator <= denominatorUpper) :
    signedQuotientLower numerator denominatorLower denominatorUpper <=
      numerator / denominator := by
  by_cases numeratorNonnegative : 0 <= numerator
  · rw [signedQuotientLower, if_pos numeratorNonnegative]
    exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      numeratorNonnegative (denominatorLowerPositive.trans_le lowerLe) upperLe
  · rw [signedQuotientLower, if_neg numeratorNonnegative]
    have numeratorNonpositive : numerator <= 0 := le_of_not_ge numeratorNonnegative
    have negNumeratorNonnegative : 0 <= -numerator :=
      neg_nonneg.mpr numeratorNonpositive
    have positiveDivision :
        (-numerator) / denominator <=
          (-numerator) / denominatorLower :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        negNumeratorNonnegative denominatorLowerPositive lowerLe
    calc
      numerator / denominatorLower =
          -((-numerator) / denominatorLower) := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        ring1
      _ <= -((-numerator) / denominator) :=
        RFAP.ConstructiveFraction.neg_le_neg_direct positiveDivision
      _ = numerator / denominator := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        ring1

/-- Fixed dyadic grid for summable real lower certificates.  Rounding each
cell separately loses less than `2^-32` while preventing denominator growth
across long prepared paths. -/
def realLowerDyadicPrecision : Nat := 32

def realLowerDyadicScale : Coordinate :=
  (2 : Coordinate) ^ realLowerDyadicPrecision

/-- Greatest point on the fixed dyadic certificate grid below `source`. -/
def dyadicRealLower (source : Coordinate) : Coordinate :=
  RFAP.CanonicalFraction.fromInt
      (RFAP.ConstructiveFraction.floor (source * realLowerDyadicScale)) /
    realLowerDyadicScale

private theorem realLowerDyadicScale_positive :
    (0 : Coordinate) < realLowerDyadicScale := by
  unfold realLowerDyadicScale
  exact RFAP.ConstructiveFraction.pow_pos_direct (by decide)
    realLowerDyadicPrecision

/-- Downward dyadic rounding remains a certified lower endpoint for every
rational, including negative cell contributions. -/
theorem dyadicRealLower_le (source : Coordinate) :
    dyadicRealLower source <= source := by
  unfold dyadicRealLower
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    realLowerDyadicScale_positive).2
  have floorBound :=
    (RFAP.ConstructiveFraction.intCast_le_iff_floor
      (RFAP.ConstructiveFraction.floor (source * realLowerDyadicScale))
      (source * realLowerDyadicScale)).2 le_rfl
  rw [RFAP.CanonicalFraction.intCast_eq_fromInt] at floorBound
  exact floorBound

/-- Integer upper endpoint for the squared norm of every member of a box.
Using an integer here keeps the later sign-selected quotient inexpensive. -/
def boxNormSqCeil (box : Box) : Coordinate :=
  (RFAP.ConstructiveFraction.ceilNat box.normSqBound : Nat)

theorem normSqBound_le_boxNormSqCeil (box : Box) :
    box.normSqBound <= boxNormSqCeil box := by
  exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
    box.normSqBound_nonneg

/-- Unconditional dyadic denominator floor used by negative cell bounds.
It is the magnitude component of the existing segment denominator theorem,
so it avoids evaluating a pointwise square-root sample. -/
def cellDenominatorLower
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start
      finish) : Coordinate :=
  CCL.Riemann.PreparedDifferentialModels.magnitudeDenominatorLower segment

theorem cellDenominatorLower_positive
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start
      finish) :
    0 < cellDenominatorLower segment := by
  unfold cellDenominatorLower
    CCL.Riemann.PreparedDifferentialModels.magnitudeDenominatorLower
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.div_pos_direct
    (CCL.FiniteGeometric.dyadicSquareRadius_positive _) (by decide))
    (by decide)

/-- Best cheap denominator floor available from one prepared cell: the
segment-wide magnitude theorem keeps it strictly positive, while the cached
owner box usually supplies the sharper value. -/
def geometricDenominatorLower
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start
      finish) (box : Box) : Coordinate :=
  max (cellDenominatorLower segment) (boxNormSqLower box)

theorem geometricDenominatorLower_positive
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start
      finish) (box : Box) :
    0 < geometricDenominatorLower segment box :=
  (cellDenominatorLower_positive segment).trans_le (le_max_left _ _)

private theorem half_lt_self {target : Coordinate} (positive : 0 < target) :
    target / 2 < target := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    target = target * 1 := by ring1
    _ < target * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

private theorem twice_readingTarget_sum_eq_half {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) :
    2 * (prepared.readingTarget + prepared.readingTarget) =
      prepared.modelErrorAllowance / 2 := by
  unfold readingTarget
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (8 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (prepared.modelErrorAllowance / 8 +
        prepared.modelErrorAllowance / 8)) * 8 =
      2 * ((prepared.modelErrorAllowance / 8) * 8 +
        (prepared.modelErrorAllowance / 8) * 8) := by ring1
    _ = 2 * (prepared.modelErrorAllowance +
        prepared.modelErrorAllowance) := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 8 (by decide)]
    _ = prepared.modelErrorAllowance * 4 := by ring1
    _ = ((prepared.modelErrorAllowance / 2) * 2) * 4 := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = (prepared.modelErrorAllowance / 2) * 8 := by ring1

/-- A recached literal coefficient remains within the original local model
allowance of the centre whose state and accuracy evidence it retained. -/
theorem CenterState.recache_value_sub_value_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((center.recache value denominator denominatorPossible valueEq).value -
          center.value) < prepared.modelErrorAllowance := by
  let replacement :=
    center.recache value denominator denominatorPossible valueEq
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have replacementPossible : process.Possible center.state replacement.value := by
    exact replacement.value_possible
  have replacementInside : ball.Contains replacement.value :=
    process.possible_inside replacementPossible
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible
  have identity : replacement.value - center.value =
      (replacement.value - ball.center) + (ball.center - center.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have centerReverse :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - center.value) <= ball.radiusSq := by
    have reverse : ball.center - center.value =
        -(center.value - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact centerInside
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (replacement.value - center.value) < prepared.modelErrorAllowance
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (replacement.value - center.value) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((replacement.value - ball.center) +
          (ball.center - center.value)) := by rw [identity]
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add replacementInside centerReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide)
        (RFAP.ConstructiveFraction.add_lt_add_direct
          replacement.radius_lt center.radius_lt)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      half_lt_self prepared.modelErrorAllowance_positive

def CenterState.laterValue {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) : Gaussian :=
  CCL.ProgressiveSampling.witnessAt
    (prepared.coefficient 0 prepared.baseInside).name.process
      center.state index

theorem CenterState.laterValue_possible_at_state {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      center.state (center.laterValue index) :=
  CCL.ProgressiveSampling.witnessAt_possible_start
    (prepared.coefficient 0 prepared.baseInside).name.process
      center.state index

/-- Every later nested witness from a selected centre state remains within
one original prepared model-error allowance of that centre's current
witness. -/
theorem CenterState.laterValue_sub_value_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (center.laterValue index - center.value) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have laterInside : ball.Contains (center.laterValue index) :=
    process.possible_inside (center.laterValue_possible_at_state index)
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible
  have identity : center.laterValue index - center.value =
      (center.laterValue index - ball.center) +
        (ball.center - center.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have centerReverse :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - center.value) <= ball.radiusSq := by
    have reverse : ball.center - center.value =
        -(center.value - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact centerInside
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (center.laterValue index - center.value) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((center.laterValue index - ball.center) +
          (ball.center - center.value)) := by rw [identity]
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add laterInside centerReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide)
        (RFAP.ConstructiveFraction.add_lt_add_direct
          center.radius_lt center.radius_lt)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      half_lt_self prepared.modelErrorAllowance_positive

/-- A finite right-centre selection aligned with one already selected parent
centre.  The error bound consists of the requested operational comparison
and the explicitly bounded move from the parent's current witness to the
later witness used by that comparison. -/
structure CenterAlignment {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent) (target : Coordinate) where
  childCenter : CenterState child
  close :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (childCenter.value - parentCenter.value) <
      2 * (target + parent.modelErrorAllowance)

/-- Select a child centre by one operational comparison of the two
base-point coefficient names.  Every index and reading returned here is
finite rational data. -/
def alignRight {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name)
    (target : Coordinate) (positive : 0 < target) :
    CenterAlignment parent child parentCenter target := by
  let alignedEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      parentCenter.named (CenterState.baseNamed child) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      parentCenter.equivalent.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans coefficientEquivalent
        (CenterState.baseEquivalent child))
  let childStart := CenterState.canonicalIndex child
  let comparison := alignedEquivalent.compare 0 childStart target positive
  let childState := CCL.ProgressiveSampling.stateAt
    (child.coefficient 0 child.baseInside).name.process
      (child.readingState 0 child.baseInside) comparison.rightIndex
  let childCenter : CenterState child :=
    CenterState.ofState child childState
      (by
        intro value possible
        exact CCL.ProgressiveSampling.stateAt_possible_at_start
          (child.coefficient 0 child.baseInside).name.process
            (child.readingState 0 child.baseInside)
              comparison.rightIndex possible)
      (by
        have indexOrder : CCL.ProgressiveSampling.refinementTarget
            comparison.rightIndex <=
          CCL.ProgressiveSampling.refinementTarget childStart := by
          unfold CCL.ProgressiveSampling.refinementTarget
          exact CCL.FiniteGeometric.quarterRadius_antitone
            (by decide) comparison.right_ge
        exact
          ((CCL.ProgressiveSampling.stateAt_accurate
            (child.coefficient 0 child.baseInside).name.process
              (child.readingState 0 child.baseInside)
                comparison.rightIndex).trans_le indexOrder).trans
            (CCL.FiniteGeometric.firstQuarterBelow_accurate
              1 (by decide) 0 child.readingTarget
                child.readingTarget_positive))
  exact
    { childCenter := childCenter
      close := by
        let parentLater := parentCenter.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            RFAP.ConstructiveGaussian.Gaussian.normSq
                (childCenter.value - parentLater) < target := by
          have reverse : childCenter.value - parentLater =
              -(parentLater - childCenter.value) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
          rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
          exact alignedClose
        have parentTail :=
          parentCenter.laterValue_sub_value_lt comparison.leftIndex
        have identity : childCenter.value - parentCenter.value =
            (childCenter.value - parentLater) +
              (parentLater - parentCenter.value) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
        rw [identity]
        exact
          (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans_lt
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide)
              (RFAP.ConstructiveFraction.add_lt_add_direct
                alignedCloseReverse parentTail)) }

/-- Every persisted centre witness remains within one model-error allowance
of the originally prepared base reading.  Both are explicit candidates of
the same already-small finite ball. -/
theorem CenterState.value_sub_baseReading_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (center.value - prepared.baseReading) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball
    (prepared.readingState 0 prepared.baseInside)
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible_at_readingState
  have baseInside : ball.Contains prepared.baseReading :=
    process.possible_inside
      (prepared.reading_possible 0 prepared.baseInside)
  have centerDifference :
      center.value - prepared.baseReading =
        (center.value - ball.center) +
          (ball.center - prepared.baseReading) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have centerToBaseCenter :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - prepared.baseReading) <= ball.radiusSq := by
    have identity : ball.center - prepared.baseReading =
        -(prepared.baseReading - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [identity, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact baseInside
  have radiusSmall : ball.radiusSq < prepared.readingTarget :=
    prepared.reading_radius_lt 0 prepared.baseInside
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (center.value - prepared.baseReading) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((center.value - ball.center) +
          (ball.center - prepared.baseReading)) := by rw [centerDifference]
    _ <= 2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            (center.value - ball.center) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (ball.center - prepared.baseReading)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add centerInside centerToBaseCenter) (by decide)
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide)
        (RFAP.ConstructiveFraction.add_lt_add_direct radiusSmall radiusSmall)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      half_lt_self prepared.modelErrorAllowance_positive

theorem point_contains {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    prepared.ambient.Contains (prepared.point fraction) := by
  change prepared.ambient.Contains (prepared.localSegment.pointAt fraction)
  simp only [localSegment, CCL.Riemann.PreparedDifferentialModels.edge]
  rw [← CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
    prepared.segment prepared.within prepared.left prepared.request fraction]
  exact prepared.segment.pointAt_contains prepared.within
    (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction)
    (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside prepared.left
      prepared.request prepared.ordered fraction inside)

/-- The selected quotient reading exposes the exact rational numerator and
one finite candidate of the transported denominator process. -/
theorem reading_components {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    ∃ denominator : Gaussian,
      (prepared.sheetValue fraction inside).value.name.process.Possible
          (prepared.readingState fraction inside).2 denominator ∧
        prepared.reading fraction inside =
          prepared.point fraction ^ differential.exponent / denominator := by
  exact differentialValue_possible_components differential
    (prepared.point fraction) (prepared.sheetValue fraction inside).value
      (prepared.sheetValue fraction inside).apart
      (prepared.readingState fraction inside)
      (prepared.reading_possible fraction inside)

theorem denominator_candidate_in_source {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner
      prepared.request).track.initial.box.Contains candidate :=
  CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached_candidate_in_prepared_box
    curve differential prepared.segment prepared.within prepared.left
      prepared.owner prepared.request prepared.cached prepared.ordered
        prepared.small prepared.sheet fraction inside state possible

/-- Cached form of `denominator_candidate_in_source`.  Certificate-facing
clients should use this statement when the prepared owner itself carries the
finite enclosure they want to reuse. -/
theorem denominator_candidate_in_cached_source {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    prepared.cached.preparedOwner.track.initial.box.Contains candidate := by
  rw [prepared.cached.preparedOwner_eq]
  exact prepared.denominator_candidate_in_source fraction inside state possible

theorem denominator_candidate_lower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
        prepared.segment <=
      RFAP.ConstructiveGaussian.Gaussian.normSq candidate := by
  have pointwiseLower :
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
    change CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
        prepared.segment <=
      (CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached curve
        differential
        prepared.segment prepared.within prepared.left prepared.owner
          prepared.request prepared.cached prepared.ordered prepared.small
            prepared.sheet fraction inside).apart.certificate.lowerSq
    rw [CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached_apart_lowerSq]
    exact
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_le_point
        prepared.segment prepared.within
        (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside)
  exact pointwiseLower.trans
    ((prepared.sheetValue fraction inside).apart.certificate.lower state
      ((prepared.sheetValue fraction inside).value.name.process.possible_inside
        possible))

/-- The sharper cached denominator floor bounds every queried root candidate.
The segment contribution is the existing pointwise apartness estimate; the
box contribution follows from the prepared-owner containment certificate. -/
theorem preparedDenominator_candidate_lower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    prepared.preparedDenominatorLower <=
      RFAP.ConstructiveGaussian.Gaussian.normSq candidate := by
  apply max_le
  · exact prepared.denominator_candidate_lower fraction inside state possible
  · have candidateInside :=
      prepared.denominator_candidate_in_source fraction inside state possible
    rw [prepared.cached.preparedOwner_eq]
    exact boxNormSqLower_le candidateInside

/-- The productive coefficient process on a cached prepared edge retains the
same finite ambient/denominator centre bound as the canonical query. -/
theorem coefficient_centerBound_le_automatic {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.centerBound <=
      CCL.Riemann.PreparedDifferentialModels.automaticBoundValue differential
        prepared.segment := by
  have pointNormBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq (prepared.point fraction) <=
        prepared.ambient.normSqBound :=
    prepared.ambient.normSq_le_normSqBound
      (prepared.point_contains fraction inside)
  have numeratorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq (prepared.point fraction) ^
          differential.exponent <=
        prepared.ambient.normSqBound ^ differential.exponent :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
      pointNormBound differential.exponent
  have segmentLower :
      CCL.Riemann.PreparedDifferentialModels.denominatorLower
          prepared.segment <=
        CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
          prepared.segment :=
    (le_max_left _ _).trans (le_max_left _ _)
  have pointwiseLower :
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
    change CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
        prepared.segment <=
      (CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached curve
        differential prepared.segment prepared.within prepared.left
          prepared.owner prepared.request prepared.cached prepared.ordered
            prepared.small prepared.sheet fraction inside).apart.certificate.lowerSq
    rw [CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached_apart_lowerSq]
    exact
      CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower_le_point
        prepared.segment prepared.within
        (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside)
  have denominatorBound :
      CCL.Riemann.PreparedDifferentialModels.denominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq :=
    segmentLower.trans pointwiseLower
  have actualPositive :
      0 < (prepared.sheetValue fraction inside).apart.certificate.lowerSq :=
    (CCL.Riemann.PreparedDifferentialModels.denominatorLower_positive
      prepared.segment).trans_le denominatorBound
  unfold coefficient
    CCL.Riemann.PreparedDifferentialModels.coefficientAtCached
  rw [CCL.Riemann.AlgebraicDifferentials.differentialValue_centerBound]
  unfold CCL.Riemann.PreparedDifferentialModels.automaticBoundValue
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (prepared.point fraction) ^
          differential.exponent /
          (prepared.sheetValue fraction inside).apart.certificate.lowerSq <=
        prepared.ambient.normSqBound ^ differential.exponent /
          (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        numeratorBound
        (RFAP.ConstructiveFraction.inv_pos_direct actualPositive).le
    _ <= prepared.ambient.normSqBound ^ differential.exponent /
          CCL.Riemann.PreparedDifferentialModels.denominatorLower
            prepared.segment :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent)
        (CCL.Riemann.PreparedDifferentialModels.denominatorLower_positive
          prepared.segment)
        denominatorBound

/-- A segment-wide squared norm bound for every persisted coefficient centre
whose edge model error is at most `errorBound`. -/
def centerValueNormSqBound {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) : Coordinate :=
  2 * (errorBound / 8 +
    CCL.Riemann.PreparedDifferentialModels.automaticBoundValue differential
      segment)

theorem centerValueNormSqBound_nonnegative {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {errorBound : Coordinate} (errorBoundNonnegative : 0 <= errorBound) :
    0 <= centerValueNormSqBound differential segment errorBound := by
  unfold centerValueNormSqBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.div_nonneg_direct errorBoundNonnegative
        (by decide))
      (CCL.Riemann.PreparedDifferentialModels.automaticBoundValue_nonnegative
        differential segment))

/-- A cheaper coefficient upper bound for executable sample preflight.  It
uses the residual component of the certified denominator floor directly,
avoiding the dyadic-magnitude calculation while only enlarging a global
sample bound (never a refinement error scale). -/
def residualAutomaticBoundValue {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) : Coordinate :=
  ambient.normSqBound ^ differential.exponent /
    CCL.Riemann.PreparedDifferentialModels.residualDenominatorLower segment

private theorem residualDenominatorLower_positive
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < CCL.Riemann.PreparedDifferentialModels.residualDenominatorLower
      segment := by
  unfold CCL.Riemann.PreparedDifferentialModels.residualDenominatorLower
  exact RFAP.ConstructiveFraction.div_pos_direct
    (lt_min (by decide)
      (RFAP.ConstructiveFraction.div_pos_direct
        segment.clearanceBound_positive (by decide)))
    (by decide)

theorem automaticBoundValue_le_residual {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    CCL.Riemann.PreparedDifferentialModels.automaticBoundValue differential
        segment <=
      residualAutomaticBoundValue differential segment := by
  unfold CCL.Riemann.PreparedDifferentialModels.automaticBoundValue
    residualAutomaticBoundValue
  apply RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (residualDenominatorLower_positive segment)
  unfold CCL.Riemann.PreparedDifferentialModels.denominatorLower
  exact le_max_left _ _

theorem residualAutomaticBoundValue_nonnegative {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    0 <= residualAutomaticBoundValue differential segment :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (residualDenominatorLower_positive segment).le

/-- Residual-floor counterpart of `centerValueNormSqBound`. -/
def centerValueNormSqResidualBound {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) : Coordinate :=
  2 * (errorBound / 8 + residualAutomaticBoundValue differential segment)

theorem centerValueNormSqBound_le_residual {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) :
    centerValueNormSqBound differential segment errorBound <=
      centerValueNormSqResidualBound differential segment errorBound := by
  unfold centerValueNormSqBound centerValueNormSqResidualBound
  have sumOrder :
      errorBound / 8 +
          CCL.Riemann.PreparedDifferentialModels.automaticBoundValue
            differential segment <=
        errorBound / 8 + residualAutomaticBoundValue differential segment :=
    RFAP.ConstructiveFraction.add_le_add_direct (le_refl _)
      (automaticBoundValue_le_residual differential segment)
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    sumOrder (by decide)

theorem centerValueNormSqResidualBound_nonnegative {genus : Nat}
    (differential : Differential genus)
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {errorBound : Coordinate} (errorBoundNonnegative : 0 <= errorBound) :
    0 <= centerValueNormSqResidualBound differential segment errorBound := by
  unfold centerValueNormSqResidualBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.div_nonneg_direct errorBoundNonnegative
        (by decide))
      (residualAutomaticBoundValue_nonnegative differential segment))

theorem CenterState.value_normSq_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (errorBound : Coordinate)
    (errorLe : prepared.modelErrorAllowance <= errorBound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq center.value <=
      centerValueNormSqBound differential prepared.segment errorBound := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have centerInside :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (center.value - ball.center) <= ball.radiusSq :=
    process.possible_inside center.value_possible
  have ballCenterBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq ball.center <=
        process.centerBound :=
    process.center_bounded center.state
  have processBound : process.centerBound <=
      CCL.Riemann.PreparedDifferentialModels.automaticBoundValue differential
        prepared.segment :=
    prepared.coefficient_centerBound_le_automatic 0 prepared.baseInside
  have radiusBound : ball.radiusSq <= errorBound / 8 :=
    center.radius_lt.le.trans (by
      unfold readingTarget
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        errorLe
        (RFAP.ConstructiveFraction.inv_pos_direct
          (show (0 : Coordinate) < 8 by decide)).le)
  have identity : center.value =
      (center.value - ball.center) + ball.center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [identity]
  exact
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (centerInside.trans radiusBound)
          (ballCenterBound.trans processBound)) (by decide))

/-- The queried rational coefficient reading is uniformly close to the one
fixed base reading, with an allowance that shrinks with the base edge and the
prepared root box. -/
theorem reading_difference_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (prepared.reading fraction inside - prepared.baseReading) <=
      prepared.modelErrorAllowance := by
  rcases prepared.reading_components fraction inside with
    ⟨queryRoot, queryRootPossible, queryReadingEqual⟩
  rcases prepared.reading_components 0 prepared.baseInside with
    ⟨baseRoot, baseRootPossible, baseReadingEqual⟩
  have queryRootInside := prepared.denominator_candidate_in_source fraction
    inside (prepared.readingState fraction inside).2 queryRootPossible
  have baseRootInside := prepared.denominator_candidate_in_source 0
    prepared.baseInside (prepared.readingState 0 prepared.baseInside).2
      baseRootPossible
  have queryRootLower := prepared.preparedDenominator_candidate_lower
    fraction inside (prepared.readingState fraction inside).2 queryRootPossible
  have baseRootLower := prepared.preparedDenominator_candidate_lower 0
    prepared.baseInside (prepared.readingState 0 prepared.baseInside).2
      baseRootPossible
  have queryPointBound := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains fraction inside)
  have basePointBound := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains 0 prepared.baseInside)
  have pointDifference :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (prepared.point fraction - prepared.point 0) <=
        prepared.pointMovement := by
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        (prepared.localSegment.pointAt fraction -
          prepared.localSegment.pointAt 0) <= _
    unfold pointMovement
    change _ <= RFAP.ConstructiveGaussian.Gaussian.normSq
      (prepared.localSegment.pointAt 1 - prepared.localSegment.pointAt 0)
    exact prepared.localSegment.normSq_pointAt_sub_zero_le_full fraction inside
  have numeratorDifference :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (prepared.point fraction ^ differential.exponent -
            prepared.point 0 ^ differential.exponent) <=
        CCL.Riemann.FiniteQuotientVariation.powerSlope
            prepared.ambient.normSqBound differential.exponent *
          prepared.pointMovement :=
    (CCL.Riemann.FiniteQuotientVariation.normSq_pow_sub_pow_le
      prepared.ambient.normSqBound_nonneg differential.exponent
      queryPointBound basePointBound).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          pointDifference
          (CCL.Riemann.FiniteQuotientVariation.powerSlope_nonnegative
            prepared.ambient.normSqBound_nonneg differential.exponent))
  have baseNumeratorBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (prepared.point 0 ^ differential.exponent) <=
        prepared.ambient.normSqBound ^ differential.exponent := by
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_pow]
    exact RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg (prepared.point 0))
      basePointBound differential.exponent
  have baseRootBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq baseRoot <=
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound := by
    apply (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSq_le_normSqBound
    have refines :
        (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner
          prepared.request).track.initial.box.Refines
            (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
              prepared.segment) := by
      exact
        CCL.Riemann.PreparedSheetContinuation.prepared_initial_box_refines_rootAmbient
          prepared.segment prepared.left prepared.owner prepared.request
    exact refines.contains baseRootInside
  have rootDifference :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (baseRoot - queryRoot) <= prepared.preparedRootDiameter := by
    rw [prepared.preparedRootDiameter_eq_canonical]
    exact (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner
      prepared.request).track.initial.box.normSq_sub_le_diagonalSq
        baseRootInside queryRootInside
  have quotientDifference :=
    CCL.Riemann.FiniteQuotientVariation.normSq_div_sub_div_le
      prepared.preparedDenominatorLower_positive
      numeratorDifference baseNumeratorBound baseRootBound rootDifference
        queryRootLower baseRootLower
  have rawBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (prepared.reading fraction inside - prepared.baseReading) <=
        prepared.rawVariation := by
    rw [queryReadingEqual]
    unfold baseReading
    rw [baseReadingEqual]
    exact quotientDifference
  exact rawBound.trans
    (le_add_of_nonneg_right prepared.preparedRootDiameter_positive.le)

/-- A queried edge reading differs from any persisted centre by the direct
variation error plus the finite centre-rebasing error. -/
theorem CenterState.reading_sub_value_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (prepared.reading fraction inside - center.value) <=
      4 * prepared.modelErrorAllowance := by
  have identity :
      prepared.reading fraction inside - center.value =
        (prepared.reading fraction inside - prepared.baseReading) +
          (prepared.baseReading - center.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have reversedCenter :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (prepared.baseReading - center.value) <=
        prepared.modelErrorAllowance := by
    have reversed : prepared.baseReading - center.value =
        -(center.value - prepared.baseReading) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reversed, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact center.value_sub_baseReading_lt.le
  rw [identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((prepared.reading fraction inside - prepared.baseReading) +
          (prepared.baseReading - center.value)) <=
      2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            (prepared.reading fraction inside - prepared.baseReading) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (prepared.baseReading - center.value)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ <= 2 * (prepared.modelErrorAllowance +
        prepared.modelErrorAllowance) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (prepared.reading_difference_le fraction inside)
          reversedCenter) (by decide)
    _ = 4 * prepared.modelErrorAllowance := by ring1

/-- A finitely accurate coefficient state at an arbitrary rational parameter
of one prepared parent edge.  This is the comparison anchor used when a
child subdivision begins in the interior of that parent edge. -/
structure QueryState {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) where
  state : (prepared.coefficient fraction inside).name.process.State
  persists : forall {value : Gaussian},
    (prepared.coefficient fraction inside).name.process.Possible state value ->
      (prepared.coefficient fraction inside).name.process.Possible
        (prepared.readingState fraction inside) value
  radius_lt :
    ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
      prepared.readingTarget

namespace QueryState

/-- The prepared reading at the requested rational parameter is already a
valid query state.  Reusing it avoids a second generic coefficient search at
every boundary between consecutive subdivision edges. -/
def canonical {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    QueryState prepared fraction inside where
  state := prepared.readingState fraction inside
  persists := by
    intro value possible
    exact possible
  radius_lt := prepared.reading_radius_lt fraction inside

def value {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) : Gaussian :=
  ((prepared.coefficient fraction inside).name.process.witness query.state).val

theorem value_possible {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    (prepared.coefficient fraction inside).name.process.Possible
      query.state query.value :=
  ((prepared.coefficient fraction inside).name.process.witness
    query.state).property

theorem value_possible_at_readingState {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    (prepared.coefficient fraction inside).name.process.Possible
      (prepared.readingState fraction inside) query.value :=
  query.persists query.value_possible

def named {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    CCL.ProgressiveTransducer.Named :=
  { process := (prepared.coefficient fraction inside).name.process
    state := query.state }

def equivalent {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    CCL.OperationalEquivalence.NamedEquivalent
      (prepared.coefficient fraction inside).name query.named :=
  CCL.ProgressiveCoherence.CoherentNamed.rebaseEquivalent
    (prepared.coefficient fraction inside) query.state

def laterValue {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) : Gaussian :=
  CCL.ProgressiveSampling.witnessAt
    (prepared.coefficient fraction inside).name.process query.state index

theorem laterValue_possible_at_state {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    (prepared.coefficient fraction inside).name.process.Possible
      query.state (query.laterValue index) :=
  CCL.ProgressiveSampling.witnessAt_possible_start
    (prepared.coefficient fraction inside).name.process query.state index

end QueryState

/-- A query state refined to one caller-supplied positive squared-radius
target.  The ordinary `QueryState` accuracy is retained as well, so this
payload can be consumed by the existing child-alignment API. -/
structure TargetedQueryState {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (target : Coordinate) where
  query : QueryState prepared fraction inside
  radius_lt_target :
    ((prepared.coefficient fraction inside).name.process.ball
      query.state).radiusSq < target

namespace TargetedQueryState

/-- Refine the canonical finite query just far enough to meet both its model
accuracy obligation and the caller's sharper target. -/
def atTarget {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (target : Coordinate) (targetPositive : 0 < target) :
    TargetedQueryState prepared fraction inside target := by
  let accuracy := min target prepared.readingTarget
  have accuracyPositive : 0 < accuracy :=
    lt_min targetPositive prepared.readingTarget_positive
  let index := CCL.FiniteGeometric.firstQuarterBelow 1 0 accuracy
  let state := CCL.ProgressiveSampling.stateAt
    (prepared.coefficient fraction inside).name.process
      (prepared.readingState fraction inside) index
  have stateAccurate :
      ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
        accuracy :=
    (CCL.ProgressiveSampling.stateAt_accurate
      (prepared.coefficient fraction inside).name.process
        (prepared.readingState fraction inside) index).trans
      (CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) 0 accuracy accuracyPositive)
  exact
    { query :=
        { state := state
          persists := by
            intro value possible
            exact CCL.ProgressiveSampling.stateAt_possible_at_start
              (prepared.coefficient fraction inside).name.process
                (prepared.readingState fraction inside) index possible
          radius_lt := stateAccurate.trans_le (min_le_right _ _) }
      radius_lt_target := stateAccurate.trans_le (min_le_left _ _) }

end TargetedQueryState

/-- Exact ball-radius form of the distance between a retained query witness
and any later witness of the same finite process. -/
theorem QueryState.laterValue_sub_value_le_radius {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (query.laterValue index - query.value) <=
      4 * ((prepared.coefficient fraction inside).name.process.ball
        query.state).radiusSq := by
  let process := (prepared.coefficient fraction inside).name.process
  let ball := process.ball query.state
  have laterInside : ball.Contains (query.laterValue index) :=
    process.possible_inside (query.laterValue_possible_at_state index)
  have queryInside : ball.Contains query.value :=
    process.possible_inside query.value_possible
  have identity : query.laterValue index - query.value =
      (query.laterValue index - ball.center) +
        (ball.center - query.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have queryReverse :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - query.value) <= ball.radiusSq := by
    have reverse : ball.center - query.value =
        -(query.value - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact queryInside
  rw [identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((query.laterValue index - ball.center) +
          (ball.center - query.value)) <=
      2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
          (query.laterValue index - ball.center) +
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - query.value)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add laterInside queryReverse) (by decide)
    _ = 4 * ball.radiusSq := by ring1

private theorem coefficientCandidates_sub_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.coefficient fraction inside).name.process.State)
    (radiusSmall :
      ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
        prepared.readingTarget)
    {left right : Gaussian}
    (leftPossible :
      (prepared.coefficient fraction inside).name.process.Possible state left)
    (rightPossible :
      (prepared.coefficient fraction inside).name.process.Possible state right) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (left - right) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient fraction inside).name.process
  let ball := process.ball state
  have leftInside : ball.Contains left :=
    process.possible_inside leftPossible
  have rightInside : ball.Contains right :=
    process.possible_inside rightPossible
  have identity : left - right =
      (left - ball.center) + (ball.center - right) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have rightReverse :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (ball.center - right) <= ball.radiusSq := by
    have reverse : ball.center - right = -(right - ball.center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact rightInside
  rw [identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((left - ball.center) + (ball.center - right)) <=
      2 * (ball.radiusSq + ball.radiusSq) :=
      (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftInside rightReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide)
        (RFAP.ConstructiveFraction.add_lt_add_direct radiusSmall radiusSmall)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      half_lt_self prepared.modelErrorAllowance_positive

theorem QueryState.laterValue_sub_value_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (query.laterValue index - query.value) <
      prepared.modelErrorAllowance :=
  coefficientCandidates_sub_lt prepared fraction inside query.state
    query.radius_lt (query.laterValue_possible_at_state index)
      query.value_possible

theorem QueryState.value_sub_reading_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (query.value - prepared.reading fraction inside) <
      prepared.modelErrorAllowance :=
  coefficientCandidates_sub_lt prepared fraction inside
    (prepared.readingState fraction inside)
    (prepared.reading_radius_lt fraction inside)
      query.value_possible_at_readingState
      (prepared.reading_possible fraction inside)

/-- An accurate query witness remains close to the selected constant centre
of its parent edge, with every contribution exposed as finite rational
allowance. -/
theorem QueryState.value_sub_center_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside)
    (center : CenterState prepared) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (query.value - center.value) <
      10 * prepared.modelErrorAllowance := by
  have identity : query.value - center.value =
      (query.value - prepared.reading fraction inside) +
        (prepared.reading fraction inside - center.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((query.value - prepared.reading fraction inside) +
          (prepared.reading fraction inside - center.value)) <=
      2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            (query.value - prepared.reading fraction inside) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (prepared.reading fraction inside - center.value)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ < 2 * (prepared.modelErrorAllowance +
        4 * prepared.modelErrorAllowance) :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        (by decide)
        ((RFAP.ConstructiveFraction.add_lt_add_right_direct
            query.value_sub_reading_lt
            (RFAP.ConstructiveGaussian.Gaussian.normSq
              (prepared.reading fraction inside - center.value))).trans_le
          (RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            (center.reading_sub_value_le fraction inside)))
    _ = 10 * prepared.modelErrorAllowance := by ring1

structure QueryCenterAlignment {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside) (target : Coordinate) where
  childCenter : CenterState child
  close_radius :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (childCenter.value - query.value) <
      2 * (target +
        4 * ((parent.coefficient fraction inside).name.process.ball
          query.state).radiusSq)
  close :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (childCenter.value - query.value) <
      2 * (target + parent.modelErrorAllowance)

/-- Operationally align a child base coefficient with the coefficient queried
at its starting parameter inside the parent edge. -/
def alignQueryRight {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name)
    (target : Coordinate) (positive : 0 < target) :
    QueryCenterAlignment parent child query target := by
  let alignedEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      query.named (CenterState.baseNamed child) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans query.equivalent.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans coefficientEquivalent
        (CenterState.baseEquivalent child))
  let childStart := CenterState.canonicalIndex child
  let comparison := alignedEquivalent.compare 0 childStart target positive
  let childState := CCL.ProgressiveSampling.stateAt
    (child.coefficient 0 child.baseInside).name.process
      (child.readingState 0 child.baseInside) comparison.rightIndex
  let childCenter : CenterState child :=
    CenterState.ofState child childState
      (by
        intro value possible
        exact CCL.ProgressiveSampling.stateAt_possible_at_start
          (child.coefficient 0 child.baseInside).name.process
            (child.readingState 0 child.baseInside)
              comparison.rightIndex possible)
      (by
        have indexOrder : CCL.ProgressiveSampling.refinementTarget
            comparison.rightIndex <=
          CCL.ProgressiveSampling.refinementTarget childStart := by
          unfold CCL.ProgressiveSampling.refinementTarget
          exact CCL.FiniteGeometric.quarterRadius_antitone
            (by decide) comparison.right_ge
        exact
          ((CCL.ProgressiveSampling.stateAt_accurate
            (child.coefficient 0 child.baseInside).name.process
              (child.readingState 0 child.baseInside)
                comparison.rightIndex).trans_le indexOrder).trans
            (CCL.FiniteGeometric.firstQuarterBelow_accurate
              1 (by decide) 0 child.readingTarget
                child.readingTarget_positive))
  exact
    { childCenter := childCenter
      close_radius := by
        let queryLater := query.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            RFAP.ConstructiveGaussian.Gaussian.normSq
                (childCenter.value - queryLater) < target := by
          have reverse : childCenter.value - queryLater =
              -(queryLater - childCenter.value) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
          rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
          exact alignedClose
        have queryTail := query.laterValue_sub_value_le_radius
          comparison.leftIndex
        have identity : childCenter.value - query.value =
            (childCenter.value - queryLater) +
              (queryLater - query.value) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
        rw [identity]
        exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans_lt
          (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (by decide)
            ((RFAP.ConstructiveFraction.add_lt_add_right_direct
              alignedCloseReverse
                (RFAP.ConstructiveGaussian.Gaussian.normSq
                  (queryLater - query.value))).trans_le
              (add_le_add le_rfl queryTail)))
      close := by
        let queryLater := query.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            RFAP.ConstructiveGaussian.Gaussian.normSq
                (childCenter.value - queryLater) < target := by
          have reverse : childCenter.value - queryLater =
              -(queryLater - childCenter.value) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.neg_re,
                RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
          rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
          exact alignedClose
        have queryTail := query.laterValue_sub_value_lt comparison.leftIndex
        have identity : childCenter.value - query.value =
            (childCenter.value - queryLater) +
              (queryLater - query.value) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
        rw [identity]
        exact
          (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans_lt
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide)
              (RFAP.ConstructiveFraction.add_lt_add_direct
                alignedCloseReverse queryTail)) }

def alignedChildAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    CenterState child :=
  (alignQueryRight parent child query coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive).childCenter

/-- The shrinking Gaussian-constant cell model. -/
def model {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : CellModel :=
  { start := prepared.point 0
    finish := prepared.point 1
    polynomial := CCL.FiniteGaussianPolynomial.constant prepared.baseReading
    localAllowance := 4 * prepared.modelErrorAllowance
    localAllowance_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        prepared.modelErrorAllowance_positive.le
    observations := [] }

/-- The same shrinking cell recentered at an arbitrary persisted finite
coefficient state.  The larger constant factor pays explicitly for the
finite rebasing comparison. -/
def centeredModel {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) : CellModel :=
  { start := prepared.point 0
    finish := prepared.point 1
    polynomial := CCL.FiniteGaussianPolynomial.constant center.value
    localAllowance := 16 * prepared.modelErrorAllowance
    localAllowance_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        sixteen_nonnegative
        prepared.modelErrorAllowance_positive.le
    observations := [] }

/-- A literal recache of one centre is a certified one-cell constant
partition of the original centred model.  The geometry is unchanged, and
the same-state stability theorem places the coefficient discrepancy inside
the ordinary child allowance. -/
def centeredModelRecachePartitionCertificate
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      (prepared.centeredModel center)
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        [prepared.centeredModel
          (center.recache value denominator denominatorPossible valueEq)]) := by
  let replacement :=
    center.recache value denominator denominatorPossible valueEq
  let error := replacement.value - center.value
  have errorLe : RFAP.ConstructiveGaussian.Gaussian.normSq error <=
      (prepared.centeredModel replacement).localAllowance := by
    have localBound := center.recache_value_sub_value_lt value denominator
      denominatorPossible valueEq
    apply localBound.le.trans
    change prepared.modelErrorAllowance <=
      16 * prepared.modelErrorAllowance
    calc
      prepared.modelErrorAllowance = 1 * prepared.modelErrorAllowance := by
        ring1
      _ <= 16 * prepared.modelErrorAllowance :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (by decide) prepared.modelErrorAllowance_positive.le
  exact
    { reference := center.value
      parent_polynomial_eq := rfl
      errors := [error]
      comparison := .cons replacement.value error rfl rfl errorLe .nil
      displacement_eq := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [CCL.ProgressiveGaussianIntegration.PathModel.displacementSum,
            List.foldr_cons, List.foldr_nil,
            CCL.ProgressiveGaussianIntegration.CellModel.displacement,
            centeredModel, RFAP.ConstructiveGaussian.Gaussian.add_re,
            RFAP.ConstructiveGaussian.Gaussian.add_im,
            RFAP.ConstructiveGaussian.Gaussian.zero_re,
            RFAP.ConstructiveGaussian.Gaussian.zero_im,
            RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1 }

/-- The centred constant cell really integrates the retained rational
coefficient.  In genus one this exposes one finite reciprocal, with no
coefficient or sheet-process recomputation. -/
theorem centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    (prepared.centeredModel center).integralSample =
      (prepared.centeredModel center).displacement * (1 / center.denominator) := by
  rw [CCL.ProgressiveGaussianIntegration.PathModel.CellModel.integralSample_constant
    (prepared.centeredModel center) center.value rfl,
      center.value_eq_one_div_denominator_of_exponent_zero exponentZero]

/-- A positive rational dot-product floor for one prepared genus-one cell
gives a positive lower bound for the real projection of its integral sample.
The only geometric input is membership of the retained denominator in the
prepared source box. -/
theorem centeredModel_integralSample_re_lower_of_projection
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0)
    (projectionLower : Coordinate) (projectionPositive : 0 < projectionLower)
    (projectionLe : projectionLower <=
      (prepared.centeredModel center).displacement.re * center.denominator.re +
        (prepared.centeredModel center).displacement.im * center.denominator.im) :
    projectionLower /
        (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner prepared.request).track.initial.box.normSqBound <=
      (prepared.centeredModel center).integralSample.re := by
  let box :=
    (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner prepared.request).track.initial.box
  let displacement := (prepared.centeredModel center).displacement
  let denominator := center.denominator
  have inside : box.Contains denominator := center.denominator_in_prepared_box
  have denominatorNonzero : denominator ≠ 0 := by
    intro equal
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
    have imaginaryZero := congrArg RFAP.ConstructiveGaussian.Gaussian.im equal
    simp only [RFAP.ConstructiveGaussian.Gaussian.zero_re] at realZero
    simp only [RFAP.ConstructiveGaussian.Gaussian.zero_im] at imaginaryZero
    rw [realZero, imaginaryZero] at projectionLe
    simp only [RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add] at projectionLe
    exact (not_lt_of_ge projectionLe) projectionPositive
  have normPositive : 0 <
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos denominatorNonzero
  have normLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator <= box.normSqBound :=
    box.normSq_le_normSqBound inside
  have lowerToSameNumerator :
      projectionLower / box.normSqBound <=
        projectionLower /
          RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      projectionPositive.le normPositive normLe
  have sameDenominator :
      projectionLower /
          RFAP.ConstructiveGaussian.Gaussian.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            RFAP.ConstructiveGaussian.Gaussian.normSq denominator := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      projectionLe
      (RFAP.ConstructiveFraction.inv_pos_direct normPositive).le
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact lowerToSameNumerator.trans sameDenominator

/-- Geometric displacement of one accepted prepared edge.  This projection
does not inspect the retained coefficient centre. -/
def integralDisplacement
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  prepared.point 1 - prepared.point 0

/-- Unconditional compact rational lower endpoint for an arbitrary projected
displacement against one prepared edge's cached denominator box. -/
def geometricIntegralProjectionLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (displacement : Gaussian) : Coordinate :=
  let box := prepared.cached.preparedOwner.track.initial.box
  signedQuotientLower
    (dyadicRealLower
      (boxProjectionLower box displacement))
    (geometricDenominatorLower prepared.segment box)
    (boxNormSqCeil box)

/-- Fixed-grid form of the arbitrary projected endpoint. -/
def geometricIntegralProjectionDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (displacement : Gaussian) : Coordinate :=
  dyadicRealLower
    (prepared.geometricIntegralProjectionLower displacement)

/-- Unconditional compact rational lower endpoint obtained solely from one
prepared edge's cached owner box and actual displacement. -/
def geometricIntegralRealLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionLower prepared.integralDisplacement

/-- Compatibility presentation of the geometric endpoint for a particular
retained centre.  The value is centre-independent by construction. -/
def centeredModelIntegralRealLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (_center : CenterState prepared) : Coordinate :=
  prepared.geometricIntegralRealLower

/-- Fixed-grid geometric endpoint suitable for long finite path folds. -/
def geometricIntegralRealDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    prepared.integralDisplacement

/-- Lower endpoint for the negative real projection of one cell. -/
def geometricNegatedIntegralRealDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    (-prepared.integralDisplacement)

/-- Centre-free endpoint for an arbitrary rational projection of the
integral.  If `direction = a + bi`, this bounds `a * integral.re +
b * integral.im`.  Multiplying the displacement by the conjugate direction
before applying the existing quotient bound keeps the construction entirely
inside finite Gaussian-rational arithmetic. -/
def geometricDirectionalIntegralDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    (direction.conj * prepared.integralDisplacement)

/-- Sign-aware denominator floor obtained from the apartness certificate and
the compact box selected at a retained state. -/
def centeredBallDenominatorLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  geometricDenominatorLower prepared.segment center.denominatorProjectionBox

theorem centeredBallDenominatorLower_positive
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    0 < centeredBallDenominatorLower center :=
  geometricDenominatorLower_positive prepared.segment
    center.denominatorProjectionBox

/-- Sharp finite lower endpoint using the canonical process ball when it fits
the fixed rational sector square.  Its definition inspects only the retained
state enclosure and never evaluates the denominator witness. -/
def centeredBallIntegralProjectionLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) : Coordinate :=
  let box := center.denominatorProjectionBox
  let lowerSq := geometricDenominatorLower prepared.segment box
  signedQuotientLower
    (dyadicRealLower
      (boxProjectionLower box displacement))
    lowerSq
    (boxNormSqCeil box)

/-- Fixed-grid form of the compact process-ball projection endpoint. -/
def centeredBallIntegralProjectionDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) : Coordinate :=
  dyadicRealLower
    (centeredBallIntegralProjectionLower center displacement)

def centeredBallIntegralRealDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    prepared.integralDisplacement

def centeredBallNegatedIntegralRealDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    (-prepared.integralDisplacement)

/-- Sharp endpoint for an arbitrary rational projection, using the retained
coefficient process ball whenever it fits the fixed sector square. -/
def centeredBallDirectionalIntegralDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (direction : Gaussian) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    (direction.conj * prepared.integralDisplacement)

/-- The compact state-selected endpoint bounds the corresponding exact
reciprocal projection. -/
theorem centeredBallIntegralProjectionLower_le_quotient
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    centeredBallIntegralProjectionLower center displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator := by
  let box := center.denominatorProjectionBox
  let denominator := center.denominator
  let projection := boxProjectionLower box displacement
  let roundedProjection := dyadicRealLower projection
  let lowerSq := centeredBallDenominatorLower center
  let upperSq := boxNormSqCeil box
  have denominatorInsideBox : box.Contains denominator :=
    center.denominator_in_projection_box
  have lowerPositive : 0 < lowerSq :=
    centeredBallDenominatorLower_positive center
  have cellLowerLeNorm : cellDenominatorLower prepared.segment <=
        RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    ((le_max_right
        (CCL.Riemann.PreparedDifferentialModels.residualDenominatorLower
          prepared.segment)
        (CCL.Riemann.PreparedDifferentialModels.magnitudeDenominatorLower
          prepared.segment)).trans
      ((le_max_left _ _).trans (le_max_left _ _))).trans
      (prepared.denominator_candidate_lower 0 prepared.baseInside center.state.2
        center.denominator_possible)
  have boxLowerLeNorm : boxNormSqLower box <=
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    boxNormSqLower_le denominatorInsideBox
  have lowerLeNorm : lowerSq <=
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    max_le cellLowerLeNorm boxLowerLeNorm
  have normLeUpper :
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator <= upperSq :=
    (box.normSq_le_normSqBound denominatorInsideBox).trans
      (normSqBound_le_boxNormSqCeil box)
  have signedLower := signedQuotientLower_le roundedProjection lowerSq
    (RFAP.ConstructiveGaussian.Gaussian.normSq denominator) upperSq
      lowerPositive lowerLeNorm normLeUpper
  have projectionLe : projection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    boxProjectionLower_le denominatorInsideBox
  have roundedProjectionLe : roundedProjection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    (dyadicRealLower_le projection).trans projectionLe
  have normPositive : 0 <
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    lowerPositive.trans_le lowerLeNorm
  have quotientProjectionLe :
      roundedProjection /
          RFAP.ConstructiveGaussian.Gaussian.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            RFAP.ConstructiveGaussian.Gaussian.normSq denominator := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      roundedProjectionLe
        (RFAP.ConstructiveFraction.inv_pos_direct normPositive).le
  change signedQuotientLower roundedProjection lowerSq upperSq <= _
  exact signedLower.trans quotientProjectionLe

theorem centeredBallIntegralProjectionDyadicLower_le_quotient
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    centeredBallIntegralProjectionDyadicLower center displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator :=
  (dyadicRealLower_le _).trans
    (centeredBallIntegralProjectionLower_le_quotient center displacement)

theorem centeredBallIntegralRealDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredBallIntegralRealDyadicLower center <=
      (prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact centeredBallIntegralProjectionDyadicLower_le_quotient center
    prepared.integralDisplacement

theorem centeredBallNegatedIntegralRealDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredBallNegatedIntegralRealDyadicLower center <=
      -(prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  change centeredBallNegatedIntegralRealDyadicLower center <=
    -((prepared.integralDisplacement.re * center.denominator.re +
      prepared.integralDisplacement.im * center.denominator.im) /
        RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator)
  have bound := centeredBallIntegralProjectionDyadicLower_le_quotient
    center (-prepared.integralDisplacement)
  convert bound using 1
  · rfl
  · simp only [RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    ring1

/-- The sharp process-ball endpoint bounds any fixed rational linear
projection of the centred cell integral. -/
theorem centeredBallDirectionalIntegralDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centeredBallDirectionalIntegralDyadicLower center direction <=
      direction.re * (prepared.centeredModel center).integralSample.re +
        direction.im * (prepared.centeredModel center).integralSample.im := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero]
  have lower := centeredBallIntegralProjectionDyadicLower_le_quotient center
    (direction.conj * prepared.integralDisplacement)
  apply lower.trans_eq
  rw [← CenterState.mul_one_div_re]
  unfold integralDisplacement centeredModel
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
  simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im]
  ring1

/-- Fixed-grid version of the exact cell lower endpoint.  Long path folds
should consume this value so every addition stays on one dyadic grid. -/
def centeredModelIntegralRealDyadicLower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (_center : CenterState prepared) : Coordinate :=
  prepared.geometricIntegralRealDyadicLower

/-- The sign-aware box endpoint for any projected displacement bounds the
corresponding exact quotient against the retained denominator. -/
theorem geometricIntegralProjectionLower_le_quotient
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    prepared.geometricIntegralProjectionLower displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator := by
  let box := prepared.cached.preparedOwner.track.initial.box
  let denominator := center.denominator
  let projection := boxProjectionLower box displacement
  let roundedProjection := dyadicRealLower projection
  let lowerSq := geometricDenominatorLower prepared.segment box
  let upperSq := boxNormSqCeil box
  have denominatorInsideBox : box.Contains denominator :=
    center.denominator_in_cached_prepared_box
  have denominatorInsideBall :
      ((prepared.sheetValue 0 prepared.baseInside).value.name.process.ball
        center.state.2).Contains denominator :=
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.possible_inside
      center.denominator_possible
  have lowerPositive : 0 < lowerSq :=
    geometricDenominatorLower_positive prepared.segment box
  have segmentLowerLeApart : cellDenominatorLower prepared.segment <=
      (prepared.sheetValue 0 prepared.baseInside).apart.certificate.lowerSq := by
    change CCL.Riemann.PreparedDifferentialModels.magnitudeDenominatorLower
        prepared.segment <=
      (CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached curve
        differential prepared.segment prepared.within prepared.left
          prepared.owner prepared.request prepared.cached prepared.ordered
            prepared.small prepared.sheet 0
              prepared.baseInside).apart.certificate.lowerSq
    rw [CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached_apart_lowerSq]
    exact (le_max_right _ _).trans
      (CCL.Riemann.PreparedDifferentialModels.denominatorLower_le_point
        prepared.segment
          (prepared.segment.pointAt_onCertifiedLine
            (CCL.Riemann.PreparedSheetContinuation.parameterAt prepared.left
              prepared.request 0)
            (CCL.Riemann.PreparedSheetContinuation.parameterAt_inside
              prepared.left prepared.request prepared.ordered 0
                prepared.baseInside)))
  have segmentLowerLeNorm : cellDenominatorLower prepared.segment <=
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    segmentLowerLeApart.trans
      ((prepared.sheetValue 0 prepared.baseInside).apart.certificate.lower
        center.state.2 denominatorInsideBall)
  have boxLowerLeNorm : boxNormSqLower box <=
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    boxNormSqLower_le denominatorInsideBox
  have lowerLeNorm : lowerSq <=
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    max_le segmentLowerLeNorm boxLowerLeNorm
  have normLeUpper :
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator <= upperSq :=
    (box.normSq_le_normSqBound denominatorInsideBox).trans
      (normSqBound_le_boxNormSqCeil box)
  have signedLower := signedQuotientLower_le
    roundedProjection lowerSq
      (RFAP.ConstructiveGaussian.Gaussian.normSq denominator) upperSq
        lowerPositive lowerLeNorm normLeUpper
  have projectionLe : projection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    boxProjectionLower_le denominatorInsideBox
  have roundedProjectionLe : roundedProjection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    (dyadicRealLower_le projection).trans projectionLe
  have normPositive : 0 <
      RFAP.ConstructiveGaussian.Gaussian.normSq denominator :=
    lowerPositive.trans_le lowerLeNorm
  have quotientProjectionLe :
      roundedProjection /
          RFAP.ConstructiveGaussian.Gaussian.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            RFAP.ConstructiveGaussian.Gaussian.normSq denominator := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      roundedProjectionLe
        (RFAP.ConstructiveFraction.inv_pos_direct normPositive).le
  change signedQuotientLower roundedProjection lowerSq upperSq <= _
  exact signedLower.trans quotientProjectionLe

/-- Fixed-grid form of the arbitrary projected quotient lower. -/
theorem geometricIntegralProjectionDyadicLower_le_quotient
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    prepared.geometricIntegralProjectionDyadicLower displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator :=
  (dyadicRealLower_le _).trans
    (prepared.geometricIntegralProjectionLower_le_quotient center displacement)

/-- The arbitrary centre-free direction endpoint bounds the corresponding
linear projection of every retained centred model. -/
theorem geometricDirectionalIntegralDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricDirectionalIntegralDyadicLower direction <=
      direction.re * (prepared.centeredModel center).integralSample.re +
        direction.im * (prepared.centeredModel center).integralSample.im := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero]
  have lower := prepared.geometricIntegralProjectionDyadicLower_le_quotient
    center (direction.conj * prepared.integralDisplacement)
  apply lower.trans_eq
  rw [← CenterState.mul_one_div_re]
  unfold integralDisplacement centeredModel
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
  simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im]
  ring1

/-- The sign-aware real endpoint is a lower bound for every prepared
genus-one cell, without requiring the cell itself to lie in one positive
sector. -/
theorem centeredModelIntegralRealLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredModelIntegralRealLower center <=
      (prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact prepared.geometricIntegralProjectionLower_le_quotient center
    prepared.integralDisplacement

/-- The rounded endpoint retains the exact cellwise lower theorem. -/
theorem centeredModelIntegralRealDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredModelIntegralRealDyadicLower center <=
      (prepared.centeredModel center).integralSample.re :=
  (dyadicRealLower_le _).trans
    (centeredModelIntegralRealLower_le center exponentZero)

/-- Centre-free statement of the same cellwise bound.  A caller may compute
the endpoint from preparation geometry and supply any retained centre only
when relating it to an integration model. -/
theorem geometricIntegralRealDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricIntegralRealDyadicLower <=
      (prepared.centeredModel center).integralSample.re :=
  prepared.centeredModelIntegralRealDyadicLower_le center exponentZero

/-- The same cached geometry bounds the negative real projection when the
displayed A-cycle orientation makes that the positive sector. -/
theorem geometricNegatedIntegralRealDyadicLower_le
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricNegatedIntegralRealDyadicLower <=
      -(prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  change prepared.geometricNegatedIntegralRealDyadicLower <=
    -((prepared.integralDisplacement.re * center.denominator.re +
      prepared.integralDisplacement.im * center.denominator.im) /
        RFAP.ConstructiveGaussian.Gaussian.normSq center.denominator)
  have bound := prepared.geometricIntegralProjectionDyadicLower_le_quotient
    center (-prepared.integralDisplacement)
  convert bound using 1
  · rfl
  · simp only [RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    ring1

/-- The executable lower endpoint of the prepared owner box supplies the
projection hypothesis automatically.  A client only checks that this one
displayed rational is positive. -/
theorem centeredModel_integralSample_re_lower
    {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0)
    (positive : 0 < boxProjectionLower
      (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner prepared.request).track.initial.box
      (prepared.centeredModel center).displacement) :
    boxProjectionLower
        (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner prepared.request).track.initial.box
        (prepared.centeredModel center).displacement /
      (CCL.Riemann.PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner prepared.request).track.initial.box.normSqBound <=
      (prepared.centeredModel center).integralSample.re := by
  apply centeredModel_integralSample_re_lower_of_projection center exponentZero
    _ positive
  exact boxProjectionLower_le center.denominator_in_prepared_box

/-- Choose a child centre at the parent model's own positive error scale. -/
def alignedChildCenter {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name) :
    CenterState child :=
  (alignRight parent child parentCenter coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive).childCenter

/-- The selected child coefficient satisfies exactly the combined
parent--child allowance used by `CompatibleConstantPathRefinement`. -/
theorem alignedChildCenter_error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((alignedChildCenter parent child parentCenter coefficientEquivalent).value -
          parentCenter.value) <=
      CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel
          (alignedChildCenter parent child parentCenter
            coefficientEquivalent)) := by
  let alignment := alignRight parent child parentCenter coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive
  have close :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (alignment.childCenter.value - parentCenter.value) <
        4 * parent.modelErrorAllowance := by
    exact alignment.close.trans_eq (by ring1)
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (alignment.childCenter.value - parentCenter.value) <= _
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (alignment.childCenter.value - parentCenter.value) <=
      4 * parent.modelErrorAllowance := close.le
    _ <= 16 * parent.modelErrorAllowance :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        four_le_sixteen
          parent.modelErrorAllowance_positive.le
    _ <= 16 * parent.modelErrorAllowance +
        16 * parent.modelErrorAllowance :=
      le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          sixteen_nonnegative parent.modelErrorAllowance_positive.le)
    _ <= (16 * parent.modelErrorAllowance +
          16 * parent.modelErrorAllowance) +
        (16 * child.modelErrorAllowance +
          16 * child.modelErrorAllowance) :=
      le_add_of_nonneg_right
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            sixteen_nonnegative child.modelErrorAllowance_positive.le)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            sixteen_nonnegative child.modelErrorAllowance_positive.le))
    _ = CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel alignment.childCenter) := by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
      change (16 * parent.modelErrorAllowance +
            16 * parent.modelErrorAllowance) +
          (16 * child.modelErrorAllowance +
            16 * child.modelErrorAllowance) =
        2 * (16 * parent.modelErrorAllowance +
          16 * child.modelErrorAllowance)
      ring1

/-- A child aligned at an arbitrary parent parameter also satisfies the
combined model comparison allowance.  The parent contribution includes the
finite variation from its constant centre to the queried parameter. -/
theorem alignedChildAt_error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (parentCenter : CenterState parent)
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((alignedChildAt parent child query coefficientEquivalent).value -
          parentCenter.value) <=
      CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel
          (alignedChildAt parent child query coefficientEquivalent)) := by
  let alignment := alignQueryRight parent child query coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive
  have childQuery :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (alignment.childCenter.value - query.value) <=
        4 * parent.modelErrorAllowance :=
    alignment.close.trans_eq (by ring1) |>.le
  have queryParent :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (query.value - parentCenter.value) <=
        10 * parent.modelErrorAllowance :=
    (query.value_sub_center_lt parentCenter).le
  have identity : alignment.childCenter.value - parentCenter.value =
      (alignment.childCenter.value - query.value) +
        (query.value - parentCenter.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (alignment.childCenter.value - parentCenter.value) <= _
  rw [identity]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((alignment.childCenter.value - query.value) +
          (query.value - parentCenter.value)) <=
      2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            (alignment.childCenter.value - query.value) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (query.value - parentCenter.value)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ <= 2 * (4 * parent.modelErrorAllowance +
        10 * parent.modelErrorAllowance) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add childQuery queryParent) (by decide)
    _ = 2 * (14 * parent.modelErrorAllowance) := by ring1
    _ <= 2 * (16 * parent.modelErrorAllowance) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          fourteen_le_sixteen parent.modelErrorAllowance_positive.le)
        (by decide)
    _ <= 2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.mul_nonneg_direct sixteen_nonnegative
            child.modelErrorAllowance_positive.le)) (by decide)
    _ = CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel alignment.childCenter) := by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
      rfl

/-- Any two already selected parent and child centres satisfy the combined
parent--child comparison allowance when the child's base coefficient names
the coefficient at its starting parameter inside the parent.  Unlike
`alignedChildAt_error_le`, this theorem does not replace the child's centre:
it synchronizes finite tails of the two existing centre names and pays both
displayed semantic allowances. -/
theorem arbitraryChildAt_error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (parentCenter : CenterState parent)
    (childCenter : CenterState child)
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (childCenter.value - parentCenter.value) <=
      CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel childCenter) := by
  let target := parent.modelErrorAllowance + child.modelErrorAllowance
  have targetPositive : 0 < target :=
    add_pos parent.modelErrorAllowance_positive
      child.modelErrorAllowance_positive
  let centerEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      query.named childCenter.named :=
    CCL.OperationalEquivalence.NamedEquivalent.trans query.equivalent.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans coefficientEquivalent
        childCenter.equivalent)
  let comparison := centerEquivalent.compare 0 0 target targetPositive
  let queryLater := query.laterValue comparison.leftIndex
  let childLater := childCenter.laterValue comparison.rightIndex
  have laterClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (childLater - queryLater) < target := by
    have forward := comparison.close
      (Nat.le_refl comparison.leftIndex)
      (Nat.le_refl comparison.rightIndex)
    have reverse : childLater - queryLater = -(queryLater - childLater) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact forward
  have childTail :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (childCenter.value - childLater) < child.modelErrorAllowance := by
    have forward := childCenter.laterValue_sub_value_lt comparison.rightIndex
    have reverse : childCenter.value - childLater =
        -(childLater - childCenter.value) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact forward
  have childToQueryLater :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (childCenter.value - queryLater) <
        2 * (child.modelErrorAllowance + target) := by
    have identity : childCenter.value - queryLater =
        (childCenter.value - childLater) + (childLater - queryLater) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
    rw [identity]
    exact
      (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans_lt
        (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide)
          (RFAP.ConstructiveFraction.add_lt_add_direct childTail laterClose))
  have queryTail := query.laterValue_sub_value_lt comparison.leftIndex
  have childToQuery :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (childCenter.value - query.value) <
        2 * (2 * (child.modelErrorAllowance + target) +
          parent.modelErrorAllowance) := by
    have identity : childCenter.value - query.value =
        (childCenter.value - queryLater) + (queryLater - query.value) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
    rw [identity]
    exact
      (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans_lt
        (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide)
          (RFAP.ConstructiveFraction.add_lt_add_direct childToQueryLater
            queryTail))
  have queryToParent := query.value_sub_center_lt parentCenter
  have identity : childCenter.value - parentCenter.value =
      (childCenter.value - query.value) +
        (query.value - parentCenter.value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [identity]
  apply le_trans
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _)
  apply le_trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add childToQuery.le queryToParent.le) (by decide))
  unfold target
  change
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) <=
      CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel childCenter)
  unfold CCL.ProgressiveGaussianIntegration.PathModel.parentChildAllowance
    centeredModel
  change
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) <=
      2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance)
  have childPart : 16 * child.modelErrorAllowance <=
      32 * child.modelErrorAllowance := by
    calc
      16 * child.modelErrorAllowance <=
          16 * child.modelErrorAllowance +
            16 * child.modelErrorAllowance :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.mul_nonneg_direct sixteen_nonnegative
            child.modelErrorAllowance_positive.le)
      _ = 32 * child.modelErrorAllowance := by ring1
  calc
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) =
      32 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance := by ring1
    _ <= 32 * parent.modelErrorAllowance +
        32 * child.modelErrorAllowance := add_le_add le_rfl childPart
    _ = 2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance) := by ring1

/-- One already centred prepared child whose left endpoint occurs at a
displayed parameter of a centred prepared parent.  The operational
equivalence is the only analytic relation required by a finite geometric
partition. -/
structure CenteredChildAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : PreparedEdge curve differential)
    (parentCenter : CenterState parent) where
  child : PreparedEdge curve differential
  center : CenterState child
  fraction : Coordinate
  inside : (0 : Coordinate) <= fraction ∧ fraction <= 1
  query : QueryState parent fraction inside
  coefficientEquivalent :
    CCL.OperationalEquivalence.NamedEquivalent
      (parent.coefficient fraction inside).name
      (child.coefficient 0 child.baseInside).name

namespace CenteredChildAt

/-- Build the differential-level child comparison from the
differential-independent sheet-root equivalence at its common point. -/
def ofRootEquivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (childCenter : CenterState child)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (point_eq : parent.point fraction = child.point 0)
    (rootEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (parent.rootName fraction inside)
        (child.rootName 0 child.baseInside)) :
    CenteredChildAt parent parentCenter where
  child := child
  center := childCenter
  fraction := fraction
  inside := inside
  query := QueryState.canonical parent fraction inside
  coefficientEquivalent :=
    coefficientEquivalent_of_rootEquivalent parent child fraction inside
      point_eq rootEquivalent

/-- The actual constant cell selected by this child. -/
def model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) : CellModel :=
  child.child.centeredModel child.center

/-- The displayed child-minus-parent coefficient error. -/
def error {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) : Gaussian :=
  child.center.value - parentCenter.value

/-- The two-sided centre comparison proves exactly the local allowance of the
comparison view used by a compatible path refinement. -/
theorem error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq child.error <=
      (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
        (parent.centeredModel parentCenter) child.model).localAllowance := by
  simpa only [error, model,
    CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell,
    CCL.ProgressiveGaussianIntegration.CellModel.withAllowance] using
      arbitraryChildAt_error_le parent child.child parentCenter child.center
        child.query child.coefficientEquivalent

/-- Cellwise constant comparison for a complete displayed child block. -/
def comparison {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent} :
    (children : List (CenteredChildAt parent parentCenter)) ->
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantComparison
        parentCenter.value
        (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
          (parent.centeredModel parentCenter)
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (children.map model))).cells
        (children.map error)
  | [] => .nil
  | child :: remaining =>
      .cons child.center.value child.error rfl rfl child.error_le
        (comparison remaining)

/-- Comparison views retain the exact displacement sum of the actual child
cells. -/
theorem displacementSum_comparison {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent} :
    forall children : List (CenteredChildAt parent parentCenter),
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
            (parent.centeredModel parentCenter)
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (children.map model))).cells =
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (children.map model)
  | [] => rfl
  | child :: remaining => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.comparisonCell
            (parent.centeredModel parentCenter) child.model).displacement +
            CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
              (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
                (parent.centeredModel parentCenter)
                (CCL.ProgressiveGaussianIntegration.PathModel.mk
                  (remaining.map model))).cells =
          child.model.displacement +
            CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
              (remaining.map model)
      rw [displacementSum_comparison remaining]
      rfl

/-- Turn a geometric displacement partition into the exact head certificate
required by `CompatibleConstantPathRefinement`. -/
def partitionCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (children : List (CenteredChildAt parent parentCenter))
    (displacement_eq :
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (children.map model) =
        (parent.centeredModel parentCenter).displacement) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      (parent.centeredModel parentCenter)
      (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
        (parent.centeredModel parentCenter)
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (children.map model))) where
  reference := parentCenter.value
  parent_polynomial_eq := rfl
  errors := children.map error
  comparison := comparison children
  displacement_eq := by
    rw [displacementSum_comparison children]
    exact displacement_eq

/-- A child block that follows any lifted path with the parent's displayed
endpoints automatically has the exact displacement needed by the partition
certificate. -/
def partitionCertificateOfFollowedBy {genus sheets : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (children : List (CenteredChildAt parent parentCenter))
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint sheets}
    {path : CCL.Riemann.LiftedPaths.LiftedPath sheets start finish}
    (follows : CCL.Riemann.LiftedPaths.LiftedPath.FollowedBy
      (children.map model) path)
    (start_eq : (parent.centeredModel parentCenter).start = start.coordinate)
    (finish_eq : (parent.centeredModel parentCenter).finish =
      finish.coordinate) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      (parent.centeredModel parentCenter)
      (CCL.ProgressiveGaussianIntegration.PathModel.comparisonBlock
        (parent.centeredModel parentCenter)
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (children.map model))) :=
  partitionCertificate children (by
    rw [CCL.Riemann.LiftedPaths.LiftedPath.followedBy_displacementSum follows]
    unfold CCL.ProgressiveGaussianIntegration.CellModel.displacement
    rw [start_eq, finish_eq])

end CenteredChildAt

/-- A prepared parent list together with an ordered decomposition of every
parent into already centred child blocks.  Each child block carries only its
common-point root equivalences and exact finite displacement identity. -/
inductive CenteredPathRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    List CellModel -> List CellModel -> Type
  | nil : CenteredPathRefinement [] []
  | cons
      (parent : PreparedEdge curve differential)
      (parentCenter : CenterState parent)
      {parents children : List CellModel}
      (childBlock : List (CenteredChildAt parent parentCenter))
      (displacement_eq :
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
            (childBlock.map CenteredChildAt.model) =
          (parent.centeredModel parentCenter).displacement)
      (remaining : CenteredPathRefinement
        (curve := curve) (differential := differential) parents children) :
      CenteredPathRefinement
        (parent.centeredModel parentCenter :: parents)
        (childBlock.map CenteredChildAt.model ++ children)

namespace CenteredPathRefinement

/-- Forget the prepared root provenance after constructing the exact
comparison-aware constant path refinement required by the integration
kernel. -/
def toCompatible {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents children : List CellModel},
      CenteredPathRefinement
          (curve := curve) (differential := differential) parents children ->
        CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
          parents children
  | [], [], .nil => .nil
  | _, _, .cons parent parentCenter childBlock displacement_eq remaining =>
      .cons
        (CenteredChildAt.partitionCertificate childBlock displacement_eq)
        (toCompatible remaining)

end CenteredPathRefinement

def observation {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveGaussianIntegration.LocalObservation
      prepared.model.polynomial prepared.model.localAllowance where
  parameter := fraction
  integrandReading := prepared.reading fraction inside
  error := prepared.reading fraction inside - prepared.baseReading
  decomposition := by
    change prepared.reading fraction inside -
        CCL.FiniteGaussianPolynomial.eval
          (CCL.FiniteGaussianPolynomial.constant prepared.baseReading)
            ⟨fraction, 0⟩ =
      prepared.reading fraction inside - prepared.baseReading
    rw [CCL.FiniteGaussianPolynomial.eval_constant]
  error_le := by
    exact (prepared.reading_difference_le fraction inside).trans
      (by
        change prepared.modelErrorAllowance <=
          4 * prepared.modelErrorAllowance
        simpa only [RFAP.ConstructiveFraction.one_mul] using
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (show (1 : Coordinate) <= 4 by decide)
            prepared.modelErrorAllowance_positive.le)

def centeredObservation {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.ProgressiveGaussianIntegration.LocalObservation
      (prepared.centeredModel center).polynomial
      (prepared.centeredModel center).localAllowance where
  parameter := fraction
  integrandReading := prepared.reading fraction inside
  error := prepared.reading fraction inside - center.value
  decomposition := by
    change prepared.reading fraction inside -
        CCL.FiniteGaussianPolynomial.eval
          (CCL.FiniteGaussianPolynomial.constant center.value)
            ⟨fraction, 0⟩ =
      prepared.reading fraction inside - center.value
    rw [CCL.FiniteGaussianPolynomial.eval_constant]
  error_le := by
    exact (center.reading_sub_value_le fraction inside).trans
      (by
        change 4 * prepared.modelErrorAllowance <=
          16 * prepared.modelErrorAllowance
        exact
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            four_le_sixteen
              prepared.modelErrorAllowance_positive.le)

/-- The shrinking constant model has productive uniform algebraic semantics
at every rational parameter of the accepted edge. -/
def uniformCertificate {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (prepared : PreparedEdge curve differential) :
    UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      prepared.model where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let localObservation := prepared.observation fraction inside
    let localSheetValue := prepared.sheetValue fraction inside
    let localCoefficient := prepared.coefficient fraction inside
    let localState := prepared.readingState fraction inside
    let localReading := prepared.reading fraction inside
    let algebraic : AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
        prepared.model localObservation :=
      { point := prepared.point fraction
        point_eq := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [observationPoint, localObservation, observation, model,
              CCL.ProgressiveGaussianIntegration.CellModel.displacement,
              point, CCL.Riemann.BranchCuts.ClearSegment.pointAt,
              CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1
        sheetValue := localSheetValue
        chosenSheet_eq := rfl
        readingState := localState
        readingPossible := prepared.reading_possible fraction inside }
    exact
      { observation := localObservation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := localCoefficient.name.process.ball localState
          have radiusSmall : ball.radiusSq < prepared.readingTarget :=
            prepared.reading_radius_lt fraction inside
          have errorBound :
              RFAP.ConstructiveGaussian.Gaussian.normSq
                  (localReading - prepared.baseReading) <=
                prepared.modelErrorAllowance :=
            prepared.reading_difference_le fraction inside
          change 2 * (4 * ball.radiusSq +
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (localReading - prepared.baseReading)) <=
            4 * prepared.modelErrorAllowance
          calc
            2 * (4 * ball.radiusSq +
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  (localReading - prepared.baseReading)) <=
              2 * (4 * prepared.readingTarget +
                prepared.modelErrorAllowance) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) errorBound) (by decide)
            _ = 3 * prepared.modelErrorAllowance := by
              unfold readingTarget
              calc
                2 * (4 * (prepared.modelErrorAllowance / 8) +
                    prepared.modelErrorAllowance) =
                  (prepared.modelErrorAllowance / 8) * 8 +
                    prepared.modelErrorAllowance * 2 := by ring1
                _ = prepared.modelErrorAllowance +
                    prepared.modelErrorAllowance * 2 := by
                  rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 8
                    (by decide)]
                _ = 3 * prepared.modelErrorAllowance := by ring1
            _ <= 4 * prepared.modelErrorAllowance :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                (by decide) prepared.modelErrorAllowance_positive.le }

/-- Uniform algebraic semantics are preserved when the constant polynomial
is recentered at any finitely persisted base-point coefficient state. -/
def centeredUniformCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) :
    UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      (prepared.centeredModel center) where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let localObservation :=
      prepared.centeredObservation center fraction inside
    let localSheetValue := prepared.sheetValue fraction inside
    let localCoefficient := prepared.coefficient fraction inside
    let localState := prepared.readingState fraction inside
    let localReading := prepared.reading fraction inside
    let algebraic : AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
        (prepared.centeredModel center) localObservation :=
      { point := prepared.point fraction
        point_eq := by
          change prepared.point fraction =
            prepared.point 0 + CCL.FiniteExp.scale fraction
              ((prepared.point 1) - prepared.point 0)
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [point,
              CCL.Riemann.BranchCuts.ClearSegment.pointAt,
              CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1
        sheetValue := localSheetValue
        chosenSheet_eq := rfl
        readingState := localState
        readingPossible := prepared.reading_possible fraction inside }
    exact
      { observation := localObservation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := localCoefficient.name.process.ball localState
          have radiusSmall : ball.radiusSq < prepared.readingTarget :=
            prepared.reading_radius_lt fraction inside
          have errorBound :
              RFAP.ConstructiveGaussian.Gaussian.normSq
                  (localReading - center.value) <=
                4 * prepared.modelErrorAllowance :=
            center.reading_sub_value_le fraction inside
          change 2 * (4 * ball.radiusSq +
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (localReading - center.value)) <=
            16 * prepared.modelErrorAllowance
          calc
            2 * (4 * ball.radiusSq +
                RFAP.ConstructiveGaussian.Gaussian.normSq
                  (localReading - center.value)) <=
              2 * (4 * prepared.readingTarget +
                4 * prepared.modelErrorAllowance) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) errorBound) (by decide)
            _ = 9 * prepared.modelErrorAllowance := by
              unfold readingTarget
              calc
                2 * (4 * (prepared.modelErrorAllowance / 8) +
                    4 * prepared.modelErrorAllowance) =
                  (prepared.modelErrorAllowance / 8) * 8 +
                    prepared.modelErrorAllowance * 8 := by ring1
                _ = prepared.modelErrorAllowance +
                    prepared.modelErrorAllowance * 8 := by
                  rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 8
                    (by decide)]
                _ = 9 * prepared.modelErrorAllowance := by ring1
            _ <= 16 * prepared.modelErrorAllowance :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                nine_le_sixteen
                  prepared.modelErrorAllowance_positive.le }

def validCertificate {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (prepared : PreparedEdge curve differential) :
    ValidCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      prepared.model :=
  .uniform (uniformCertificate curve differential prepared)

def centeredValidCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) :
    ValidCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      (prepared.centeredModel center) :=
  .uniform (centeredUniformCertificate curve differential prepared center)

end PreparedEdge

end CCL.Riemann.PreparedConstantModels
