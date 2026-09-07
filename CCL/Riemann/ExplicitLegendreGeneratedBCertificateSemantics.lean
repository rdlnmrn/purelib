import CCL.Riemann.GeneratedLegendreBCertificateSemantics
import CCL.Riemann.ExplicitLegendrePreparedPeriods
import CCL.Riemann.GeneratedCycleProvenance

/-!
# Intended-sheet semantics of the generated Legendre certificate

The integer certificate begins with a small winding-one square at the lower
left anchor of the standard B-cycle.  This module proves that the square is
strictly inside the explicit sheet-zero owner already used by the canonical
prepared period construction.  Together with the checked inter-cell bridges,
this prevents the external generator from silently choosing the opposite
square-root sheet.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedLegendreBCertificateData
open CCL.Riemann.ExplicitLegendrePreparedPeriods

/-- Endpoint-retaining packaging of one dyadic parameter edge in a canonical
clear segment.  Keeping the parent segment is essential: `variationBound`
uses its affine polynomial together with the small dyadic endpoint factor.
Replacing the edge by a freshly restricted whole segment would discard that
factor and replace every local bound by the global floor `1`. -/
structure GeneratedParameterEdgePackage where
  ambient : RFAP.Boxes.Box
  start : RFAP.ConstructiveGaussian.Gaussian
  finish : RFAP.ConstructiveGaussian.Gaussian
  segment : CCL.Riemann.BranchCuts.ClearSegment
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
    ambient start finish
  within : segment.WithinAmbient
  edge : CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge
  depth : Nat
  variation_eq :
    CCL.Riemann.ClearSheetContinuation.variationBound segment
        edge.left.parameter edge.right.parameter =
      CCL.Riemann.ClearSheetContinuation.Subdivision.quarterVariation depth
        (CCL.Riemann.ClearSheetContinuation.variationBound segment 0 1)

/-- One actual working-path segment together with the dyadic depth used by
its inner prepared bank.  Retaining the outer subdivision is essential:
`variationBound` is computed on this segment, rather than on the much longer
raw leg from which it came. -/
structure GeneratedLegPackage where
  ambient : RFAP.Boxes.Box
  start : RFAP.ConstructiveGaussian.Gaussian
  finish : RFAP.ConstructiveGaussian.Gaussian
  segment : CCL.Riemann.BranchCuts.ClearSegment
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
    ambient start finish
  within : segment.WithinAmbient
  depth : Nat

/-- Pair each working clear-path segment with its inner bank depth. -/
def generatedLegPackages {ambient : RFAP.Boxes.Box} :
    {start finish : RFAP.ConstructiveGaussian.Gaussian} ->
    (path : CCL.Riemann.BranchCuts.ClearPath
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
      ambient start finish) ->
    path.WithinAmbient -> List Nat -> List GeneratedLegPackage
  | _, _, .nil _, _, _ => []
  | _, _, .cons head tail, within, [] =>
      { ambient := ambient
        start := _
        finish := _
        segment := head
        within := within.head
        depth := 0 } ::
      generatedLegPackages tail within.tail []
  | _, _, .cons head tail, within, depth :: depths =>
      { ambient := ambient
        start := _
        finish := _
        segment := head
        within := within.head
        depth := depth } ::
      generatedLegPackages tail within.tail depths

@[simp] theorem generatedLegPackages_length {ambient : RFAP.Boxes.Box} :
    {start finish : RFAP.ConstructiveGaussian.Gaussian} ->
    (path : CCL.Riemann.BranchCuts.ClearPath
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
      ambient start finish) ->
    (within : path.WithinAmbient) -> (depths : List Nat) ->
      (generatedLegPackages path within depths).length = path.segmentCount
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons _ tail, within, [] => by
      simp only [generatedLegPackages,
        CCL.Riemann.BranchCuts.ClearPath.segmentCount, List.length_cons,
        generatedLegPackages_length tail within.tail []]
  | _, _, .cons _ tail, within, _ :: depths => by
      simp only [generatedLegPackages,
        CCL.Riemann.BranchCuts.ClearPath.segmentCount, List.length_cons,
        generatedLegPackages_length tail within.tail depths]

/-- The 34 actual directed working segments, in the exact order used by the
prepared B-cycle banks. -/
def generatedBLegs : List GeneratedLegPackage :=
  generatedLegPackages workingBConnector
      workingBConnector_withinAmbient
      (List.replicate workingBConnector.segmentCount
        bConnectorInnerDepth) ++
    generatedLegPackages workingBBackwardConnector
      workingBBackwardConnector_withinAmbient
      (List.replicate workingBBackwardConnector.segmentCount
        bConnectorInnerDepth)

theorem generatedBLegs_length : generatedBLegs.length = 34 := by
  simp only [generatedBLegs, List.length_append,
    generatedLegPackages_length]
  decide +revert

/-- Working-segment index for a global generated row. -/
def generatedWorkingSegmentOfPosition (position : Nat) : Nat :=
  position / 8

/-- Global row offset of one working segment. -/
def generatedWorkingSegmentOffset (segment : Nat) : Nat :=
  segment * 8

/-- Inner dyadic depth of the working bank containing one generated row. -/
def generatedInnerDepthOfPosition (_position : Nat) : Nat :=
  bConnectorInnerDepth

/-- Small positional evidence selecting one working segment and one local
dyadic edge.  These two inequalities are emitted per row, keeping the generic
lookup free of a 272-way arithmetic case split. -/
structure GeneratedCellLocation (data : CompactCellData) where
  legIndex : Fin generatedBLegs.length
  legIndex_eq :
    legIndex.val = generatedWorkingSegmentOfPosition data.position
  localWithin :
    data.position - generatedWorkingSegmentOffset
        (generatedWorkingSegmentOfPosition data.position) <
      2 ^ generatedInnerDepthOfPosition data.position

/-- The actual working segment containing one generated row. -/
def generatedLegAt
    {data : CompactCellData}
    (location : GeneratedCellLocation data) : GeneratedLegPackage :=
  generatedBLegs.get location.legIndex

/-- Constant-depth lookup of the canonical fine edge named by one generated
row.  The only list traversal left is within a single dyadic leg (at most
512 cells), which stays inside Lean's ordinary recursion limit. -/
def generatedBMeshEdgeAt
    {data : CompactCellData}
    (location : GeneratedCellLocation data) :
    GeneratedParameterEdgePackage := by
  let leg := generatedLegAt location
  let localIndex := data.position - generatedWorkingSegmentOffset
    (generatedWorkingSegmentOfPosition data.position)
  exact
    { ambient := leg.ambient
      start := leg.start
      finish := leg.finish
      segment := leg.segment
      within := leg.within
      edge := CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt
        (generatedInnerDepthOfPosition data.position)
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint
            ⟨localIndex, location.localWithin⟩
      depth := generatedInnerDepthOfPosition data.position
      variation_eq :=
        CCL.Riemann.ClearSheetContinuation.Subdivision.variationBound_dyadicEdgeAt
          leg.segment
            (generatedInnerDepthOfPosition data.position)
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
            ⟨localIndex, location.localWithin⟩ }

/-- The parent-segment variation written only in terms of its two endpoints.
`ClearSheetContinuation.segmentPolynomial` deliberately ignores the clearance
proof object, so this is the exact parent calculation without forcing Lean to
unfold the generated refined-path lookup. -/
def endpointVariationBound
    (start finish : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.ConstructiveFraction.Rational :=
  RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
        start (finish - start))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient *
    ((0 : RFAP.ConstructiveFraction.Rational) - 1) ^ 2

/-- Segment-level arithmetic shared by every fine edge in one working
segment.  The endpoint-only formulation is an elaboration boundary: generated
checks never unfold the 76-entry refined-path lookup. -/
structure GeneratedLegCertificate where
  start : RFAP.ConstructiveGaussian.Gaussian
  finish : RFAP.ConstructiveGaussian.Gaussian
  coefficients : List RFAP.ConstructiveGaussian.Gaussian
  coefficients_eq :
    (RFAP.PathPolynomial.composeLine
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
      start (finish - start)).coeffs = coefficients
  finalBounds : RFAP.PolynomialBounds.HornerNormBounds
  finalBounds_eq :
    coefficients.foldl
      (RFAP.PolynomialBounds.HornerNormBounds.step 2) ⟨0, 0⟩ = finalBounds
  variation : RFAP.ConstructiveFraction.Rational
  variation_le :
    max 1 finalBounds.slope *
        ((0 : RFAP.ConstructiveFraction.Rational) - 1) ^ 2 <=
      variation

theorem parameterAmbient_normSqBound :
    CCL.Riemann.ClearSheetContinuation.parameterAmbient.normSqBound = 2 := by
  decide +revert

theorem GeneratedLegCertificate.endpointVariationBound_le
    (certificate : GeneratedLegCertificate) :
    endpointVariationBound certificate.start certificate.finish <=
      certificate.variation := by
  unfold endpointVariationBound RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds
  rw [certificate.coefficients_eq, parameterAmbient_normSqBound]
  rw [certificate.finalBounds_eq]
  exact certificate.variation_le

/-- Exact parent variation recovered from the cached final Horner bound.
Unlike `variation`, this value is not rounded upward: it is used only to
check segment-local arithmetic once at the 76-segment certificate boundary. -/
def GeneratedLegCertificate.exactVariation
    (certificate : GeneratedLegCertificate) :
    RFAP.ConstructiveFraction.Rational :=
  max 1 certificate.finalBounds.slope *
    ((0 : RFAP.ConstructiveFraction.Rational) - 1) ^ 2

theorem GeneratedLegCertificate.endpointVariationBound_eq
    (certificate : GeneratedLegCertificate) :
    endpointVariationBound certificate.start certificate.finish =
      certificate.exactVariation := by
  unfold endpointVariationBound RFAP.PolynomialBounds.denseLipschitzBound
    RFAP.PolynomialBounds.denseEvalNormLipschitzBound
    RFAP.PolynomialBounds.denseHornerNormBounds exactVariation
  rw [certificate.coefficients_eq, parameterAmbient_normSqBound]
  rw [certificate.finalBounds_eq]

/-- Every line in the explicit Legendre path carries the common runtime
clearance floor installed by `ExplicitLegendreLoopBaseBranches`. -/
def generatedPathClearanceFloor : RFAP.ConstructiveFraction.Rational :=
  CCL.Riemann.GeneratedLegendreBCertificateData.reducedRational
    1 262144 (by decide) 1 0 (by decide)

/-- The square-root derivative scan for the common path-clearance floor is
performed once, rather than once for every one of the 3,648 moving rows. -/
theorem generatedPathClearanceFloor_derivativeMarginLe :
    4 * CCL.FiniteGeometric.dyadicSquareRadius
        (generatedPathClearanceFloor / 4) <=
      (1 / 4 : RFAP.ConstructiveFraction.Rational) := by
  unfold generatedPathClearanceFloor
  decide +revert

/-- Endpoint-only presentation of the strengthened denominator floor.  This
is intentionally transparent: generated code checks it against one small
rational literal without unfolding the refined path that owns the segment. -/
def GeneratedLegCertificate.denominatorLower
    (certificate : GeneratedLegCertificate) :
    RFAP.ConstructiveFraction.Rational :=
  let radicandLower :=
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          certificate.start) / 2 - certificate.exactVariation
  let midpoint := certificate.start + CCL.FiniteExp.scale (1 / 2)
    (certificate.finish - certificate.start)
  let midpointLower :=
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          midpoint) / 2 - certificate.exactVariation / 4
  let localLower := max radicandLower midpointLower
  let coordinateLower := max
    (min 1 (generatedPathClearanceFloor / 4) / 8)
    ((CCL.FiniteGeometric.dyadicSquareRadius
      (generatedPathClearanceFloor / 2) / 2) / 8)
  let sampledMagnitude := if 0 < localLower then
    (CCL.FiniteGeometric.dyadicSquareRadius (localLower / 2) / 2) / 8
    else 0
  max (max coordinateLower (min 1 (radicandLower / 4) / 8))
    sampledMagnitude

/-- The endpoint cache computes the canonical strengthened denominator of
any segment to which it is bound.  This is the elaboration boundary that
keeps generated segment checks independent of the refined-path lookup. -/
theorem GeneratedLegCertificate.segmentDenominatorLower_eq
    (leg : GeneratedLegPackage) (certificate : GeneratedLegCertificate)
    (start_eq : leg.start = certificate.start)
    (finish_eq : leg.finish = certificate.finish)
    (clearance_eq : leg.segment.clearanceBound = generatedPathClearanceFloor) :
    CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
        leg.segment = certificate.denominatorLower := by
  have variation_eq :
      CCL.Riemann.ClearSheetContinuation.variationBound leg.segment 0 1 =
        certificate.exactVariation := by
    rw [CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz]
    change endpointVariationBound leg.start leg.finish = _
    rw [start_eq, finish_eq, certificate.endpointVariationBound_eq]
  have midpoint_eq : leg.segment.pointAt (1 / 2) =
      certificate.start + CCL.FiniteExp.scale (1 / 2)
        (certificate.finish - certificate.start) := by
    unfold CCL.Riemann.BranchCuts.ClearSegment.pointAt
    rw [start_eq, finish_eq]
  have startEvaluation_eq :
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          leg.start =
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          certificate.start :=
    congrArg
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
      start_eq
  unfold CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
    CCL.Riemann.PreparedDifferentialModels.denominatorLower
    CCL.Riemann.PreparedDifferentialModels.residualDenominatorLower
    CCL.Riemann.PreparedDifferentialModels.magnitudeDenominatorLower
    CCL.Riemann.PreparedDifferentialModels.segmentMagnitudeDenominatorLower
    GeneratedLegCertificate.denominatorLower
  unfold CCL.Riemann.PreparedDifferentialModels.segmentLocalRadicandNormLower
  unfold CCL.Riemann.PreparedDifferentialModels.segmentRadicandNormLower
    CCL.Riemann.PreparedDifferentialModels.segmentMidpointRadicandNormLower
  rw [clearance_eq, variation_eq,
    CCL.Riemann.BranchCuts.ClearSegment.pointAt_zero, startEvaluation_eq,
    midpoint_eq]
  rfl

/-- One inexpensive binding between an endpoint-only arithmetic cache and an
actual working-path segment.  Keeping this separate from the Horner trace
prevents either proof from unfolding the other calculation. -/
structure GeneratedLegBinding (leg : GeneratedLegPackage) where
  certificate : GeneratedLegCertificate
  start_eq : leg.start = certificate.start
  finish_eq : leg.finish = certificate.finish
  clearance_eq : leg.segment.clearanceBound = generatedPathClearanceFloor
  denominatorLower : RFAP.ConstructiveFraction.Rational
  denominatorLower_eq :
    CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
      leg.segment = denominatorLower

/-- A generated row tied to the identically indexed canonical B-mesh edge.
Only the two exact endpoint equalities are row-specific. -/
structure GeneratedCellGeometry
    {rootBits coefficientBits allowanceBits : Nat}
    (data : CompactCellData)
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) where
  location : GeneratedCellLocation data
  segmentBinding : GeneratedLegBinding (generatedLegAt location)
  cachedStart_eq :
    segmentBinding.certificate.start +
        CCL.FiniteExp.scale
          (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt
            (generatedInnerDepthOfPosition data.position)
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
            ⟨data.position - generatedWorkingSegmentOffset
                (generatedWorkingSegmentOfPosition data.position),
              location.localWithin⟩).left.parameter
          (segmentBinding.certificate.finish -
            segmentBinding.certificate.start) =
      data.startValue
  cachedFinish_eq :
    segmentBinding.certificate.start +
        CCL.FiniteExp.scale
          (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt
            (generatedInnerDepthOfPosition data.position)
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint
            ⟨data.position - generatedWorkingSegmentOffset
                (generatedWorkingSegmentOfPosition data.position),
              location.localWithin⟩).right.parameter
          (segmentBinding.certificate.finish -
            segmentBinding.certificate.start) =
      data.finishValue
  transportWithinThree :
    (-(3 : RFAP.ConstructiveFraction.Rational) <=
        (data.transportRootBox rootBits).xLower) ∧
      ((data.transportRootBox rootBits).xUpper <= 3) ∧
      (-(3 : RFAP.ConstructiveFraction.Rational) <=
        (data.transportRootBox rootBits).yLower) ∧
      ((data.transportRootBox rootBits).yUpper <= 3)
  narrowRefinesTransport :
    (data.rootBox rootBits).Refines (data.transportRootBox rootBits)
  cachedTransportCarries :
    CCL.Riemann.ClearSheetContinuation.Subdivision.quarterVariation
        (generatedInnerDepthOfPosition data.position)
        segmentBinding.certificate.variation <
      (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate /
        16

namespace GeneratedCellGeometry

/-- The inexpensive standalone dyadic edge used by the generated endpoint
checks.  It has the same parameters as the canonical edge but does not force
the refined-path segment lookup. -/
def cachedEdge
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :=
  CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt
    (generatedInnerDepthOfPosition data.position)
    CCL.Riemann.PreparedClearPathModels.zeroEndpoint
    CCL.Riemann.PreparedClearPathModels.oneEndpoint
    ⟨data.position - generatedWorkingSegmentOffset
        (generatedWorkingSegmentOfPosition data.position),
      geometry.location.localWithin⟩

/-- Reindex an executable root owner across a proved equality of parameters.
The equality is proof-only; the stored track is retained unchanged. -/
def reindexOwner
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (equal : left = right)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner right) :
    CCL.Riemann.SquareRootContinuationChain.Owner left := by
  cases equal
  exact owner

@[simp] theorem reindexOwner_initial_box
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (equal : left = right)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner right) :
    (reindexOwner equal owner).track.initial.box = owner.track.initial.box := by
  cases equal
  rfl

@[simp] theorem reindexOwner_initial_clearance_bound
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (equal : left = right)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner right) :
    (reindexOwner equal owner).track.initial.clearance.bound =
      owner.track.initial.clearance.bound := by
  cases equal
  rfl

def ambient
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) : RFAP.Boxes.Box :=
  (generatedBMeshEdgeAt geometry.location).ambient

def segment
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.BranchCuts.ClearSegment
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
      geometry.ambient (generatedBMeshEdgeAt geometry.location).start
        (generatedBMeshEdgeAt geometry.location).finish :=
  (generatedBMeshEdgeAt geometry.location).segment

def left
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :=
  (generatedBMeshEdgeAt geometry.location).edge.left

def right
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :=
  (generatedBMeshEdgeAt geometry.location).edge.right

theorem start_eq
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    geometry.segment.pointAt geometry.left.parameter = data.startValue := by
  change (generatedLegAt geometry.location).start +
      CCL.FiniteExp.scale geometry.cachedEdge.left.parameter
        ((generatedLegAt geometry.location).finish -
          (generatedLegAt geometry.location).start) = data.startValue
  rw [geometry.segmentBinding.start_eq, geometry.segmentBinding.finish_eq]
  exact geometry.cachedStart_eq

theorem finish_eq
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    geometry.segment.pointAt geometry.right.parameter = data.finishValue := by
  change (generatedLegAt geometry.location).start +
      CCL.FiniteExp.scale geometry.cachedEdge.right.parameter
        ((generatedLegAt geometry.location).finish -
          (generatedLegAt geometry.location).start) = data.finishValue
  rw [geometry.segmentBinding.start_eq, geometry.segmentBinding.finish_eq]
  exact geometry.cachedFinish_eq

theorem within
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    geometry.segment.WithinAmbient := by
  exact (generatedBMeshEdgeAt geometry.location).within

theorem derivativeMarginLe
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
        geometry.segment <=
      (1 / 4 : RFAP.ConstructiveFraction.Rational) := by
  unfold CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeThreshold
  have clearance :
      geometry.segment.clearanceBound = generatedPathClearanceFloor := by
    exact geometry.segmentBinding.clearance_eq
  rw [clearance]
  exact generatedPathClearanceFloor_derivativeMarginLe

theorem variationBound_eq_quarteredParent
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.ClearSheetContinuation.variationBound geometry.segment
        geometry.left.parameter geometry.right.parameter =
      CCL.Riemann.ClearSheetContinuation.Subdivision.quarterVariation
        (generatedInnerDepthOfPosition data.position)
          (CCL.Riemann.ClearSheetContinuation.variationBound
            geometry.segment 0 1) := by
  let edge := generatedBMeshEdgeAt geometry.location
  convert edge.variation_eq using 1 <;> congr 1

theorem parentVariationBound_le_cached
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.ClearSheetContinuation.variationBound geometry.segment 0 1 <=
      geometry.segmentBinding.certificate.variation := by
  rw [CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz]
  change endpointVariationBound
      (generatedBMeshEdgeAt geometry.location).start
      (generatedBMeshEdgeAt geometry.location).finish <=
    geometry.segmentBinding.certificate.variation
  change endpointVariationBound
      (generatedLegAt geometry.location).start
      (generatedLegAt geometry.location).finish <=
    geometry.segmentBinding.certificate.variation
  rw [geometry.segmentBinding.start_eq, geometry.segmentBinding.finish_eq]
  exact geometry.segmentBinding.certificate.endpointVariationBound_le

theorem variationBound_le_cachedVariation
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.ClearSheetContinuation.variationBound geometry.segment
        geometry.left.parameter geometry.right.parameter <=
      CCL.Riemann.ClearSheetContinuation.Subdivision.quarterVariation
        (generatedInnerDepthOfPosition data.position)
          geometry.segmentBinding.certificate.variation := by
  rw [geometry.variationBound_eq_quarteredParent]
  apply CCL.Riemann.ClearSheetContinuation.Subdivision.quarterVariation_mono
  exact geometry.parentVariationBound_le_cached

/-- The row's winding-one square, reindexed along the canonical segment's
definitionally equal starting point. -/
def rootOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        ((generatedBMeshEdgeAt geometry.location).segment.pointAt
          (generatedBMeshEdgeAt geometry.location).edge.left.parameter)) := by
  let generated := data.rootOwner bounds 0 (by decide) (by decide)
  apply reindexOwner _ generated
  calc
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        ((generatedBMeshEdgeAt geometry.location).segment.pointAt
          (generatedBMeshEdgeAt geometry.location).edge.left.parameter) =
        radicand ((generatedBMeshEdgeAt geometry.location).segment.pointAt
          (generatedBMeshEdgeAt geometry.location).edge.left.parameter) :=
      (CompactCellData.radicand_eq_baseCurve_eval _).symm
    _ = radicand data.startValue := congrArg radicand geometry.start_eq
    _ = radicand (data.parameterValue 0) := by
      rw [CompactCellData.parameterValue_zero]

/-- The wider source-only owner used to transport the selected occurrence
across the actual prepared subedge. -/
def transportRootOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds)
    (transportBounds :
      data.TransportBounds rootBits coefficientBits allowanceBits) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        (geometry.segment.pointAt geometry.left.parameter)) := by
  let generated := data.rootFactorizedSourceOwner transportBounds
  apply reindexOwner _ generated
  calc
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        (geometry.segment.pointAt geometry.left.parameter) =
        radicand (geometry.segment.pointAt geometry.left.parameter) :=
      (CompactCellData.radicand_eq_baseCurve_eval _).symm
    _ = radicand data.startValue := congrArg radicand geometry.start_eq
    _ = radicand (data.transportView.parameterValue 0) := by
      rw [CompactCellData.parameterValue_zero]
      rfl

@[simp] theorem rootOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    geometry.rootOwner.track.initial.box = data.rootBox rootBits := by
  unfold rootOwner
  rw [reindexOwner_initial_box, CompactCellData.rootOwner_initial_box]

/-- The narrow generated owner interpreted directly at the actual canonical
mesh point.  This avoids transporting a proof through the row's cached
rational endpoint equality when comparing coefficient processes. -/
def narrowSheetValue
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) (sheet : Fin 2) :
    CCL.Riemann.AlgebraicDifferentials.AlgebraicSheetValue
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      (geometry.segment.pointAt geometry.left.parameter) := by
  let owner := geometry.rootOwner
  let certificate := owner.certificate owner.parameterNonzero
  exact
    { value := certificate.value
      apart := certificate.apart
      sheet := sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans certificate.square
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
              (geometry.segment.pointAt geometry.left.parameter))) }

/-- Differential coefficient carried by the narrow generated occurrence at
the actual left endpoint. -/
@[irreducible] def narrowCoefficient
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) (sheet : Fin 2) :=
  let root := geometry.narrowSheetValue sheet
  CCL.Riemann.AlgebraicDifferentials.differentialValue
    CompactCellData.legendreDifferential
      (geometry.segment.pointAt geometry.left.parameter)
      root.value root.apart

/-- Every finite narrow-coefficient candidate receives the sharp reciprocal
error proved by the generated integer row. -/
theorem narrowCoefficient_candidate_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds)
    (sheet : Fin 2)
    (state : (geometry.narrowCoefficient sheet).name.process.State)
    {value : RFAP.ConstructiveGaussian.Gaussian}
    (possible : (geometry.narrowCoefficient sheet).name.process.Possible
      state value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (value - data.coefficientValue coefficientBits) <=
      (data.coefficientErrorSq allowanceBits).toCoordinate := by
  unfold narrowCoefficient at state possible
  let root := geometry.narrowSheetValue sheet
  rcases
      CCL.Riemann.AlgebraicDifferentials.differentialValue_possible_components
        CompactCellData.legendreDifferential
        (geometry.segment.pointAt geometry.left.parameter)
        root.value root.apart state possible with
    ⟨denominator, denominatorPossible, value_eq⟩
  have denominatorInside :
      (data.rootBox rootBits).Contains denominator := by
    have inside := geometry.rootOwner.certificate_candidate_in_initial_box
      geometry.rootOwner.parameterNonzero state.2 denominatorPossible
    simpa only [rootOwner_initial_box] using inside
  have reciprocalBound :=
    CompactCellData.coefficient_reciprocal_error_le bounds denominatorInside
  have value_eq_reciprocal : value = 1 / denominator := by
    simpa only [CompactCellData.legendreDifferential_exponent, pow_zero] using
      value_eq
  have errorIdentity :
      value - data.coefficientValue coefficientBits =
        -(data.coefficientValue coefficientBits - 1 / denominator) := by
    rw [value_eq_reciprocal]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
  rw [errorIdentity, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
  exact reciprocalBound

@[simp] theorem transportRootOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds)
    (transportBounds :
      data.TransportBounds rootBits coefficientBits allowanceBits) :
    (geometry.transportRootOwner transportBounds).track.initial.box =
      data.transportRootBox rootBits := by
  unfold transportRootOwner CompactCellData.transportRootBox
  rw [reindexOwner_initial_box,
    CompactCellData.rootFactorizedSourceOwner_initial_box]
  rfl

@[simp] theorem transportRootOwner_clearance_bound
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds)
    (transportBounds :
      data.TransportBounds rootBits coefficientBits allowanceBits) :
    (geometry.transportRootOwner transportBounds).track.initial.clearance.bound =
      (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate /
        16 := by
  unfold transportRootOwner
  rw [reindexOwner_initial_clearance_bound,
    CompactCellData.rootFactorizedSourceOwner_clearance_bound]

/-- A row-local squared root-diameter request, strictly larger than its
checked square's diagonal while remaining small enough for inexpensive
preparation reuse. -/
def rootDiameter
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (_geometry : GeneratedCellGeometry data bounds) :
    RFAP.ConstructiveFraction.Rational :=
  16 * data.transportHalfWidth ^ 2

theorem rootDiameter_positive
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    0 < geometry.rootDiameter :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (RFAP.ConstructiveFraction.pow_pos_direct
      data.transportView.halfWidth_positive 2)

def request
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
  (geometry : GeneratedCellGeometry data bounds) :
    CCL.Riemann.PreparedSheetContinuation.StepRequest :=
  { endpoint := (generatedBMeshEdgeAt geometry.location).edge.right
    rootDiameter := geometry.rootDiameter
    rootDiameterPositive := geometry.rootDiameter_positive }

@[simp] theorem request_endpoint
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    {bounds : data.Bounds rootBits coefficientBits allowanceBits}
    (geometry : GeneratedCellGeometry data bounds) :
    geometry.request.endpoint = geometry.right := by
  rfl

end GeneratedCellGeometry

/-- A checked arithmetic row together with its exact location in the
canonical prepared B-mesh.  Generated modules package these records in short
independently buildable lists, so clients can consume the geometry without
replaying any endpoint calculation. -/
structure GeometricCheckedCell
    (rootBits coefficientBits allowanceBits : Nat) where
  checked : CompactCheckedCell rootBits coefficientBits allowanceBits
  geometry : GeneratedCellGeometry checked.data checked.bounds

namespace GeometricCheckedCell

/-- The checked transport-only source owner, reindexed onto this row's actual
prepared segment. -/
def transportOwner
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :=
  cell.geometry.transportRootOwner cell.checked.transportBounds

theorem transportReady
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared
      cell.geometry.segment cell.geometry.left cell.transportOwner
        cell.geometry.request := by
  refine ⟨?_, ?_, ?_⟩
  · rw [transportOwner,
      GeneratedCellGeometry.transportRootOwner_initial_box]
    unfold CompactCellData.transportRootBox CompactCellData.rootBox
    rw [RFAP.AffineWinding.centeredSquare_diagonalSq]
    exact RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (by decide)
      (RFAP.ConstructiveFraction.pow_pos_direct
        cell.checked.data.transportView.halfWidth_positive 2)
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_transportFloor
        cell.geometry.segment cell.geometry.request.rootDiameter
          cell.geometry.request.rootDiameterPositive
            cell.geometry.derivativeMarginLe).trans (by
        simpa only [transportOwner,
          GeneratedCellGeometry.transportRootOwner_clearance_bound,
          CompactCellData.preparationClearanceFloor_toCoordinate] using
            cell.checked.transportBounds.preparationClearanceFloor_le)
  · rw [transportOwner,
      GeneratedCellGeometry.transportRootOwner_initial_box]
    change
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          cell.geometry.segment <=
            (cell.checked.data.transportRootBox rootBits).xLower ∧
        (cell.checked.data.transportRootBox rootBits).xUpper <=
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            cell.geometry.segment ∧
        -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          cell.geometry.segment <=
            (cell.checked.data.transportRootBox rootBits).yLower ∧
        (cell.checked.data.transportRootBox rootBits).yUpper <=
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            cell.geometry.segment
    have threeLe :=
      CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
        cell.geometry.segment
    exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        cell.geometry.transportWithinThree.1,
      cell.geometry.transportWithinThree.2.1.trans threeLe,
      (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        cell.geometry.transportWithinThree.2.2.1,
      cell.geometry.transportWithinThree.2.2.2.trans threeLe⟩

theorem transportCarries
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.Riemann.ClearSheetContinuation.variationBound
        cell.geometry.segment cell.geometry.left.parameter
          cell.geometry.right.parameter <
      cell.transportOwner.track.initial.clearance.bound := by
  simp only [transportOwner,
    GeneratedCellGeometry.transportRootOwner_clearance_bound]
  exact (cell.geometry.variationBound_le_cachedVariation).trans_lt
    cell.geometry.cachedTransportCarries

/-- Preparation recognizes the generated wide owner immediately; no fallback
search or reset is evaluated for this row. -/
theorem prepared_eq_transportOwner
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.Riemann.PreparedSheetContinuation.prepared
        cell.geometry.segment cell.geometry.left cell.transportOwner
          cell.geometry.request = cell.transportOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_eq_self_of_ready
    cell.geometry.segment cell.geometry.left cell.transportOwner
      cell.geometry.request cell.transportReady cell.transportCarries

/-- Sheet zero covers the forward connector and sheet one its reverse.  The
stationary switch cells are inserted only after these rows are assembled. -/
def sheet
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    Fin 2 :=
  if cell.checked.data.position < 136 then 0 else 1

/-- The actual prepared constant edge represented by one generated row.  Its
wide owner is cached verbatim, so constructing the edge never re-enters the
bounded preparation search. -/
@[irreducible] def preparedEdge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.Riemann.PreparedConstantModels.PreparedEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential where
  ambient := cell.geometry.ambient
  start := (generatedBMeshEdgeAt cell.geometry.location).start
  finish := (generatedBMeshEdgeAt cell.geometry.location).finish
  segment := cell.geometry.segment
  within := cell.geometry.within
  left := cell.geometry.left
  owner := cell.transportOwner
  request := cell.geometry.request
  cached :=
    { preparedOwner := cell.transportOwner
      preparedOwner_eq := cell.prepared_eq_transportOwner.symm }
  ordered :=
    CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt_ordered
      (generatedInnerDepthOfPosition cell.checked.data.position)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      CCL.Riemann.PreparedClearPathModels.oneEndpoint
      ⟨cell.checked.data.position - generatedWorkingSegmentOffset
          (generatedWorkingSegmentOfPosition cell.checked.data.position),
        cell.geometry.location.localWithin⟩ (by decide)
  small := by
    rw [cell.prepared_eq_transportOwner]
    exact cell.transportCarries
  sheet := cell.sheet

theorem preparedEdge_prepared_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (CCL.Riemann.PreparedSheetContinuation.prepared
      cell.preparedEdge.segment cell.preparedEdge.left cell.preparedEdge.owner
        cell.preparedEdge.request).track.initial.box =
      cell.checked.data.transportRootBox rootBits := by
  unfold GeometricCheckedCell.preparedEdge
  change (CCL.Riemann.PreparedSheetContinuation.prepared
      cell.geometry.segment cell.geometry.left cell.transportOwner
        cell.geometry.request).track.initial.box = _
  rw [cell.prepared_eq_transportOwner,
    GeometricCheckedCell.transportOwner,
    GeneratedCellGeometry.transportRootOwner_initial_box]

@[simp] theorem preparedEdge_point_zero
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.preparedEdge.point 0 =
      cell.geometry.segment.pointAt cell.geometry.left.parameter := by
  unfold preparedEdge
    CCL.Riemann.PreparedConstantModels.PreparedEdge.point
    CCL.Riemann.PreparedConstantModels.PreparedEdge.localSegment
    CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      cell.geometry.segment cell.geometry.within cell.geometry.left
        cell.geometry.request 0).symm

@[simp] theorem preparedEdge_point_one
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.preparedEdge.point 1 =
      cell.geometry.segment.pointAt
        cell.geometry.request.endpoint.parameter := by
  unfold preparedEdge
    CCL.Riemann.PreparedConstantModels.PreparedEdge.point
    CCL.Riemann.PreparedConstantModels.PreparedEdge.localSegment
    CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_one] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      cell.geometry.segment cell.geometry.within cell.geometry.left
        cell.geometry.request 1).symm

/-- Every prepared-edge coefficient candidate remains within the reciprocal
error checked on the generated transport square.  This avoids the expensive
generic narrow/prepared comparison: the cached prepared owner is literally
the generated transport owner, so denominator containment and the checked
reciprocal estimate suffice. -/
theorem preparedCoefficient_candidate_transport_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (fraction : RFAP.ConstructiveFraction.Rational)
    (inside : (0 : RFAP.ConstructiveFraction.Rational) <= fraction ∧
      fraction <= 1)
    (state : (cell.preparedEdge.coefficient fraction
      inside).name.process.State)
    {value : RFAP.ConstructiveGaussian.Gaussian}
    (possible : (cell.preparedEdge.coefficient fraction
      inside).name.process.Possible state value) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (value - cell.checked.data.coefficientValue coefficientBits) <=
      (cell.checked.data.transportCoefficientErrorSq
        allowanceBits).toCoordinate := by
  rcases
      CCL.Riemann.AlgebraicDifferentials.differentialValue_possible_components
        CompactCellData.legendreDifferential
        (cell.preparedEdge.point fraction)
        (cell.preparedEdge.sheetValue fraction inside).value
        (cell.preparedEdge.sheetValue fraction inside).apart
        state possible with
    ⟨denominator, denominatorPossible, value_eq⟩
  have denominatorInside :
      (cell.checked.data.transportRootBox rootBits).Contains denominator := by
    have inside := cell.preparedEdge.denominator_candidate_in_source
      fraction inside state.2 denominatorPossible
    rwa [cell.preparedEdge_prepared_initial_box] at inside
  have reciprocalBound :=
    CompactCellData.coefficient_reciprocal_error_le
      cell.checked.transportBounds.rootBounds denominatorInside
  have value_eq_reciprocal : value = 1 / denominator := by
    simpa only [CompactCellData.legendreDifferential_exponent, pow_zero] using
      value_eq
  have errorIdentity :
      value - cell.checked.data.coefficientValue coefficientBits =
        -(cell.checked.data.coefficientValue coefficientBits -
          1 / denominator) := by
    rw [value_eq_reciprocal]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
  rw [errorIdentity, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
  simpa only [CompactCellData.transportView_coefficientValue,
    CompactCellData.transportView_coefficientErrorSq] using reciprocalBound

/-- In particular, the persisted base centre used by the generated parent
model satisfies the same transport-square reciprocal bound. -/
theorem preparedCenter_transport_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (center : CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState
      cell.preparedEdge) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (center.value - cell.checked.data.coefficientValue coefficientBits) <=
      (cell.checked.data.transportCoefficientErrorSq
        allowanceBits).toCoordinate :=
  cell.preparedCoefficient_candidate_transport_error_le
    0 cell.preparedEdge.baseInside center.state center.value_possible

/-- Every finitely retained query value at an arbitrary rational point of the
generated parent edge remains in the externally checked reciprocal enclosure.
This is the quantitative anchor inherited by later direct children. -/
theorem preparedQuery_transport_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {fraction : RFAP.ConstructiveFraction.Rational}
    {inside : (0 : RFAP.ConstructiveFraction.Rational) <= fraction ∧
      fraction <= 1}
    (query : CCL.Riemann.PreparedConstantModels.PreparedEdge.QueryState
      cell.preparedEdge fraction inside) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (query.value - cell.checked.data.coefficientValue coefficientBits) <=
      (cell.checked.data.transportCoefficientErrorSq
        allowanceBits).toCoordinate :=
  cell.preparedCoefficient_candidate_transport_error_le
    fraction inside query.state query.value_possible

/-- Select a child centre by comparing it with an arbitrarily accurate query
of the generated parent occurrence.  The result is still an ordinary
persisted `CenterState`, so all existing prepared-model certificates apply. -/
def transportAlignedChildCenter
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (child : CCL.Riemann.PreparedConstantModels.PreparedEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)
    (fraction : RFAP.ConstructiveFraction.Rational)
    (inside : (0 : RFAP.ConstructiveFraction.Rational) <= fraction ∧
      fraction <= 1)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (cell.preparedEdge.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState child :=
  let query :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.TargetedQueryState.atTarget
      cell.preparedEdge fraction inside target targetPositive
  (CCL.Riemann.PreparedConstantModels.PreparedEdge.alignQueryRight
    cell.preparedEdge child query.query coefficientEquivalent target
      targetPositive).childCenter

/-- The aligned child pays only the caller-selected finite comparison target
on top of the generated transport-square error.  In particular, no coarse
parent model allowance appears in this estimate. -/
theorem transportAlignedChildCenter_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (child : CCL.Riemann.PreparedConstantModels.PreparedEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)
    (fraction : RFAP.ConstructiveFraction.Rational)
    (inside : (0 : RFAP.ConstructiveFraction.Rational) <= fraction ∧
      fraction <= 1)
    (coefficientEquivalent :
      CCL.OperationalEquivalence.NamedEquivalent
        (cell.preparedEdge.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((cell.transportAlignedChildCenter child fraction inside
          coefficientEquivalent target targetPositive).value -
            cell.checked.data.coefficientValue coefficientBits) <=
      2 * (10 * target +
        (cell.checked.data.transportCoefficientErrorSq
          allowanceBits).toCoordinate) := by
  let query :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.TargetedQueryState.atTarget
      cell.preparedEdge fraction inside target targetPositive
  let alignment :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.alignQueryRight
      cell.preparedEdge child query.query coefficientEquivalent target
        targetPositive
  have alignedError :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (alignment.childCenter.value - query.query.value) <
        10 * target := by
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (alignment.childCenter.value - query.query.value) <
          2 * (target +
            4 * ((cell.preparedEdge.coefficient fraction inside).name.process.ball
              query.query.state).radiusSq) := alignment.close_radius
      _ < 2 * (target + 4 * target) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide)
          (RFAP.ConstructiveFraction.add_lt_add_left_direct
            (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide) query.radius_lt_target) target)
      _ = 10 * target := by ring1
  have queryError := cell.preparedQuery_transport_error_le query.query
  have identity : alignment.childCenter.value -
      cell.checked.data.coefficientValue coefficientBits =
        (alignment.childCenter.value - query.query.value) +
          (query.query.value -
            cell.checked.data.coefficientValue coefficientBits) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (alignment.childCenter.value -
        cell.checked.data.coefficientValue coefficientBits) <= _
  rw [identity]
  exact
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add alignedError.le queryError) (by decide))

/-- Strict initial-box refinement preserves the selected root occurrence.
This track-level form keeps concrete prepared-path expressions out of the
operational proof. -/
private def trackRootEquivalent_of_initial_refines
    {parameter : RFAP.ConstructiveGaussian.Gaussian}
    (parameterNonzero : parameter ≠ 0)
    {narrowAmbient transportAmbient : RFAP.Boxes.Box}
    (narrow : RFAP.ShrinkingTrack.WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) narrowAmbient)
    (transport : RFAP.ShrinkingTrack.WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) transportAmbient)
    (refines : narrow.initial.box.Refines transport.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero narrow).name
      (CCL.Riemann.CertifiedSquareRoot.root parameterNonzero transport).name := by
  let common : RFAP.ShrinkingTrack.WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter
        CCL.Riemann.SquareRootSheets.degreeTwo) narrowAmbient :=
    { initial := CCL.Riemann.CoherentRoot.state narrow 1
      refine := narrow.refine
      nested := narrow.nested
      strict := narrow.strict
      accurate := narrow.accurate }
  have commonStrictNarrow : common.initial.box.StrictInterior
      narrow.initial.box := by
    change (CCL.Riemann.CoherentRoot.state narrow 1).box.StrictInterior
      narrow.initial.box
    exact CCL.Riemann.SquareRootTrackEquivalence.state_strict_initial_of_pos
      narrow (by decide)
  have commonStrictTransport : common.initial.box.StrictInterior
      transport.initial.box :=
    commonStrictNarrow.trans_refines refines
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      parameterNonzero narrow common commonStrictNarrow)
    (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      parameterNonzero transport common commonStrictTransport).symm

/-- Owner-level wrapper around the track comparison.  At concrete call sites
this leaves only the owner index to unify, rather than the full winding-track
polynomial and ambient parameters. -/
private def ownerRootEquivalent_of_initial_refines
    {parameter : RFAP.ConstructiveGaussian.Gaussian}
    (narrow wide : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (refines : narrow.track.initial.box.Refines wide.track.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        wide.parameterNonzero narrow)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        wide.parameterNonzero wide) := by
  unfold CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
    CCL.Riemann.SquareRootContinuationChain.Owner.certificate
    CCL.Riemann.CertifiedSquareRoot.certificate
  exact trackRootEquivalent_of_initial_refines wide.parameterNonzero
    narrow.track wide.track refines

/-- The same comparison when the two owner indices are propositionally equal.
Keeping the equality explicit prevents concrete generated-path indices from
being normalized merely to type-check the comparison. -/
private def ownerRootEquivalent_of_initial_refines_eq
    {narrowParameter wideParameter : RFAP.ConstructiveGaussian.Gaussian}
    (parameterEq : narrowParameter = wideParameter)
    (narrow : CCL.Riemann.SquareRootContinuationChain.Owner narrowParameter)
    (wide : CCL.Riemann.SquareRootContinuationChain.Owner wideParameter)
    (refines : narrow.track.initial.box.Refines wide.track.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        narrow.parameterNonzero narrow)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        wide.parameterNonzero wide) := by
  subst wideParameter
  cases Subsingleton.elim narrow.parameterNonzero wide.parameterNonzero
  exact ownerRootEquivalent_of_initial_refines narrow wide refines

/-- Compare two owners through separately cached descriptions of their
initial boxes.  This form is useful for generated examples: no proposition in
the caller's context contains both large dependent owner expressions. -/
private def ownerRootEquivalent_of_initial_boxes_eq
    {narrowParameter wideParameter : RFAP.ConstructiveGaussian.Gaussian}
    (parameterEq : narrowParameter = wideParameter)
    (narrow : CCL.Riemann.SquareRootContinuationChain.Owner narrowParameter)
    (wide : CCL.Riemann.SquareRootContinuationChain.Owner wideParameter)
    {narrowBox wideBox : RFAP.Boxes.Box}
    (narrowInitial : narrow.track.initial.box = narrowBox)
    (wideInitial : wide.track.initial.box = wideBox)
    (refines : narrowBox.Refines wideBox) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        narrow.parameterNonzero narrow)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        wide.parameterNonzero wide) := by
  apply ownerRootEquivalent_of_initial_refines_eq parameterEq narrow wide
  rw [narrowInitial, wideInitial]
  exact refines

/-- Lightweight name of the narrow generated source occurrence.  The
irreducible boundary prevents later operational statements from normalizing
the concrete scheduled path merely to recover this name. -/
@[irreducible] def narrowOwnerName
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.ProgressiveTransducer.Named :=
  CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
    cell.geometry.rootOwner.parameterNonzero cell.geometry.rootOwner

/-- Lightweight name of the wider occurrence used by prepared transport. -/
@[irreducible] def transportOwnerName
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
  CCL.ProgressiveTransducer.Named :=
  CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
    cell.transportOwner.parameterNonzero cell.transportOwner

/-- The narrow and transport owners select the same source occurrence.  The
explicit parameter equality keeps the two dependent owner indices separate
until the small generic bridge has already been constructed. -/
def narrowRootEquivalentTransport
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.OperationalEquivalence.NamedEquivalent
      (narrowOwnerName cell) (transportOwnerName cell) := by
  have parameterEq :
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          ((generatedBMeshEdgeAt cell.geometry.location).segment.pointAt
            (generatedBMeshEdgeAt cell.geometry.location).edge.left.parameter) =
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          (cell.geometry.segment.pointAt cell.geometry.left.parameter) := by
    rfl
  unfold narrowOwnerName transportOwnerName
  apply ownerRootEquivalent_of_initial_boxes_eq parameterEq
    cell.geometry.rootOwner cell.transportOwner
    (narrowBox := cell.checked.data.rootBox rootBits)
    (wideBox := cell.checked.data.transportRootBox rootBits)
  · exact cell.geometry.rootOwner_initial_box
  · simp only [transportOwner,
      GeneratedCellGeometry.transportRootOwner_initial_box]
  · exact cell.geometry.narrowRefinesTransport

/-- Two productive names together with their finite operational comparison.
The small record boundary prevents the dependent prepared-edge expressions
from being normalized while later declarations elaborate their types. -/
private structure NamedBridge where
  first : CCL.ProgressiveTransducer.Named
  second : CCL.ProgressiveTransducer.Named
  equivalent : CCL.OperationalEquivalence.NamedEquivalent first second

/-- Operationally equivalent denominator names give equivalent differential
coefficients at equal displayed rational points.  Abstracting the points here
keeps concrete prepared-edge reductions out of the proof. -/
private def differentialValueBridgeAtEqualPoints {genus : Nat}
    (differential :
      CCL.Riemann.AlgebraicDifferentials.Differential genus)
    (firstPoint secondPoint : RFAP.ConstructiveGaussian.Gaussian)
    (point_eq : firstPoint = secondPoint)
    (firstRoot secondRoot : CCL.ProgressiveCoherence.CoherentNamed)
    (firstApart : CCL.ProgressiveTransducer.Named.Apart firstRoot.name)
    (secondApart : CCL.ProgressiveTransducer.Named.Apart secondRoot.name)
    (rootEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      firstRoot.name secondRoot.name) : NamedBridge := by
  cases point_eq
  exact
    { first := (CCL.Riemann.AlgebraicDifferentials.differentialValue
        differential firstPoint firstRoot firstApart).name
      second := (CCL.Riemann.AlgebraicDifferentials.differentialValue
        differential firstPoint secondRoot secondApart).name
      equivalent :=
        CCL.Riemann.AlgebraicDifferentials.differentialValue_respects_sheet
          differential firstPoint firstRoot secondRoot firstApart secondApart
            rootEquivalent }

private theorem differentialValueBridgeAtEqualPoints_first {genus : Nat}
    (differential :
      CCL.Riemann.AlgebraicDifferentials.Differential genus)
    (firstPoint secondPoint : RFAP.ConstructiveGaussian.Gaussian)
    (point_eq : firstPoint = secondPoint)
    (firstRoot secondRoot : CCL.ProgressiveCoherence.CoherentNamed)
    (firstApart : CCL.ProgressiveTransducer.Named.Apart firstRoot.name)
    (secondApart : CCL.ProgressiveTransducer.Named.Apart secondRoot.name)
    (rootEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      firstRoot.name secondRoot.name) :
    (differentialValueBridgeAtEqualPoints differential firstPoint secondPoint
      point_eq firstRoot secondRoot firstApart secondApart
        rootEquivalent).first =
      (CCL.Riemann.AlgebraicDifferentials.differentialValue differential
        firstPoint firstRoot firstApart).name := by
  cases point_eq
  rfl

private theorem differentialValueBridgeAtEqualPoints_second {genus : Nat}
    (differential :
      CCL.Riemann.AlgebraicDifferentials.Differential genus)
    (firstPoint secondPoint : RFAP.ConstructiveGaussian.Gaussian)
    (point_eq : firstPoint = secondPoint)
    (firstRoot secondRoot : CCL.ProgressiveCoherence.CoherentNamed)
    (firstApart : CCL.ProgressiveTransducer.Named.Apart firstRoot.name)
    (secondApart : CCL.ProgressiveTransducer.Named.Apart secondRoot.name)
    (rootEquivalent : CCL.OperationalEquivalence.NamedEquivalent
      firstRoot.name secondRoot.name) :
    (differentialValueBridgeAtEqualPoints differential firstPoint secondPoint
      point_eq firstRoot secondRoot firstApart secondApart
        rootEquivalent).second =
      (CCL.Riemann.AlgebraicDifferentials.differentialValue differential
        secondPoint secondRoot secondApart).name := by
  cases point_eq
  rfl

/-- The generated narrow root and the wider owner used for actual transport
name the same operational square-root occurrence. -/
private def narrowRootBridge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    NamedBridge where
  first := narrowOwnerName cell
  second := transportOwnerName cell
  equivalent := narrowRootEquivalentTransport cell

/-- Lightweight name of the diameter-prepared source occurrence. -/
@[irreducible] private def preparedOwnerName
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.ProgressiveTransducer.Named :=
  cell.preparedEdge.preparedRootName

/-- Generic bridge from any explicitly boxed source owner to the prepared
source occurrence cached by one edge.  Keeping the dependent prepared-owner
term inside this generic declaration prevents concrete path data from being
normalized at call sites. -/
private def sourceRootEquivalent_preparedRoot {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {differential : CCL.Riemann.AlgebraicDifferentials.Differential genus}
    {sourceParameter : RFAP.ConstructiveGaussian.Gaussian}
    (source : CCL.Riemann.SquareRootContinuationChain.Owner sourceParameter)
    (edge : CCL.Riemann.PreparedConstantModels.PreparedEdge curve differential)
    (parameterEq : sourceParameter =
      curve.polynomial.eval (edge.segment.pointAt edge.left.parameter))
    {box : RFAP.Boxes.Box}
    (sourceInitial : source.track.initial.box = box)
    (preparedInitial :
      (CCL.Riemann.PreparedSheetContinuation.prepared edge.segment edge.left
        edge.owner edge.request).track.initial.box = box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        source.parameterNonzero source)
      edge.preparedRootName := by
  let preparedOwner := CCL.Riemann.PreparedSheetContinuation.prepared
    edge.segment edge.left edge.owner edge.request
  have equivalent := ownerRootEquivalent_of_initial_boxes_eq parameterEq
    source preparedOwner sourceInitial preparedInitial
      (RFAP.Boxes.Box.refines_refl box)
  unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedRootName
    CCL.Riemann.PreparedSheetContinuation.preparedRootName
  exact equivalent

/-- The generated transport owner and the diameter-prepared source owner name
the same occurrence.  Their parameters are related through the public
parameter-zero point theorem, and their initial boxes are compared through
the cached generated box certificates. -/
private def transportPreparedRootBridge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    NamedBridge := by
  have sourcePointEq :
      cell.geometry.segment.pointAt cell.geometry.left.parameter =
        cell.preparedEdge.segment.pointAt
          cell.preparedEdge.left.parameter := by
    calc
      cell.geometry.segment.pointAt cell.geometry.left.parameter =
          cell.preparedEdge.point 0 := cell.preparedEdge_point_zero.symm
      _ = cell.preparedEdge.segment.pointAt
          cell.preparedEdge.left.parameter :=
        cell.preparedEdge.point_zero_eq_source
  have parameterEq := congrArg
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
      sourcePointEq
  have transportInitial : cell.transportOwner.track.initial.box =
      cell.checked.data.transportRootBox rootBits := by
    simp only [transportOwner,
      GeneratedCellGeometry.transportRootOwner_initial_box]
  have equivalent := sourceRootEquivalent_preparedRoot cell.transportOwner
    cell.preparedEdge parameterEq transportInitial
      cell.preparedEdge_prepared_initial_box
  exact
    { first := transportOwnerName cell
      second := preparedOwnerName cell
      equivalent := by
        unfold transportOwnerName preparedOwnerName
        exact equivalent }

/-- The prepared source occurrence and the actual parameter-zero query,
packaged using the lightweight concrete source name. -/
private def preparedBaseRootBridge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    NamedBridge where
  first := preparedOwnerName cell
  second := cell.preparedEdge.rootName 0 cell.preparedEdge.baseInside
  equivalent := by
    unfold preparedOwnerName
    exact cell.preparedEdge.preparedRootEquivalent_baseQuery

/-- Compose three explicit operational transitions: narrow generated owner to
transport owner, transport owner to the prepared source, and prepared source
to its local-zero query.  No concrete prepared-edge field is normalized to
establish a definitional middle equality. -/
private def narrowPreparedRootBridge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    NamedBridge := by
  have transportPrepared := (transportPreparedRootBridge cell).equivalent
  change CCL.OperationalEquivalence.NamedEquivalent
    (transportOwnerName cell) (preparedOwnerName cell) at transportPrepared
  have preparedBase := (preparedBaseRootBridge cell).equivalent
  change CCL.OperationalEquivalence.NamedEquivalent
    (preparedOwnerName cell)
      (cell.preparedEdge.rootName 0 cell.preparedEdge.baseInside) at preparedBase
  exact
    { first := narrowOwnerName cell
      second := cell.preparedEdge.rootName 0 cell.preparedEdge.baseInside
      equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
        (narrowRootEquivalentTransport cell)
        (CCL.OperationalEquivalence.NamedEquivalent.trans transportPrepared
          preparedBase) }

private theorem narrowPreparedRootBridge_first
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (narrowPreparedRootBridge cell).first =
      (cell.geometry.narrowSheetValue cell.sheet).value.name := by
  unfold narrowPreparedRootBridge narrowOwnerName
    GeneratedCellGeometry.narrowSheetValue
  rfl

private theorem narrowPreparedRootBridge_second
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (narrowPreparedRootBridge cell).second =
      (cell.preparedEdge.sheetValue 0 cell.preparedEdge.baseInside).value.name := by
  unfold narrowPreparedRootBridge
    CCL.Riemann.PreparedConstantModels.PreparedEdge.rootName
    CCL.Riemann.PreparedConstantModels.PreparedEdge.sheetValue
    CCL.Riemann.PreparedDifferentialModels.sheetValueAtCached
  rfl

/-- The sharp generated coefficient and its actual prepared-edge coefficient,
packaged with the comparison and literal-error interface needed downstream. -/
private structure NarrowPreparedBridge
    {coefficientBits allowanceBits : Nat} (data : CompactCellData) where
  prepared :
    CCL.Riemann.PreparedConstantModels.PreparedEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential
  narrow : CCL.ProgressiveCoherence.CoherentNamed
  equivalent : CCL.OperationalEquivalence.NamedEquivalent narrow.name
    (prepared.coefficient 0 prepared.baseInside).name
  narrowError :
    ∀ (state : narrow.name.process.State)
      {value : RFAP.ConstructiveGaussian.Gaussian},
      narrow.name.process.Possible state value →
        RFAP.ConstructiveGaussian.Gaussian.normSq
            (value - data.coefficientValue coefficientBits) <=
          (data.coefficientErrorSq allowanceBits).toCoordinate
  start_eq : prepared.point 0 = data.startValue
  finish_eq : prepared.point 1 = data.finishValue

theorem preparedEdge_finish_eq
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.preparedEdge.point 1 = cell.checked.data.finishValue := by
  exact cell.preparedEdge_point_one.trans (by
    rw [cell.geometry.request_endpoint]
    exact cell.geometry.finish_eq)

/-- Build the narrow/prepared coefficient bridge without exposing either
large name in the declaration's result type. -/
private def narrowPreparedBridge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    NarrowPreparedBridge (coefficientBits := coefficientBits)
      (allowanceBits := allowanceBits) cell.checked.data where
  prepared := cell.preparedEdge
  narrow := cell.geometry.narrowCoefficient cell.sheet
  equivalent := by
    let roots := narrowPreparedRootBridge cell
    have rootEquivalent : CCL.OperationalEquivalence.NamedEquivalent
        (cell.geometry.narrowSheetValue cell.sheet).value.name
        (cell.preparedEdge.sheetValue 0 cell.preparedEdge.baseInside).value.name := by
      have equivalent := roots.equivalent
      rw [narrowPreparedRootBridge_first,
        narrowPreparedRootBridge_second] at equivalent
      exact equivalent
    let coefficients := differentialValueBridgeAtEqualPoints
      CompactCellData.legendreDifferential
      (cell.geometry.segment.pointAt cell.geometry.left.parameter)
      (cell.preparedEdge.point 0)
      cell.preparedEdge_point_zero.symm
      (cell.geometry.narrowSheetValue cell.sheet).value
      (cell.preparedEdge.sheetValue 0 cell.preparedEdge.baseInside).value
      (cell.geometry.narrowSheetValue cell.sheet).apart
      (cell.preparedEdge.sheetValue 0 cell.preparedEdge.baseInside).apart
      rootEquivalent
    have equivalent := coefficients.equivalent
    rw [differentialValueBridgeAtEqualPoints_first,
      differentialValueBridgeAtEqualPoints_second] at equivalent
    unfold GeneratedCellGeometry.narrowCoefficient
      CCL.Riemann.PreparedConstantModels.PreparedEdge.coefficient
      CCL.Riemann.PreparedDifferentialModels.coefficientAtCached
    exact equivalent
  narrowError := by
    intro state value possible
    exact cell.geometry.narrowCoefficient_candidate_error_le cell.sheet
      state possible
  start_eq := cell.preparedEdge_point_zero.trans cell.geometry.start_eq
  finish_eq := cell.preparedEdge_finish_eq

/-- Lightweight payload for one exact finite operational comparison.  The
prepared edge is stored rather than repeated as a dependent index, keeping
the 3,648 generated clients behind a small elaboration boundary. -/
structure LiteralCenterAlignment
    {coefficientBits allowanceBits : Nat} (data : CompactCellData) where
  prepared :
    CCL.Riemann.PreparedConstantModels.PreparedEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential
  center : CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState prepared
  narrowValue : RFAP.ConstructiveGaussian.Gaussian
  narrowError :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (narrowValue - data.coefficientValue coefficientBits) <=
      (data.coefficientErrorSq allowanceBits).toCoordinate
  close : RFAP.ConstructiveGaussian.Gaussian.normSq
      (narrowValue - center.value) <
    (data.coefficientErrorSq allowanceBits).toCoordinate
  start_eq : prepared.point 0 = data.startValue
  finish_eq : prepared.point 1 = data.finishValue

/-- Perform the comparison and centre selection for an abstract packaged
narrow/prepared pair.  The generated cell never unfolds while this finite
sampling program elaborates. -/
private def alignNarrowPrepared
    {coefficientBits allowanceBits : Nat} {data : CompactCellData}
    (bridge : NarrowPreparedBridge (coefficientBits := coefficientBits)
      (allowanceBits := allowanceBits) data)
    (errorPositive :
      0 < (data.coefficientErrorSq allowanceBits).toCoordinate) :
    LiteralCenterAlignment (coefficientBits := coefficientBits)
      (allowanceBits := allowanceBits) data := by
  let prepared := bridge.prepared
  let narrow := bridge.narrow
  let error := (data.coefficientErrorSq allowanceBits).toCoordinate
  let equivalent : CCL.OperationalEquivalence.NamedEquivalent narrow.name
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.baseNamed
        prepared) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      bridge.equivalent
      (CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.baseEquivalent
        prepared)
  let preparedStart :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.canonicalIndex
      prepared
  let comparison := equivalent.compare 0 preparedStart error errorPositive
  let narrowState := CCL.ProgressiveSampling.stateAt narrow.name.process
    narrow.name.state comparison.leftIndex
  let preparedState := CCL.ProgressiveSampling.stateAt
    (prepared.coefficient 0 prepared.baseInside).name.process
    (prepared.readingState 0 prepared.baseInside) comparison.rightIndex
  let center :
      CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState prepared :=
    CCL.Riemann.PreparedConstantModels.PreparedEdge.CenterState.ofState
      prepared preparedState
      (by
        intro value possible
        exact CCL.ProgressiveSampling.stateAt_possible_at_start
          (prepared.coefficient 0 prepared.baseInside).name.process
          (prepared.readingState 0 prepared.baseInside)
          comparison.rightIndex possible)
      (by
        have indexOrder : CCL.ProgressiveSampling.refinementTarget
            comparison.rightIndex <=
          CCL.ProgressiveSampling.refinementTarget preparedStart := by
          unfold CCL.ProgressiveSampling.refinementTarget
          exact CCL.FiniteGeometric.quarterRadius_antitone
            (by decide) comparison.right_ge
        exact
          ((CCL.ProgressiveSampling.stateAt_accurate
            (prepared.coefficient 0 prepared.baseInside).name.process
            (prepared.readingState 0 prepared.baseInside)
            comparison.rightIndex).trans_le indexOrder).trans
              (CCL.FiniteGeometric.firstQuarterBelow_accurate
                1 (by decide) 0 prepared.readingTarget
                  prepared.readingTarget_positive))
  let narrowValue := (narrow.name.process.witness narrowState).val
  exact
    { prepared := prepared
      center := center
      narrowValue := narrowValue
      narrowError :=
        bridge.narrowError narrowState
          (narrow.name.process.witness narrowState).property
      close := by
        exact comparison.close (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
      start_eq := bridge.start_eq
      finish_eq := bridge.finish_eq }

/-- Construct the aligned centre at a comparison-selected finite state.  The
prepared side starts beyond its canonical accuracy index, so the resulting
centre remains valid for the ordinary constant-model API. -/
def literalCenterAlignment
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    LiteralCenterAlignment (coefficientBits := coefficientBits)
      (allowanceBits := allowanceBits) cell.checked.data := by
  exact alignNarrowPrepared (narrowPreparedBridge cell)
    (CompactCellData.coefficientError_positive cell.checked.bounds)

end GeometricCheckedCell

/-! ## Comparison with prepared constant models -/

/-- The reserved factor four in each literal allowance pays for two certified
errors: literal-to-narrow and narrow-to-prepared. -/
theorem literalCoefficient_sub_centerValue_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (cell.checked.data.coefficientValue coefficientBits -
          cell.literalCenterAlignment.center.value) <=
      4 * (cell.checked.data.coefficientErrorSq allowanceBits).toCoordinate := by
  let alignment := cell.literalCenterAlignment
  let literal := cell.checked.data.coefficientValue coefficientBits
  let narrow := alignment.narrowValue
  let center := alignment.center.value
  let error :=
    (cell.checked.data.coefficientErrorSq allowanceBits).toCoordinate
  have narrowError :
      RFAP.ConstructiveGaussian.Gaussian.normSq (narrow - literal) <= error :=
    alignment.narrowError
  have literalError :
      RFAP.ConstructiveGaussian.Gaussian.normSq (literal - narrow) <= error := by
    have reverse : literal - narrow = -(narrow - literal) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
    rw [reverse, RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
    exact narrowError
  have identity : literal - center =
      (literal - narrow) + (narrow - center) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  change RFAP.ConstructiveGaussian.Gaussian.normSq (literal - center) <=
    4 * error
  rw [identity]
  exact
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (calc
        2 * (RFAP.ConstructiveGaussian.Gaussian.normSq (literal - narrow) +
            RFAP.ConstructiveGaussian.Gaussian.normSq (narrow - center)) <=
            2 * (error + error) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add literalError alignment.close.le) (by decide)
        _ = 4 * error := by ring1)

/-- The rounded generated cell is a certified one-cell constant comparison
of its actual prepared model.  No rounded literal is claimed to be a process
witness. -/
def literalPartitionCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      (cell.literalCenterAlignment.prepared.centeredModel
        cell.literalCenterAlignment.center)
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        [cell.checked.data.literalCellModel cell.checked.bounds]) := by
  let data := cell.checked.data
  let bounds := cell.checked.bounds
  let alignment := cell.literalCenterAlignment
  let center := alignment.center
  let error := data.coefficientValue coefficientBits - center.value
  exact
    { reference := center.value
      parent_polynomial_eq := rfl
      errors := [error]
      comparison := .cons (data.coefficientValue coefficientBits) error rfl
        rfl (literalCoefficient_sub_centerValue_le cell) .nil
      displacement_eq := by
        simp only [CCL.ProgressiveGaussianIntegration.PathModel.displacementSum,
          List.foldr_cons, List.foldr_nil,
          CCL.ProgressiveGaussianIntegration.CellModel.displacement]
        dsimp only [CompactCellData.literalCellModel,
          CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel]
        rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]
        change data.finishValue - data.startValue =
          alignment.prepared.point 1 - alignment.prepared.point 0
        rw [alignment.start_eq, alignment.finish_eq] }

/-! ## Source-centred generated runs -/

@[simp] theorem GeometricCheckedCell.literalCenterAlignment_prepared
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.literalCenterAlignment.prepared = cell.preparedEdge := by
  rfl

/-- The actual prepared edge paired with the comparison-selected persisted
centre used by the sharp literal certificate. -/
def GeometricCheckedCell.centeredEdge
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential := by
  exact
    { edge := cell.preparedEdge
      center := by
        rw [← cell.literalCenterAlignment_prepared]
        exact cell.literalCenterAlignment.center }

/-- Recenter one certified direct child against a target-accurate query of
its generated parent.  Geometry and sheet provenance are unchanged; only the
persisted finite coefficient state is replaced. -/
def GeometricCheckedCell.transportAlignedChild
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {child : CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    (relation : CCL.Riemann.PreparedSubdivisionModels.RootChildAt
      cell.centeredEdge child)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential :=
  { edge := child.edge
    center := cell.transportAlignedChildCenter child.edge relation.fraction
      relation.inside
      (by
        apply
          CCL.Riemann.PreparedConstantModels.PreparedEdge.coefficientEquivalent_of_rootEquivalent
            cell.preparedEdge child.edge relation.fraction relation.inside
        · simpa only [GeometricCheckedCell.centeredEdge] using relation.point_eq
        · simpa only [GeometricCheckedCell.centeredEdge] using
            relation.rootEquivalent)
      target targetPositive }

/-- The recentered child retains its exact root-child relationship to the
generated parent, so it remains usable by the ordinary compatible refinement
constructor. -/
def GeometricCheckedCell.transportAlignedChildAt
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {child : CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    (relation : CCL.Riemann.PreparedSubdivisionModels.RootChildAt
      cell.centeredEdge child)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    CCL.Riemann.PreparedSubdivisionModels.RootChildAt cell.centeredEdge
      (cell.transportAlignedChild relation target targetPositive) where
  fraction := relation.fraction
  inside := relation.inside
  point_eq := relation.point_eq
  rootEquivalent := relation.rootEquivalent

/-- Quantitative error of the recentered direct child, stated against the
literal coefficient stored in the external generated row. -/
theorem GeometricCheckedCell.transportAlignedChild_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {child : CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    (relation : CCL.Riemann.PreparedSubdivisionModels.RootChildAt
      cell.centeredEdge child)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((cell.transportAlignedChild relation target targetPositive).center.value -
          cell.checked.data.coefficientValue coefficientBits) <=
      2 * (10 * target +
        (cell.checked.data.transportCoefficientErrorSq
          allowanceBits).toCoordinate) := by
  unfold GeometricCheckedCell.transportAlignedChild
  apply cell.transportAlignedChildCenter_error_le

/-- The explicit local allowance used when a recentered child is viewed as a
comparison term against its generated row's literal coefficient. -/
def GeometricCheckedCell.transportChildErrorAllowance
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational) :
    RFAP.ConstructiveFraction.Rational :=
  2 * (10 * target +
    (cell.checked.data.transportCoefficientErrorSq
      allowanceBits).toCoordinate)

theorem GeometricCheckedCell.transportChildErrorAllowance_nonnegative
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {target : RFAP.ConstructiveFraction.Rational}
    (targetNonnegative : 0 <= target) :
    0 <= cell.transportChildErrorAllowance target := by
  unfold GeometricCheckedCell.transportChildErrorAllowance
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        targetNonnegative)
      (by
        simpa only [CompactCellData.transportView_coefficientErrorSq] using
          (CompactCellData.coefficientError_positive
            cell.checked.transportBounds.rootBounds).le))

/-- Recenter every member of one direct child block against the same
generated parent occurrence.  The recursive result contains only ordinary
centred edges, so it can be passed to the existing path constructors. -/
def GeometricCheckedCell.transportAlignedChildren
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)} ->
    CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
      cell.centeredEdge children ->
    List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)
  | [], .nil => []
  | _ :: _, .cons head tail =>
      cell.transportAlignedChild head target targetPositive ::
        cell.transportAlignedChildren target targetPositive tail

@[simp] theorem GeometricCheckedCell.transportAlignedChildren_length
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      (cell.transportAlignedChildren target targetPositive roots).length =
        children.length
  | [], .nil => rfl
  | _ :: _, .cons _ tail => by
      simp only [GeometricCheckedCell.transportAlignedChildren,
        List.length_cons,
        cell.transportAlignedChildren_length target targetPositive tail]

/-- The recentered list keeps the root-child witness for every leaf. -/
def GeometricCheckedCell.transportAlignedRootBlock
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)} ->
    (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
      cell.centeredEdge children) ->
    CCL.Riemann.PreparedSubdivisionModels.RootChildBlock cell.centeredEdge
      (cell.transportAlignedChildren target targetPositive roots)
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (cell.transportAlignedChildAt head target targetPositive)
        (cell.transportAlignedRootBlock target targetPositive tail)

/-- One recentered child as a comparison-only cell.  Its integral sample is
unchanged, while its local allowance is the sharp generated transport error
rather than the generic prepared-model allowance. -/
def GeometricCheckedCell.transportAlignedComparisonCell
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    {child : CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    (relation : CCL.Riemann.PreparedSubdivisionModels.RootChildAt
      cell.centeredEdge child)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    CCL.ProgressiveGaussianIntegration.CellModel :=
  (cell.transportAlignedChild relation target targetPositive).model.withAllowance
    (cell.transportChildErrorAllowance target)
    (cell.transportChildErrorAllowance_nonnegative targetPositive.le)

/-- Comparison cells for a complete direct block, in exact child order. -/
def GeometricCheckedCell.transportAlignedComparisonCells
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)} ->
    CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
      cell.centeredEdge children ->
    List CCL.ProgressiveGaussianIntegration.CellModel
  | [], .nil => []
  | _ :: _, .cons head tail =>
      cell.transportAlignedComparisonCell head target targetPositive ::
        cell.transportAlignedComparisonCells target targetPositive tail

/-- Explicit coefficient-error list aligned with the comparison cells. -/
def GeometricCheckedCell.transportAlignedErrors
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)} ->
    CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
      cell.centeredEdge children ->
    List RFAP.ConstructiveGaussian.Gaussian
  | [], .nil => []
  | _ :: _, .cons head tail =>
      ((cell.transportAlignedChild head target targetPositive).center.value -
        cell.checked.data.coefficientValue coefficientBits) ::
      cell.transportAlignedErrors target targetPositive tail

/-- Every recentered comparison cell is certified against the same literal
coefficient stored in the generated row. -/
def GeometricCheckedCell.transportAlignedComparison
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)} ->
    (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
      cell.centeredEdge children) ->
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantComparison
      (cell.checked.data.coefficientValue coefficientBits)
      (cell.transportAlignedComparisonCells target targetPositive roots)
      (cell.transportAlignedErrors target targetPositive roots)
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons
        (cell.transportAlignedChild head target targetPositive).center.value
        ((cell.transportAlignedChild head target targetPositive).center.value -
          cell.checked.data.coefficientValue coefficientBits)
        rfl rfl
        (by
          change RFAP.ConstructiveGaussian.Gaussian.normSq _ <=
            cell.transportChildErrorAllowance target
          exact cell.transportAlignedChild_error_le head target targetPositive)
        (cell.transportAlignedComparison target targetPositive tail)

/-- Recentring and replacing the comparison allowance preserve every child
displacement in a direct block. -/
theorem GeometricCheckedCell.transportAlignedComparisonCells_displacementSum
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (cell.transportAlignedComparisonCells target targetPositive roots) =
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (children.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
  | [], .nil => rfl
  | _ :: children, .cons _ tail => by
      simp only [GeometricCheckedCell.transportAlignedComparisonCells,
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum_cons,
        List.map_cons]
      rw [cell.transportAlignedComparisonCells_displacementSum target
        targetPositive tail]
      rfl

/-- Recentring preserves the strict-width evidence of every direct leaf. -/
theorem GeometricCheckedCell.transportAlignedChildren_proper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper children ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
        (cell.transportAlignedChildren target targetPositive roots)
  | [], .nil, _ => True.intro
  | _ :: _, .cons _ tail, proper =>
      ⟨proper.1,
        cell.transportAlignedChildren_proper target targetPositive tail
          proper.2⟩

/-- The direct child chain can be recentered cell-for-cell without changing
either dependent endpoint. -/
def GeometricCheckedCell.transportAlignedDirectPathChain
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      CCL.Riemann.PreparedDirectDyadicRefinements.DirectPathChain children
        (start := start) (finish := finish) ->
      CCL.Riemann.PreparedDirectDyadicRefinements.DirectPathChain
        (cell.transportAlignedChildren target targetPositive roots)
        (start := start) (finish := finish)
  | [], _, _, .nil, .nil endpointValue => .nil endpointValue
  | _ :: _, _, _, .cons head roots, .cons _ tail =>
      .cons (cell.transportAlignedChild head target targetPositive)
        (cell.transportAlignedDirectPathChain target targetPositive roots tail)

@[simp] theorem GeometricCheckedCell.centeredEdge_sheet
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.edge.sheet = cell.sheet := by
  unfold centeredEdge preparedEdge
  rfl

theorem GeometricCheckedCell.centeredEdge_start_eq
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.edge.segment.pointAt
      cell.centeredEdge.edge.left.parameter =
      cell.checked.data.startValue := by
  unfold centeredEdge preparedEdge
  exact cell.geometry.start_eq

theorem GeometricCheckedCell.centeredEdge_finish_eq
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.edge.segment.pointAt
      cell.centeredEdge.edge.request.endpoint.parameter =
      cell.checked.data.finishValue := by
  unfold centeredEdge preparedEdge
  rw [cell.geometry.request_endpoint]
  exact cell.geometry.finish_eq

theorem GeometricCheckedCell.centeredEdge_proper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.edge.left.parameter <
      cell.centeredEdge.edge.request.endpoint.parameter := by
  unfold centeredEdge preparedEdge
  exact
    CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdgeAt_strict
      (generatedInnerDepthOfPosition cell.checked.data.position)
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      CCL.Riemann.PreparedClearPathModels.oneEndpoint
      ⟨cell.checked.data.position - generatedWorkingSegmentOffset
          (generatedWorkingSegmentOfPosition cell.checked.data.position),
        cell.geometry.location.localWithin⟩ (by decide)

/-- Owner-specific upper bound for the prepared model error of one generated
`dx/y` row.  The point-variation term vanishes at exponent zero, while the
cached prepared root diameter is strictly below the displayed request. -/
def GeometricCheckedCell.parentModelErrorUpper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    RFAP.ConstructiveFraction.Rational :=
  cell.preparedEdge.preparedRootErrorCoefficient *
    cell.preparedEdge.request.rootDiameter

theorem GeometricCheckedCell.modelErrorAllowance_le_parentModelErrorUpper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.preparedEdge.modelErrorAllowance <= cell.parentModelErrorUpper := by
  have pointCoefficientZero :
      cell.preparedEdge.preparedPointErrorCoefficient = 0 := by
    unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedPointErrorCoefficient
    rw [CompactCellData.legendreDifferential_exponent]
    rw [show CCL.Riemann.FiniteQuotientVariation.powerSlope
      cell.preparedEdge.ambient.normSqBound 0 = 0 by rfl]
    rw [RFAP.ConstructiveFraction.zero_mul_direct,
      RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_div_direct]
  rw [cell.preparedEdge.modelErrorAllowance_eq_preparedLinear,
    pointCoefficientZero]
  simpa only [zero_mul, zero_add, parentModelErrorUpper] using
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      cell.preparedEdge.preparedRootDiameter_lt_requested.le
      cell.preparedEdge.preparedRootErrorCoefficient_nonnegative)

@[simp] theorem GeometricCheckedCell.centeredEdge_model_displacement
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.model.displacement =
      cell.checked.data.finishValue - cell.checked.data.startValue := by
  unfold CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model
    CCL.Riemann.PreparedConstantModels.PreparedEdge.centeredModel
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
  change cell.preparedEdge.point 1 - cell.preparedEdge.point 0 =
    cell.checked.data.finishValue - cell.checked.data.startValue
  rw [cell.preparedEdge_point_one, cell.preparedEdge_point_zero,
    cell.geometry.request_endpoint,
    cell.geometry.finish_eq, cell.geometry.start_eq]

theorem GeometricCheckedCell.transportAlignedComparisonCells_length
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      (cell.transportAlignedComparisonCells target targetPositive roots).length =
        children.length
  | [], .nil => rfl
  | _ :: _, .cons _ tail => by
      simp only [GeometricCheckedCell.transportAlignedComparisonCells,
        List.length_cons]
      rw [cell.transportAlignedComparisonCells_length target targetPositive tail]

/-- The auxiliary comparison cells and the same geometric children equipped
with the uniform transport allowance have exactly the same total weighted
allowance. -/
theorem GeometricCheckedCell.transportAlignedComparisonCells_totalWeightedAllowance
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (cell.transportAlignedComparisonCells target targetPositive roots)
          ).totalWeightedAllowance =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (children.map fun child =>
            child.model.withAllowance
              (cell.transportChildErrorAllowance target)
              (cell.transportChildErrorAllowance_nonnegative
                targetPositive.le))).totalWeightedAllowance
  | [], .nil => rfl
  | _ :: children, .cons _ tail => by
      simp only [GeometricCheckedCell.transportAlignedComparisonCells,
        List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      have tailEqual :=
        cell.transportAlignedComparisonCells_totalWeightedAllowance target
          targetPositive tail
      change
        (cell.transportAlignedComparisonCells target targetPositive tail).foldr
            (fun model total => model.weightedAllowance + total) 0 =
          (children.map fun child =>
            child.model.withAllowance
              (cell.transportChildErrorAllowance target)
              (cell.transportChildErrorAllowance_nonnegative
                targetPositive.le)).foldr
            (fun model total => model.weightedAllowance + total) 0 at tailEqual
      rw [tailEqual]
      rfl

/-- The corresponding aggregate comparison allowance is therefore bounded
by the coarse row movement, independently of the direct dyadic depth. -/
theorem GeometricCheckedCell.transportAlignedComparisonCells_aggregateAllowance_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      cell.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (cell.transportAlignedComparisonCells target targetPositive
        block.roots)).aggregateAllowance <=
      CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
          cell.centeredEdge.edge.segment
          cell.centeredEdge.edge.left.parameter
          cell.centeredEdge.edge.request.endpoint.parameter *
        cell.transportChildErrorAllowance target := by
  let errorNonnegative :=
    cell.transportChildErrorAllowance_nonnegative targetPositive.le
  calc
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (cell.transportAlignedComparisonCells target targetPositive
          block.roots)).aggregateAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (block.constantAllowanceCells
          (cell.transportChildErrorAllowance target)
          errorNonnegative)).aggregateAllowance := by
        unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
        unfold
          CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock.constantAllowanceCells
        rw [cell.transportAlignedComparisonCells_length target targetPositive
            block.roots,
          cell.transportAlignedComparisonCells_totalWeightedAllowance target
            targetPositive block.roots]
        simp only [List.length_map]
    _ <= CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
          cell.centeredEdge.edge.segment
          cell.centeredEdge.edge.left.parameter
          cell.centeredEdge.edge.request.endpoint.parameter *
        cell.transportChildErrorAllowance target := by
      exact block.constantAllowanceCells_aggregateAllowance_le
        (cell.transportChildErrorAllowance target) errorNonnegative

/-- Replacing only the comparison allowance leaves the integral of the
recentered child list unchanged. -/
theorem GeometricCheckedCell.transportAlignedComparisonCells_integralSample
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        cell.centeredEdge children),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (cell.transportAlignedComparisonCells target targetPositive roots)
          ).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((cell.transportAlignedChildren target targetPositive roots).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
          ).integralSample
  | [], .nil => rfl
  | _ :: _, .cons _ tail => by
      simp only [GeometricCheckedCell.transportAlignedComparisonCells,
        GeometricCheckedCell.transportAlignedChildren, List.map_cons,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons]
      have tailEqual :=
        cell.transportAlignedComparisonCells_integralSample target
          targetPositive tail
      change
        (cell.transportAlignedComparisonCells target targetPositive tail).foldr
            (fun model total => model.integralSample + total) 0 =
          ((cell.transportAlignedChildren target targetPositive tail).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
              (fun model total => model.integralSample + total) 0 at tailEqual
      rw [tailEqual]
      rfl

/-- A complete direct block, recentered against the generated transport
owner, is a sharp constant partition of the row's literal cell. -/
def GeometricCheckedCell.transportAlignedPartitionCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      cell.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPartitionCertificate
      (cell.checked.data.literalCellModel cell.checked.bounds)
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (cell.transportAlignedComparisonCells target targetPositive
          block.roots)) where
  reference := cell.checked.data.coefficientValue coefficientBits
  parent_polynomial_eq := rfl
  errors := cell.transportAlignedErrors target targetPositive block.roots
  comparison :=
    cell.transportAlignedComparison target targetPositive block.roots
  displacement_eq := by
    calc
      CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (cell.transportAlignedComparisonCells target targetPositive
            block.roots) =
        CCL.ProgressiveGaussianIntegration.PathModel.displacementSum
          (block.children.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model) :=
        cell.transportAlignedComparisonCells_displacementSum target
          targetPositive block.roots
      _ = cell.centeredEdge.model.displacement := block.displacement_eq
      _ = (cell.checked.data.literalCellModel
          cell.checked.bounds).displacement := by
        rw [cell.centeredEdge_model_displacement,
          CompactCellData.literalCellModel_displacement]
        rfl

/-- Sharp integral comparison for the actual recentered child block. -/
theorem GeometricCheckedCell.transportAlignedIntegral_difference_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      cell.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((cell.transportAlignedChildren target targetPositive
              block.roots).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
          ).integralSample -
          (cell.checked.data.literalCellModel
            cell.checked.bounds).integralSample) <=
      CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
          cell.centeredEdge.edge.segment
          cell.centeredEdge.edge.left.parameter
          cell.centeredEdge.edge.request.endpoint.parameter *
        cell.transportChildErrorAllowance target := by
  rw [← cell.transportAlignedComparisonCells_integralSample target
    targetPositive block.roots]
  exact
    (cell.transportAlignedPartitionCertificate block target
      targetPositive).integral_difference_le.trans
        (cell.transportAlignedComparisonCells_aggregateAllowance_le block
          target targetPositive)

/-- Existential packaging of one generated row, hiding the three global
dyadic precisions while retaining its sharp direct-refinement interface. -/
structure GeneratedTransportParent where
  rootBits : Nat
  coefficientBits : Nat
  allowanceBits : Nat
  cell : GeometricCheckedCell rootBits coefficientBits allowanceBits

namespace GeneratedTransportParent

/-- Global canonical B-mesh row retained by this transport parent. -/
def position (parent : GeneratedTransportParent) : Nat :=
  parent.cell.checked.data.position

abbrev centeredEdge (parent : GeneratedTransportParent) :=
  parent.cell.centeredEdge

def literalModel (parent : GeneratedTransportParent) :
    CCL.ProgressiveGaussianIntegration.CellModel :=
  parent.cell.checked.data.literalCellModel parent.cell.checked.bounds

def movementSq (parent : GeneratedTransportParent) :
    RFAP.ConstructiveFraction.Rational :=
  CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
    parent.centeredEdge.edge.segment
    parent.centeredEdge.edge.left.parameter
    parent.centeredEdge.edge.request.endpoint.parameter

def transportErrorSq (parent : GeneratedTransportParent) :
    RFAP.ConstructiveFraction.Rational :=
  (parent.cell.checked.data.transportCoefficientErrorSq
    parent.allowanceBits).toCoordinate

def alignedChildren (parent : GeneratedTransportParent)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      parent.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :=
  parent.cell.transportAlignedChildren target targetPositive block.roots

def alignedRootBlock (parent : GeneratedTransportParent)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      parent.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :=
  parent.cell.transportAlignedRootBlock target targetPositive block.roots

theorem alignedIntegral_difference_le (parent : GeneratedTransportParent)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      parent.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parent.alignedChildren block target targetPositive).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).integralSample - parent.literalModel.integralSample) <=
      parent.movementSq *
        (2 * (10 * target + parent.transportErrorSq)) := by
  exact parent.cell.transportAlignedIntegral_difference_le block target
    targetPositive

/-- Transport alignment replaces only the retained coefficient centre.  The
prepared child edge, hence its displacement and semantic local allowance,
is unchanged. -/
theorem alignedChild_weightedAllowance_eq
    (parent : GeneratedTransportParent)
    {child : CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential}
    (relation : CCL.Riemann.PreparedSubdivisionModels.RootChildAt
      parent.centeredEdge child)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    (parent.cell.transportAlignedChild relation target
      targetPositive).model.weightedAllowance =
        child.model.weightedAllowance := by
  rfl

/-- Transport alignment preserves the complete semantic weighted allowance
of one direct block. -/
theorem alignedChildren_totalWeightedAllowance_eq
    (parent : GeneratedTransportParent)
    (block : CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
      parent.centeredEdge)
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((parent.alignedChildren block target targetPositive).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ).totalWeightedAllowance =
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (block.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ).totalWeightedAllowance := by
  change CCL.Riemann.PreparedDirectDyadicRefinements.DirectParentBlock
    parent.cell.centeredEdge at block
  change
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((parent.cell.transportAlignedChildren target targetPositive
          block.roots).map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ).totalWeightedAllowance =
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (block.children.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      ).totalWeightedAllowance
  have recursive : forall
      {children : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
      (roots : CCL.Riemann.PreparedSubdivisionModels.RootChildBlock
        parent.cell.centeredEdge children),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((parent.cell.transportAlignedChildren target targetPositive roots).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).totalWeightedAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).totalWeightedAllowance := by
    intro children roots
    induction roots with
    | nil => rfl
    | @cons child children head tail inductionHypothesis =>
        simp only [GeometricCheckedCell.transportAlignedChildren,
          List.map_cons,
          CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
          List.foldr_cons]
        change
          (parent.cell.transportAlignedChild head target
              targetPositive).model.weightedAllowance +
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                ((parent.cell.transportAlignedChildren target targetPositive
                  tail).map
                    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
                ).totalWeightedAllowance =
            child.model.weightedAllowance +
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (children.map
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
                ).totalWeightedAllowance
        rw [inductionHypothesis]
        rw [parent.alignedChild_weightedAllowance_eq head target
          targetPositive]
  exact recursive block.roots

end GeneratedTransportParent

/-- Weighted allowance bound for one generated prepared parent, expressed
only through the cached owner denominator and request diameter. -/
def GeometricCheckedCell.parentWeightedAllowanceUpper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    RFAP.ConstructiveFraction.Rational :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
      (cell.checked.data.finishValue - cell.checked.data.startValue) *
    (16 * cell.parentModelErrorUpper)

/-- Row-and-denominator presentation of the parent upper bound.  Separating
this arithmetic function from the dependent geometry record lets generated
checks reduce one compact row without dependent rewriting. -/
def compactParentWeightedAllowanceUpperAt
    (data : CompactCellData) (rootBits : Nat)
    (segmentDenominatorLower : RFAP.ConstructiveFraction.Rational) :
    RFAP.ConstructiveFraction.Rational :=
  let denominatorLower := max segmentDenominatorLower
    (CCL.Riemann.PreparedConstantModels.PreparedEdge.boxNormSqLower
      (data.transportRootBox rootBits))
  RFAP.ConstructiveGaussian.Gaussian.normSq
      (data.finishValue - data.startValue) *
    (16 * (((2 * 1) / (denominatorLower * denominatorLower) + 1) *
      (16 * data.transportHalfWidth ^ 2)))

/-- Transparent compact presentation of the same parent upper bound.  The
generated checker evaluates this expression from one row and one cached
segment denominator, without unfolding the irreducible prepared edge. -/
def GeometricCheckedCell.compactParentWeightedAllowanceUpper
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    RFAP.ConstructiveFraction.Rational :=
  compactParentWeightedAllowanceUpperAt cell.checked.data rootBits
    cell.geometry.segmentBinding.denominatorLower

theorem GeometricCheckedCell.parentWeightedAllowanceUpper_eq_compact
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.parentWeightedAllowanceUpper =
      cell.compactParentWeightedAllowanceUpper := by
  have denominatorLower_eq : cell.preparedEdge.preparedDenominatorLower =
      max cell.geometry.segmentBinding.denominatorLower
        (CCL.Riemann.PreparedConstantModels.PreparedEdge.boxNormSqLower
          (cell.checked.data.transportRootBox rootBits)) := by
    have transportBox_eq : cell.transportOwner.track.initial.box =
        cell.checked.data.transportRootBox rootBits := by
      rw [GeometricCheckedCell.transportOwner,
        GeneratedCellGeometry.transportRootOwner_initial_box]
    unfold CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedDenominatorLower
      GeometricCheckedCell.preparedEdge
    change max
        (CCL.Riemann.PreparedDifferentialModels.segmentDenominatorLower
          (generatedLegAt cell.geometry.location).segment)
        (CCL.Riemann.PreparedConstantModels.PreparedEdge.boxNormSqLower
          cell.transportOwner.track.initial.box) = _
    rw [cell.geometry.segmentBinding.denominatorLower_eq, transportBox_eq]
  have ambientPower_eq :
      cell.preparedEdge.ambient.normSqBound ^
          CompactCellData.legendreDifferential.exponent = 1 := by
    rw [CompactCellData.legendreDifferential_exponent]
    rfl
  have requestDiameter_eq : cell.preparedEdge.request.rootDiameter =
      16 * cell.checked.data.transportHalfWidth ^ 2 := by
    unfold GeometricCheckedCell.preparedEdge
    change cell.geometry.request.rootDiameter = _
    rfl
  unfold parentWeightedAllowanceUpper parentModelErrorUpper
    compactParentWeightedAllowanceUpper
    compactParentWeightedAllowanceUpperAt
    CCL.Riemann.PreparedConstantModels.PreparedEdge.preparedRootErrorCoefficient
  rw [denominatorLower_eq, ambientPower_eq, requestDiameter_eq]

theorem GeometricCheckedCell.parentWeightedAllowance_le
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    cell.centeredEdge.model.weightedAllowance <=
      cell.parentWeightedAllowanceUpper := by
  unfold CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    parentWeightedAllowanceUpper
  rw [cell.centeredEdge_model_displacement]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      cell.modelErrorAllowance_le_parentModelErrorUpper (by decide))
    (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)

private def castSwitchedChain
    {parents : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)}
    {firstStart secondStart firstFinish secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (start_eq : firstStart = secondStart)
    (finish_eq : firstFinish = secondFinish)
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      parents (start := firstStart) (finish := firstFinish)) :
    CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      parents (start := secondStart) (finish := secondFinish) := by
  cases start_eq
  cases finish_eq
  exact chain

private theorem castSwitchedChain_switchCount
    {parents : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential)}
    {firstStart secondStart firstFinish secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (start_eq : firstStart = secondStart)
    (finish_eq : firstFinish = secondFinish)
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      parents (start := firstStart) (finish := firstFinish)) :
    (castSwitchedChain start_eq finish_eq chain).switchCount =
      chain.switchCount := by
  cases start_eq
  cases finish_eq
  rfl

private def castSwitchedChainParents
    {firstParents secondParents : List
      (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (parents_eq : firstParents = secondParents)
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      firstParents (start := start) (finish := finish)) :
    CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      secondParents (start := start) (finish := finish) := by
  cases parents_eq
  exact chain

private theorem castSwitchedChainParents_switchCount
    {firstParents secondParents : List
      (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)}
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (parents_eq : firstParents = secondParents)
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      firstParents (start := start) (finish := finish)) :
    (castSwitchedChainParents parents_eq chain).switchCount =
      chain.switchCount := by
  cases parents_eq
  rfl

private theorem appendParentsProper :
    forall {first second : List
      (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)},
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper first ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper second ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1, appendParentsProper firstProper.2 secondProper⟩

private def appendLiteralRefinement :
    {firstParents firstChildren :
      List CCL.ProgressiveGaussianIntegration.CellModel} ->
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
      firstParents firstChildren ->
    {secondParents secondChildren :
      List CCL.ProgressiveGaussianIntegration.CellModel} ->
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
      secondParents secondChildren ->
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
      (firstParents ++ secondParents) (firstChildren ++ secondChildren)
  | _, _, .nil, _, _, second => second
  | _, _, .cons head remaining, _, _, second => by
      rw [List.cons_append, List.append_assoc]
      exact .cons head (appendLiteralRefinement remaining second)

/-! ## Sharp generated transport across a synchronized direct refinement -/

namespace GeneratedTransportRefinement

open CCL.Riemann.PreparedDirectDyadicRefinements

/-- Recenter every synchronized direct block against its originating
generated row, preserving block and row order. -/
def children
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent),
      SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge) ->
      List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential)
  | _, _, [], .nil => []
  | _, _, parent :: parents, .cons block _ _ tail =>
      parent.alignedChildren block target targetPositive ++
        children target targetPositive parents tail

/-- Comparison-only cells using the sharp row-local transport allowance. -/
def comparisonCells
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent),
      SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge) ->
      List CCL.ProgressiveGaussianIntegration.CellModel
  | _, _, [], .nil => []
  | _, _, parent :: parents, .cons block _ _ tail =>
      parent.cell.transportAlignedComparisonCells target targetPositive
          block.roots ++
        comparisonCells target targetPositive parents tail

/-- The row literals refine sharply to the recentered direct blocks. -/
def literalRefinement
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
        (parents.map GeneratedTransportParent.literalModel)
        (comparisonCells target targetPositive parents blocks)
  | _, _, [], .nil => .nil
  | _, _, parent :: parents, .cons block _ _ tail =>
      .cons
        (parent.cell.transportAlignedPartitionCertificate block target
          targetPositive)
        (literalRefinement target targetPositive parents tail)

/-- Recentered semantic children and their comparison views have identical
rational integral samples. -/
theorem children_integralSample_eq_comparisonCells
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((children target targetPositive parents blocks).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).integralSample =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (comparisonCells target targetPositive parents blocks)
        ).integralSample
  | _, _, [], .nil => by
      change 0 = 0
      rfl
  | _, _, parent :: parents, .cons block _ _ tail => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parent.cell.transportAlignedChildren target targetPositive
              block.roots ++
            children target targetPositive parents tail).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
          ).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parent.cell.transportAlignedComparisonCells target targetPositive
              block.roots ++
            comparisonCells target targetPositive parents tail)
          ).integralSample
      rw [List.map_append]
      rw [pathModel_integralSample_append,
        pathModel_integralSample_append,
        parent.cell.transportAlignedComparisonCells_integralSample target
          targetPositive block.roots,
        children_integralSample_eq_comparisonCells target targetPositive
          parents tail]

/-- The exact row-local coarse-scale allowance sum emitted by the external
certificate. -/
def weightedTransportSum
    (target : RFAP.ConstructiveFraction.Rational) :
    List GeneratedTransportParent -> RFAP.ConstructiveFraction.Rational
  | [] => 0
  | parent :: parents =>
      parent.movementSq *
          (2 * (10 * target + parent.transportErrorSq)) +
        weightedTransportSum target parents

def movementSqSum : List GeneratedTransportParent ->
    RFAP.ConstructiveFraction.Rational
  | [] => 0
  | parent :: parents => parent.movementSq + movementSqSum parents

def transportWeightedErrorSum : List GeneratedTransportParent ->
    RFAP.ConstructiveFraction.Rational
  | [] => 0
  | parent :: parents =>
      parent.movementSq * parent.transportErrorSq +
        transportWeightedErrorSum parents

theorem movementSqSum_append (first second : List GeneratedTransportParent) :
    movementSqSum (first ++ second) =
      movementSqSum first + movementSqSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append, movementSqSum,
        RFAP.ConstructiveFraction.zero_add]
  | cons parent parents inductionHypothesis =>
      simp only [List.cons_append, movementSqSum, inductionHypothesis]
      ring1

theorem transportWeightedErrorSum_append
    (first second : List GeneratedTransportParent) :
    transportWeightedErrorSum (first ++ second) =
      transportWeightedErrorSum first + transportWeightedErrorSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append, transportWeightedErrorSum,
        RFAP.ConstructiveFraction.zero_add]
  | cons parent parents inductionHypothesis =>
      simp only [List.cons_append, transportWeightedErrorSum,
        inductionHypothesis]
      ring1

theorem weightedTransportSum_eq
    (target : RFAP.ConstructiveFraction.Rational) :
    forall parents : List GeneratedTransportParent,
      weightedTransportSum target parents =
        2 * (10 * target * movementSqSum parents +
          transportWeightedErrorSum parents)
  | [] => by
      simp only [weightedTransportSum, movementSqSum,
        transportWeightedErrorSum,
        RFAP.ConstructiveFraction.mul_zero_direct,
        RFAP.ConstructiveFraction.zero_add]
  | parent :: parents => by
      simp only [weightedTransportSum, movementSqSum,
        transportWeightedErrorSum, weightedTransportSum_eq target parents]
      ring1

/-- One common dyadic child count times the complete comparison weight is
bounded by the sum of the row-local transport bounds. -/
theorem scaledTotalWeightedAllowance_le
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (comparisonCells target targetPositive parents blocks)
          ).totalWeightedAllowance <=
        weightedTransportSum target parents
  | _, _, [], .nil => by
      simp only [comparisonCells, weightedTransportSum,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil, RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | depth, _, parent :: parents,
      .cons block depth_eq _ tail => by
      have headBound :=
        parent.cell.transportAlignedComparisonCells_aggregateAllowance_le
          block target targetPositive
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance at headBound
      rw [parent.cell.transportAlignedComparisonCells_length target
          targetPositive block.roots,
        block.childCount, depth_eq] at headBound
      change
        ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (parent.cell.transportAlignedComparisonCells target
                targetPositive block.roots)).totalWeightedAllowance <=
          parent.movementSq *
            (2 * (10 * target + parent.transportErrorSq)) at headBound
      have tailBound := scaledTotalWeightedAllowance_le target targetPositive
        parents tail
      change
        ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              (parent.cell.transportAlignedComparisonCells target
                  targetPositive block.roots ++
                comparisonCells target targetPositive parents tail)
              ).totalWeightedAllowance <=
          parent.movementSq *
              (2 * (10 * target + parent.transportErrorSq)) +
            weightedTransportSum target parents
      rw [pathModel_totalWeightedAllowance_append]
      calc
        ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
            ((CCL.ProgressiveGaussianIntegration.PathModel.mk
                (parent.cell.transportAlignedComparisonCells target
                  targetPositive block.roots)).totalWeightedAllowance +
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (comparisonCells target targetPositive parents tail)
                ).totalWeightedAllowance) =
          ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (parent.cell.transportAlignedComparisonCells target
                  targetPositive block.roots)).totalWeightedAllowance +
            ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (comparisonCells target targetPositive parents tail)
                ).totalWeightedAllowance := by ring1
        _ <= parent.movementSq *
              (2 * (10 * target + parent.transportErrorSq)) +
            weightedTransportSum target parents :=
          add_le_add headBound tailBound

private theorem natCast_nonnegative (value : Nat) :
    (0 : RFAP.ConstructiveFraction.Rational) <= value := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

theorem comparisonCells_length
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (comparisonCells target targetPositive parents blocks).length =
        parents.length * 2 ^ depth
  | _, _, [], .nil => by
      unfold comparisonCells
      simp only [List.length_nil, Nat.zero_mul]
  | depth, _, parent :: parents, .cons block depth_eq _ tail => by
      change
        (parent.cell.transportAlignedComparisonCells target targetPositive
              block.roots ++
            comparisonCells target targetPositive parents tail).length =
          (parent :: parents).length * 2 ^ depth
      rw [List.length_append,
        parent.cell.transportAlignedComparisonCells_length target
          targetPositive block.roots,
        block.childCount, depth_eq,
        comparisonCells_length target targetPositive parents tail]
      simp only [List.length_cons, Nat.succ_mul]
      omega

theorem children_length_eq
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (children target targetPositive parents blocks).length =
        blocks.children.length
  | _, _, [], .nil => by
      change [].length = [].length
      rfl
  | _, _, parent :: parents, .cons block _ _ tail => by
      change
        (parent.cell.transportAlignedChildren target targetPositive
            block.roots ++
          children target targetPositive parents tail).length =
        (block.children ++ tail.children).length
      rw [List.length_append, List.length_append,
        parent.cell.transportAlignedChildren_length target targetPositive
          block.roots,
        children_length_eq target targetPositive parents tail]

/-- The complete sharp comparison allowance, with the common child count
cancelled before any generated arithmetic is evaluated. -/
theorem comparisonAggregateAllowance_le
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (comparisonCells target targetPositive parents blocks)
        ).aggregateAllowance <=
      (parents.length : RFAP.ConstructiveFraction.Rational) *
        weightedTransportSum target parents
  | _, _, [], .nil => by
      simp only [comparisonCells, weightedTransportSum, List.length_nil,
        Nat.cast_zero, RFAP.ConstructiveFraction.zero_mul_direct]
      exact le_rfl
  | depth, rootDiameter, parents, blocks => by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
      rw [comparisonCells_length target targetPositive parents blocks,
        Nat.cast_mul]
      have scaled := scaledTotalWeightedAllowance_le target targetPositive
        parents blocks
      calc
        (parents.length : RFAP.ConstructiveFraction.Rational) *
            ((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (comparisonCells target targetPositive parents blocks)
                ).totalWeightedAllowance =
          (parents.length : RFAP.ConstructiveFraction.Rational) *
            (((2 ^ depth : Nat) : RFAP.ConstructiveFraction.Rational) *
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (comparisonCells target targetPositive parents blocks)
                ).totalWeightedAllowance) := by ring1
        _ <= (parents.length : RFAP.ConstructiveFraction.Rational) *
            weightedTransportSum target parents :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct scaled
            (natCast_nonnegative parents.length)

/-- Recentered children retain the actual semantic aggregate allowance of
the canonical synchronized direct refinement. -/
theorem childrenAggregateAllowance_eq
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((children target targetPositive parents blocks).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).aggregateAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (blocks.children.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
        ).aggregateAllowance
  | _, _, [], .nil => rfl
  | depth, rootDiameter, parents, blocks => by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
      rw [List.length_map, List.length_map,
        children_length_eq target targetPositive parents blocks]
      have totalEq :
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((children target targetPositive parents blocks).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
            ).totalWeightedAllowance =
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (blocks.children.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
            ).totalWeightedAllowance := by
        induction parents with
        | nil => cases blocks; rfl
        | cons parent parents inductionHypothesis =>
            cases blocks with
            | cons block depth_eq root_eq tail =>
                change
                  (CCL.ProgressiveGaussianIntegration.PathModel.mk
                    ((parent.alignedChildren block target targetPositive ++
                      children target targetPositive parents tail).map
                      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
                    ).totalWeightedAllowance =
                  (CCL.ProgressiveGaussianIntegration.PathModel.mk
                    ((block.children ++ tail.children).map
                      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
                    ).totalWeightedAllowance
                rw [List.map_append, List.map_append,
                  pathModel_totalWeightedAllowance_append,
                  pathModel_totalWeightedAllowance_append,
                  parent.alignedChildren_totalWeightedAllowance_eq block target
                    targetPositive,
                  inductionHypothesis tail]
      rw [totalEq]

/-- Strict-width evidence is unaffected by generated transport alignment. -/
theorem childrenProper
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      (parents : List GeneratedTransportParent)
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
        (children target targetPositive parents blocks)
  | _, _, [], .nil => True.intro
  | _, _, parent :: parents, .cons block _ _ tail =>
      appendParentsProper
        (parent.cell.transportAlignedChildren_proper target targetPositive
          block.roots block.proper)
        (childrenProper target targetPositive parents tail)

set_option linter.unusedVariables false in
/-- Structural worker whose chain index is a variable.  The explicit equality
keeps the mapped generated-parent index out of the termination checker. -/
private def switchedChainAux
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      {centeredParents : List
        (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
          CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
          CompactCellData.legendreDifferential)}
      (parents : List GeneratedTransportParent)
      (parents_eq : centeredParents =
        parents.map GeneratedTransportParent.centeredEdge)
      {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
      (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
        centeredParents
        (start := start) (finish := finish))
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
        (children target targetPositive parents blocks)
        (start := start) (finish := finish)
  | _, _, _, [], rfl, _, _, .nil endpoint, .nil => .nil endpoint
  | _, _, _, parent :: parents, rfl, _, _, .edge _ tail,
      .cons block _ _ remaining =>
      (CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.ofDirectPathChain
        (parent.cell.transportAlignedDirectPathChain target
          targetPositive block.roots block.chain)).append
        (switchedChainAux target targetPositive parents rfl tail remaining)
  | _, _, _, parents, rfl, _, _,
      .stationary coordinate sheet tail, blocks =>
      .stationary coordinate sheet
        (switchedChainAux target targetPositive parents rfl tail blocks)
termination_by structural _ _ _ _ _ _ _ chain _ => chain

/-- Recenter every moving edge while retaining stationary switches in their
original positions. -/
def switchedChain
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target)
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    (parents : List GeneratedTransportParent)
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      (parents.map GeneratedTransportParent.centeredEdge)
      (start := start) (finish := finish))
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
      (parents.map GeneratedTransportParent.centeredEdge)) :
    CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      (children target targetPositive parents blocks)
      (start := start) (finish := finish) :=
  switchedChainAux target targetPositive parents rfl chain blocks

set_option linter.unusedVariables false in
private theorem switchedChainAux_switchCount
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target) :
    forall {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
      {centeredParents : List
        (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
          CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
          CompactCellData.legendreDifferential)}
      (parents : List GeneratedTransportParent)
      (parents_eq : centeredParents =
        parents.map GeneratedTransportParent.centeredEdge)
      {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
      (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
        centeredParents
        (start := start) (finish := finish))
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
        (parents.map GeneratedTransportParent.centeredEdge)),
      (switchedChainAux target targetPositive parents parents_eq chain blocks
        ).switchCount =
        chain.switchCount
  | _, _, _, [], rfl, _, _, .nil _, .nil => rfl
  | _, _, _, parent :: parents, rfl, _, _, .edge _ tail,
      .cons block _ _ remaining => by
      simp only [List.map]
      simp only [CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount]
      calc
        ((CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.ofDirectPathChain
              (parent.cell.transportAlignedDirectPathChain target
                targetPositive block.roots block.chain)).append
            (switchedChainAux target targetPositive parents rfl tail remaining)
          ).switchCount =
            (CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.ofDirectPathChain
              (parent.cell.transportAlignedDirectPathChain target
                targetPositive block.roots block.chain)).switchCount +
              (switchedChainAux target targetPositive parents rfl tail remaining
                ).switchCount :=
          CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount_append _ _
        _ = tail.switchCount := by
          rw [CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount_ofDirectPathChain,
            switchedChainAux_switchCount target targetPositive parents rfl tail remaining,
            Nat.zero_add]
  | _, _, _, parents, rfl, _, _, .stationary _ _ tail, blocks => by
      simp only [switchedChainAux,
        CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount,
        switchedChainAux_switchCount target targetPositive parents rfl tail blocks]
termination_by structural _ _ _ _ _ _ _ chain _ => chain

@[simp] theorem switchedChain_switchCount
    (target : RFAP.ConstructiveFraction.Rational)
    (targetPositive : 0 < target)
    {depth : Nat} {rootDiameter : RFAP.ConstructiveFraction.Rational}
    (parents : List GeneratedTransportParent)
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      (parents.map GeneratedTransportParent.centeredEdge)
      (start := start) (finish := finish))
    (blocks : SynchronizedDirectBlockRefinement depth rootDiameter
      (parents.map GeneratedTransportParent.centeredEdge)) :
    (switchedChain target targetPositive parents chain blocks).switchCount =
      chain.switchCount :=
  switchedChainAux_switchCount target targetPositive parents rfl chain blocks

end GeneratedTransportRefinement

/-- A bounded generated run retains its actual prepared parents, dependent
lifted chain, strict-width evidence, and the whole moving-cell literal
comparison.  Stationary switches are deliberately added only when the two
sheet runs are closed. -/
structure GeneratedCenteredRun where
  start : CCL.Riemann.LiftedPaths.LiftedPoint 2
  finish : CCL.Riemann.LiftedPaths.LiftedPoint 2
  parents : List (CCL.Riemann.PreparedSubdivisionModels.CenteredEdge
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
    CompactCellData.legendreDifferential)
  chain : CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
    parents (start := start) (finish := finish)
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  literalModels : List CCL.ProgressiveGaussianIntegration.CellModel
  literalRefinement :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantPathRefinement
      (parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
      literalModels
  transportParents : List GeneratedTransportParent
  transportParents_eq :
    transportParents.map GeneratedTransportParent.centeredEdge = parents
  transportLiteralModels_eq :
    transportParents.map GeneratedTransportParent.literalModel = literalModels
  positionTrace : CCL.Riemann.GeneratedCycleProvenance.PositionTrace
  positionTrace_eq :
    positionTrace =
      CCL.Riemann.GeneratedCycleProvenance.PositionTrace.ofList
        GeneratedTransportParent.position transportParents

namespace GeneratedCenteredRun

/-- The dependent switched chain reindexed by the generated transport
parents retained alongside the ordinary parent list. -/
def transportChain (run : GeneratedCenteredRun) :
    CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      (run.transportParents.map GeneratedTransportParent.centeredEdge)
      (start := run.start) (finish := run.finish) :=
  castSwitchedChainParents run.transportParents_eq.symm run.chain

@[simp] theorem transportChain_switchCount (run : GeneratedCenteredRun) :
    run.transportChain.switchCount = run.chain.switchCount := by
  unfold transportChain
  rw [castSwitchedChainParents_switchCount]

/-- Strict-width evidence reindexed onto the retained transport parent
list. -/
theorem transportProper (run : GeneratedCenteredRun) :
    CCL.Riemann.PreparedDyadicRefinements.AllParentsProper
      (run.transportParents.map GeneratedTransportParent.centeredEdge) := by
  rw [run.transportParents_eq]
  exact run.proper

/-- One generated row as the smallest source-centred run. -/
def singleton
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    GeneratedCenteredRun := by
  let parent := cell.centeredEdge
  let canonicalStart : CCL.Riemann.LiftedPaths.LiftedPoint 2 :=
    { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
      sheet := parent.edge.sheet }
  let canonicalFinish : CCL.Riemann.LiftedPaths.LiftedPoint 2 :=
    { coordinate := parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter
      sheet := parent.edge.sheet }
  let start := CompactCellData.liftedStart cell.checked.data cell.sheet
  let finish := CompactCellData.liftedFinish cell.checked.data cell.sheet
  have start_eq : canonicalStart = start := by
    dsimp only [canonicalStart, start, parent]
    rw [cell.centeredEdge_sheet]
    exact congrArg
      (fun coordinate : RFAP.ConstructiveGaussian.Gaussian =>
        ({ coordinate := coordinate, sheet := cell.sheet } :
          CCL.Riemann.LiftedPaths.LiftedPoint 2))
      cell.centeredEdge_start_eq
  have finish_eq : canonicalFinish = finish := by
    dsimp only [canonicalFinish, finish, parent]
    rw [cell.centeredEdge_sheet]
    exact congrArg
      (fun coordinate : RFAP.ConstructiveGaussian.Gaussian =>
        ({ coordinate := coordinate, sheet := cell.sheet } :
          CCL.Riemann.LiftedPaths.LiftedPoint 2))
      cell.centeredEdge_finish_eq
  let canonicalChain :
      CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain
      [parent] (start := canonicalStart) (finish := canonicalFinish) :=
    .edge parent (.nil canonicalFinish)
  let transportParent : GeneratedTransportParent :=
    { rootBits := rootBits
      coefficientBits := coefficientBits
      allowanceBits := allowanceBits
      cell := cell }
  exact
    { start := start
      finish := finish
      parents := [parent]
      chain := castSwitchedChain start_eq finish_eq canonicalChain
      proper := ⟨cell.centeredEdge_proper, True.intro⟩
      literalModels := [cell.checked.data.literalCellModel cell.checked.bounds]
      literalRefinement := .cons (literalPartitionCertificate cell) .nil
      transportParents := [transportParent]
      transportParents_eq := rfl
      transportLiteralModels_eq := rfl
      positionTrace :=
        CCL.Riemann.GeneratedCycleProvenance.PositionTrace.singleton
          cell.checked.data.position
      positionTrace_eq := rfl }

@[simp] theorem singleton_start
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (singleton cell).start =
      CompactCellData.liftedStart cell.checked.data cell.sheet := rfl

@[simp] theorem singleton_finish
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (singleton cell).finish =
      CompactCellData.liftedFinish cell.checked.data cell.sheet := rfl

@[simp] theorem singleton_literalModels
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (singleton cell).literalModels =
      [cell.checked.data.literalCellModel cell.checked.bounds] := rfl

@[simp] theorem singleton_parents
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (singleton cell).parents = [cell.centeredEdge] := rfl

@[simp] theorem singleton_transportParents
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    (singleton cell).transportParents =
      [{ rootBits := rootBits
         coefficientBits := coefficientBits
         allowanceBits := allowanceBits
         cell := cell }] := rfl

/-- Concatenate two already packaged moving runs at one exact lifted
endpoint. -/
def append (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) : GeneratedCenteredRun :=
  let secondChain := castSwitchedChain endpoint.symm rfl second.chain
  { start := first.start
    finish := second.finish
    parents := first.parents ++ second.parents
    chain := first.chain.append secondChain
    proper := appendParentsProper first.proper second.proper
    literalModels := first.literalModels ++ second.literalModels
    literalRefinement := by
      simpa only [List.map_append] using
        appendLiteralRefinement first.literalRefinement second.literalRefinement
    transportParents := first.transportParents ++ second.transportParents
    transportParents_eq := by
      rw [List.map_append, first.transportParents_eq,
        second.transportParents_eq]
    transportLiteralModels_eq := by
      rw [List.map_append, first.transportLiteralModels_eq,
        second.transportLiteralModels_eq]
    positionTrace :=
      CCL.Riemann.GeneratedCycleProvenance.PositionTrace.append
        first.positionTrace second.positionTrace
    positionTrace_eq := by
      rw [first.positionTrace_eq, second.positionTrace_eq]
      exact
        (CCL.Riemann.GeneratedCycleProvenance.PositionTrace.ofList_append
          GeneratedTransportParent.position first.transportParents
            second.transportParents).symm }

@[simp] theorem append_start (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) :
    (first.append second endpoint).start = first.start := rfl

@[simp] theorem append_finish (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) :
    (first.append second endpoint).finish = second.finish := rfl

@[simp] theorem append_literalModels (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) :
    (first.append second endpoint).literalModels =
      first.literalModels ++ second.literalModels := rfl

@[simp] theorem append_parents (first second : GeneratedCenteredRun)
    (endpoint : first.finish = second.start) :
    (first.append second endpoint).parents =
      first.parents ++ second.parents := rfl

/-- Append one exact sheet switch to a moving run.  The parent and literal
lists intentionally remain the nonstationary lists: both switched models
insert the same zero-integral stationary cell separately. -/
def appendStationary (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) : GeneratedCenteredRun := by
  let stationary :=
    CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.singletonStationary
      (curve := CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve)
      (differential := CompactCellData.legendreDifferential) coordinate sheet
  let stationaryAtFinish := castSwitchedChain endpoint.symm rfl stationary
  exact
    { start := run.start
      finish :=
        { coordinate := coordinate
          sheet := CCL.Riemann.BranchCutLifts.otherSheet sheet }
      parents := run.parents
      chain := castSwitchedChainParents (List.append_nil run.parents)
        (run.chain.append stationaryAtFinish)
      proper := run.proper
      literalModels := run.literalModels
      literalRefinement := run.literalRefinement
      transportParents := run.transportParents
      transportParents_eq := run.transportParents_eq
      transportLiteralModels_eq := run.transportLiteralModels_eq
      positionTrace := run.positionTrace
      positionTrace_eq := run.positionTrace_eq }

@[simp] theorem appendStationary_start (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    (run.appendStationary coordinate sheet endpoint).start = run.start := rfl

@[simp] theorem appendStationary_finish (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    (run.appendStationary coordinate sheet endpoint).finish =
      { coordinate := coordinate,
        sheet := CCL.Riemann.BranchCutLifts.otherSheet sheet } := rfl

@[simp] theorem appendStationary_literalModels (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    (run.appendStationary coordinate sheet endpoint).literalModels =
      run.literalModels := rfl

@[simp] theorem appendStationary_parents (run : GeneratedCenteredRun)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    (run.appendStationary coordinate sheet endpoint).parents = run.parents := rfl

end GeneratedCenteredRun

/-- Cached finite shape and allowance data for one generated run.  The parent
count, switch count, and weighted sum are stored as data, with finite proofs
tying them to the canonical run, so scalar preflight is constant-time after
generated rebasing. -/
structure GeneratedParentAllowanceSummary (run : GeneratedCenteredRun) where
  count : Nat
  switchCount : Nat
  weightedUpper : RFAP.ConstructiveFraction.Rational
  count_eq : run.parents.length = count
  switchCount_eq : run.chain.switchCount = switchCount
  totalWeightedAllowance_le :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (run.parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance <=
      weightedUpper

namespace GeneratedParentAllowanceSummary

def singleton
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    GeneratedParentAllowanceSummary (GeneratedCenteredRun.singleton cell) where
  count := 1
  switchCount := 0
  weightedUpper := cell.parentWeightedAllowanceUpper
  count_eq := rfl
  switchCount_eq := by
    unfold GeneratedCenteredRun.singleton
    rw [castSwitchedChain_switchCount]
    rfl
  totalWeightedAllowance_le := by
    rw [GeneratedCenteredRun.singleton_parents]
    unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
    simp only [List.map, List.foldr_cons, List.foldr_nil, _root_.add_zero]
    exact cell.parentWeightedAllowance_le

def append {first second : GeneratedCenteredRun}
    (firstSummary : GeneratedParentAllowanceSummary first)
    (secondSummary : GeneratedParentAllowanceSummary second)
    (endpoint : first.finish = second.start) :
    GeneratedParentAllowanceSummary (first.append second endpoint) where
  count := firstSummary.count + secondSummary.count
  switchCount := firstSummary.switchCount + secondSummary.switchCount
  weightedUpper := firstSummary.weightedUpper + secondSummary.weightedUpper
  count_eq := by
    rw [GeneratedCenteredRun.append_parents, List.length_append,
      firstSummary.count_eq, secondSummary.count_eq]
  switchCount_eq := by
    unfold GeneratedCenteredRun.append
    rw [CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount_append,
      castSwitchedChain_switchCount, firstSummary.switchCount_eq,
      secondSummary.switchCount_eq]
  totalWeightedAllowance_le := by
    rw [GeneratedCenteredRun.append_parents, List.map_append,
      pathModel_totalWeightedAllowance_append]
    exact add_le_add firstSummary.totalWeightedAllowance_le
      secondSummary.totalWeightedAllowance_le

def appendStationary {run : GeneratedCenteredRun}
    (summary : GeneratedParentAllowanceSummary run)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    GeneratedParentAllowanceSummary
      (run.appendStationary coordinate sheet endpoint) where
  count := summary.count
  switchCount := summary.switchCount + 1
  weightedUpper := summary.weightedUpper
  count_eq := by
    rw [GeneratedCenteredRun.appendStationary_parents, summary.count_eq]
  switchCount_eq := by
    unfold GeneratedCenteredRun.appendStationary
    rw [castSwitchedChainParents_switchCount,
      CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount_append,
      castSwitchedChain_switchCount, summary.switchCount_eq,
      CCL.Riemann.PreparedSwitchedRefinements.SwitchedPathChain.switchCount_singletonStationary]
  totalWeightedAllowance_le := by
    rw [GeneratedCenteredRun.appendStationary_parents]
    exact summary.totalWeightedAllowance_le

/-- Replace an accumulated expression by generated numeric checkpoints. -/
def rebase {run : GeneratedCenteredRun}
    (summary : GeneratedParentAllowanceSummary run)
    (count switchCount : Nat)
    (weightedUpper : RFAP.ConstructiveFraction.Rational)
    (count_eq : summary.count = count)
    (switchCount_eq : summary.switchCount = switchCount)
    (weightedUpper_le : summary.weightedUpper <= weightedUpper) :
    GeneratedParentAllowanceSummary run where
  count := count
  switchCount := switchCount
  weightedUpper := weightedUpper
  count_eq := summary.count_eq.trans count_eq
  switchCount_eq := summary.switchCount_eq.trans switchCount_eq
  totalWeightedAllowance_le :=
    summary.totalWeightedAllowance_le.trans weightedUpper_le

private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : RFAP.ConstructiveFraction.Rational) <= value := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

theorem aggregateAllowance_le {run : GeneratedCenteredRun}
    (summary : GeneratedParentAllowanceSummary run) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (run.parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      (summary.count : RFAP.ConstructiveFraction.Rational) *
        summary.weightedUpper := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [List.length_map, summary.count_eq]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    summary.totalWeightedAllowance_le
    (coordinateNatCast_nonnegative summary.count)

end GeneratedParentAllowanceSummary

/-- Cached finite totals for the literal comparison models of one generated
run.  This deliberately stores the totals and their semantic equalities, so
later assembly never has to normalize thousands of coefficient terms. -/
structure GeneratedCenteredRunSummary
    (coefficientBits allowanceBits : Nat) (run : GeneratedCenteredRun) where
  totals : CompactTotals
  count_eq : run.literalModels.length = totals.count
  integralSample_eq :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      run.literalModels).integralSample =
        totals.literalSample coefficientBits
  totalWeightedAllowance_eq :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      run.literalModels).totalWeightedAllowance =
        totals.weightedAllowanceValue allowanceBits
  movementSqSum_eq :
    GeneratedTransportRefinement.movementSqSum run.transportParents =
      totals.movementSqValue
  transportWeightedErrorSum_eq :
    GeneratedTransportRefinement.transportWeightedErrorSum
        run.transportParents =
      totals.transportWeightedErrorValue allowanceBits

namespace GeneratedCenteredRunSummary

/-- The literal model of one generated cell, summarized by the same compact
row total that the external certificate checker validates. -/
def singleton
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (GeneratedCenteredRun.singleton cell) where
  totals := cell.checked.data.totals coefficientBits allowanceBits
  count_eq := rfl
  integralSample_eq := by
    rw [GeneratedCenteredRun.singleton_literalModels,
      CCL.ProgressiveGaussianIntegration.PathModel.singleton_integralSample]
    exact (CompactCellData.totals_literalSample cell.checked.bounds).symm
  totalWeightedAllowance_eq := by
    rw [GeneratedCenteredRun.singleton_literalModels]
    unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
    simp only [List.foldr_cons, List.foldr_nil, _root_.add_zero]
    exact
      (CompactCellData.totals_weightedAllowanceValue cell.checked.bounds).symm
  movementSqSum_eq := by
    rw [GeneratedCenteredRun.singleton_transportParents]
    simp only [GeneratedTransportRefinement.movementSqSum, _root_.add_zero]
    change CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
        cell.centeredEdge.edge.segment
        cell.centeredEdge.edge.left.parameter
        cell.centeredEdge.edge.request.endpoint.parameter = _
    rw [CompactCellData.totals_movementSqValue cell.checked.bounds]
    unfold CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
    rw [cell.centeredEdge_start_eq, cell.centeredEdge_finish_eq]
    rfl
  transportWeightedErrorSum_eq := by
    rw [GeneratedCenteredRun.singleton_transportParents]
    simp only [GeneratedTransportRefinement.transportWeightedErrorSum,
      _root_.add_zero]
    change CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
        cell.centeredEdge.edge.segment
        cell.centeredEdge.edge.left.parameter
        cell.centeredEdge.edge.request.endpoint.parameter *
        (cell.checked.data.transportCoefficientErrorSq
          allowanceBits).toCoordinate = _
    rw [CompactCellData.totals_transportWeightedErrorValue
      cell.checked.bounds]
    unfold CCL.Riemann.PreparedDirectDyadicRefinements.geometricMovement
    rw [cell.centeredEdge_start_eq, cell.centeredEdge_finish_eq]
    rfl

/-- Reuse an independently checked literal-path summary when its model list
is definitionally the one retained by the generated run. -/
def ofLiteralSummary (run : GeneratedCenteredRun)
    {rootBits coefficientBits allowanceBits : Nat}
    {sheet : Fin 2} {start finish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (summary : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits sheet start finish)
    (models_eq : run.literalModels = summary.package.models)
    (movementSqSum_eq :
      GeneratedTransportRefinement.movementSqSum run.transportParents =
        summary.totals.movementSqValue)
    (transportWeightedErrorSum_eq :
      GeneratedTransportRefinement.transportWeightedErrorSum
          run.transportParents =
        summary.totals.transportWeightedErrorValue allowanceBits) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits run where
  totals := summary.totals
  count_eq := by rw [models_eq, summary.count_eq]
  integralSample_eq := by rw [models_eq, summary.integralSample_eq]
  totalWeightedAllowance_eq := by
    rw [models_eq, summary.totalWeightedAllowance_eq]
  movementSqSum_eq := movementSqSum_eq
  transportWeightedErrorSum_eq := transportWeightedErrorSum_eq

/-- Concatenation preserves cached finite totals without recomputation. -/
def append {first second : GeneratedCenteredRun}
    {coefficientBits allowanceBits : Nat}
    (firstSummary : GeneratedCenteredRunSummary coefficientBits allowanceBits first)
    (secondSummary : GeneratedCenteredRunSummary coefficientBits allowanceBits second)
    (endpoint : first.finish = second.start) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (first.append second endpoint) where
  totals := firstSummary.totals.add secondSummary.totals
  count_eq := by
    change (first.literalModels ++ second.literalModels).length =
      firstSummary.totals.count + secondSummary.totals.count
    rw [List.length_append, firstSummary.count_eq, secondSummary.count_eq]
  integralSample_eq := by
    change (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (first.literalModels ++ second.literalModels)).integralSample = _
    rw [pathModel_integralSample_append, firstSummary.integralSample_eq,
      secondSummary.integralSample_eq,
      ← CompactCellData.compactTotals_literalSample_add]
  totalWeightedAllowance_eq := by
    change (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (first.literalModels ++ second.literalModels)).totalWeightedAllowance = _
    rw [pathModel_totalWeightedAllowance_append,
      firstSummary.totalWeightedAllowance_eq,
      secondSummary.totalWeightedAllowance_eq,
      ← CompactCellData.compactTotals_weightedAllowanceValue_add]
  movementSqSum_eq := by
    change GeneratedTransportRefinement.movementSqSum
        (first.transportParents ++ second.transportParents) = _
    rw [GeneratedTransportRefinement.movementSqSum_append,
      firstSummary.movementSqSum_eq, secondSummary.movementSqSum_eq,
      ← CompactCellData.compactTotals_movementSqValue_add]
  transportWeightedErrorSum_eq := by
    change GeneratedTransportRefinement.transportWeightedErrorSum
        (first.transportParents ++ second.transportParents) = _
    rw [GeneratedTransportRefinement.transportWeightedErrorSum_append,
      firstSummary.transportWeightedErrorSum_eq,
      secondSummary.transportWeightedErrorSum_eq,
      ← CompactCellData.compactTotals_transportWeightedErrorValue_add]

/-- A stationary switch changes the lifted chain but not the moving literal
comparison list or its cached totals. -/
def appendStationary {run : GeneratedCenteredRun}
    {coefficientBits allowanceBits : Nat}
    (summary : GeneratedCenteredRunSummary coefficientBits allowanceBits run)
    (coordinate : RFAP.ConstructiveGaussian.Gaussian) (sheet : Fin 2)
    (endpoint : run.finish =
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2)) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits
      (run.appendStationary coordinate sheet endpoint) := by
  exact
    { totals := summary.totals
      count_eq := summary.count_eq
      integralSample_eq := summary.integralSample_eq
      totalWeightedAllowance_eq := summary.totalWeightedAllowance_eq
      movementSqSum_eq := summary.movementSqSum_eq
      transportWeightedErrorSum_eq :=
        summary.transportWeightedErrorSum_eq }

/-- Replace an evaluated totals expression by an equal persisted checkpoint.
The semantic equalities are transported once and downstream users consume
the checkpoint directly. -/
def rebaseTotals {run : GeneratedCenteredRun}
    {coefficientBits allowanceBits : Nat}
    (summary : GeneratedCenteredRunSummary coefficientBits allowanceBits run)
    (totals : CompactTotals) (totals_eq : summary.totals = totals) :
    GeneratedCenteredRunSummary coefficientBits allowanceBits run where
  totals := totals
  count_eq := summary.count_eq.trans (congrArg CompactTotals.count totals_eq)
  integralSample_eq := summary.integralSample_eq.trans
    (congrArg (CompactTotals.literalSample coefficientBits) totals_eq)
  totalWeightedAllowance_eq := summary.totalWeightedAllowance_eq.trans
    (congrArg (CompactTotals.weightedAllowanceValue allowanceBits) totals_eq)
  movementSqSum_eq := summary.movementSqSum_eq.trans
    (congrArg CompactTotals.movementSqValue totals_eq)
  transportWeightedErrorSum_eq :=
    summary.transportWeightedErrorSum_eq.trans
      (congrArg (CompactTotals.transportWeightedErrorValue allowanceBits)
        totals_eq)

theorem aggregateAllowance_eq {run : GeneratedCenteredRun}
    {coefficientBits allowanceBits : Nat}
    (summary : GeneratedCenteredRunSummary coefficientBits allowanceBits run) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      run.literalModels).aggregateAllowance =
        summary.totals.aggregateAllowance allowanceBits := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [summary.count_eq, summary.totalWeightedAllowance_eq,
    CompactTotals.aggregateAllowance_eq_count_mul]

end GeneratedCenteredRunSummary

private theorem liftedPoint_eq_of_coordinate_sheet_eq
    {leftCoordinate rightCoordinate :
      RFAP.ConstructiveGaussian.Gaussian}
    {leftSheet rightSheet : Fin 2}
    (coordinate_eq : leftCoordinate = rightCoordinate)
    (sheet_eq : leftSheet = rightSheet) :
    ({ coordinate := leftCoordinate, sheet := leftSheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2) =
      { coordinate := rightCoordinate, sheet := rightSheet } := by
  cases coordinate_eq
  cases sheet_eq
  rfl

/-- A moving run whose two small generated endpoint indices stay outside the
recursive parent and chain payload. -/
structure GeneratedCenteredRunRange
    {rootBits coefficientBits allowanceBits : Nat}
    (first last :
      GeometricCheckedCell rootBits coefficientBits allowanceBits) where
  run : GeneratedCenteredRun
  start_eq : run.start =
    CompactCellData.liftedStart first.checked.data first.sheet
  finish_eq : run.finish =
    CompactCellData.liftedFinish last.checked.data last.sheet

/-- Endpoint-indexed moving run together with cached literal totals. -/
structure SummarizedGeneratedCenteredRunRange
    {rootBits coefficientBits allowanceBits : Nat}
    (first last :
      GeometricCheckedCell rootBits coefficientBits allowanceBits) where
  range : GeneratedCenteredRunRange first last
  summary : GeneratedCenteredRunSummary coefficientBits allowanceBits range.run
  parentAllowance : GeneratedParentAllowanceSummary range.run

namespace GeneratedCenteredRunRange

/-- Join two generated ranges using one checked coordinate link and one
finite sheet equality. -/
def append
    {rootBits coefficientBits allowanceBits : Nat}
    {first middle next last :
      GeometricCheckedCell rootBits coefficientBits allowanceBits}
    (left : GeneratedCenteredRunRange first middle)
    (right : GeneratedCenteredRunRange next last)
    (coordinate_eq :
      middle.checked.data.finishValue = next.checked.data.startValue)
    (sheet_eq : middle.sheet = next.sheet) :
    GeneratedCenteredRunRange first last := by
  have endpoint : left.run.finish = right.run.start := by
    rw [left.finish_eq, right.start_eq]
    exact liftedPoint_eq_of_coordinate_sheet_eq coordinate_eq sheet_eq
  exact
    { run := left.run.append right.run endpoint
      start_eq := left.start_eq
      finish_eq := right.finish_eq }

end GeneratedCenteredRunRange

namespace SummarizedGeneratedCenteredRunRange

/-- Replace only the totals payload by an equal generated checkpoint. -/
def rebaseTotals
    {rootBits coefficientBits allowanceBits : Nat}
    {first last : GeometricCheckedCell rootBits coefficientBits allowanceBits}
    (summaryRange : SummarizedGeneratedCenteredRunRange first last)
    (totals : CompactTotals)
    (totals_eq : summaryRange.summary.totals = totals) :
    SummarizedGeneratedCenteredRunRange first last where
  range := summaryRange.range
  summary := summaryRange.summary.rebaseTotals totals totals_eq
  parentAllowance := summaryRange.parentAllowance

/-- Replace the accumulated parent count and weighted allowance by generated
numeric checkpoints, preserving the same prepared run. -/
def rebaseParentAllowance
    {rootBits coefficientBits allowanceBits : Nat}
    {first last : GeometricCheckedCell rootBits coefficientBits allowanceBits}
    (summaryRange : SummarizedGeneratedCenteredRunRange first last)
    (count switchCount : Nat)
    (weightedUpper : RFAP.ConstructiveFraction.Rational)
    (count_eq : summaryRange.parentAllowance.count = count)
    (switchCount_eq : summaryRange.parentAllowance.switchCount = switchCount)
    (weightedUpper_le :
      summaryRange.parentAllowance.weightedUpper <= weightedUpper) :
    SummarizedGeneratedCenteredRunRange first last where
  range := summaryRange.range
  summary := summaryRange.summary
  parentAllowance := summaryRange.parentAllowance.rebase count switchCount
    weightedUpper count_eq switchCount_eq weightedUpper_le

/-- Join endpoint-indexed summaries while retaining their small terminal
indices and adding only their cached totals. -/
def append
    {rootBits coefficientBits allowanceBits : Nat}
    {first middle next last :
      GeometricCheckedCell rootBits coefficientBits allowanceBits}
    (left : SummarizedGeneratedCenteredRunRange first middle)
    (right : SummarizedGeneratedCenteredRunRange next last)
    (coordinate_eq :
      middle.checked.data.finishValue = next.checked.data.startValue)
    (sheet_eq : middle.sheet = next.sheet) :
    SummarizedGeneratedCenteredRunRange first last := by
  have endpoint : left.range.run.finish = right.range.run.start := by
    rw [left.range.finish_eq, right.range.start_eq]
    exact liftedPoint_eq_of_coordinate_sheet_eq coordinate_eq sheet_eq
  exact
    { range := left.range.append right.range coordinate_eq sheet_eq
      summary := left.summary.append right.summary endpoint
      parentAllowance := left.parentAllowance.append right.parentAllowance endpoint }

end SummarizedGeneratedCenteredRunRange

/-- Exact endpoint continuity needed to turn a generated row list into one
moving range.  The terminal cell index makes shard endpoints available
without reducing the recursive run. -/
inductive GeneratedCellSequence
    {rootBits coefficientBits allowanceBits : Nat} :
    List (GeometricCheckedCell rootBits coefficientBits allowanceBits) ->
      GeometricCheckedCell rootBits coefficientBits allowanceBits -> Type
  | single (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) :
      GeneratedCellSequence [cell] cell
  | cons (left right :
        GeometricCheckedCell rootBits coefficientBits allowanceBits)
      {remaining : List
        (GeometricCheckedCell rootBits coefficientBits allowanceBits)}
      {last : GeometricCheckedCell rootBits coefficientBits allowanceBits}
      (coordinate_eq :
        left.checked.data.finishValue = right.checked.data.startValue)
      (sheet_eq : left.sheet = right.sheet)
      (tail : GeneratedCellSequence (right :: remaining) last) :
      GeneratedCellSequence (left :: right :: remaining) last

/-- Package a nonempty consecutive row list by structural recursion, keeping
both terminal indices as small range fields. -/
def GeneratedCenteredRun.ofCells
    {rootBits coefficientBits allowanceBits : Nat} :
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) ->
    (remaining : List
      (GeometricCheckedCell rootBits coefficientBits allowanceBits)) ->
    {last : GeometricCheckedCell rootBits coefficientBits allowanceBits} ->
    GeneratedCellSequence (cell :: remaining) last ->
    GeneratedCenteredRunRange cell last
  | cell, [], _, .single _ =>
      { run := singleton cell
        start_eq := singleton_start cell
        finish_eq := singleton_finish cell }
  | cell, right :: remaining, _,
      .cons _ _ coordinate_eq sheet_eq sequence =>
      (GeneratedCenteredRunRange.append
        { run := singleton cell
          start_eq := singleton_start cell
          finish_eq := singleton_finish cell }
        (ofCells right remaining sequence) coordinate_eq sheet_eq)

/-- Simultaneously assemble a consecutive generated run and its compact
literal totals.  The recursion follows the already supplied shallow link
witness, rather than asking the elaborator to reduce a large Boolean proof. -/
def GeneratedCenteredRun.ofCellsSummarized
    {rootBits coefficientBits allowanceBits : Nat} :
    (cell : GeometricCheckedCell rootBits coefficientBits allowanceBits) ->
    (remaining : List
      (GeometricCheckedCell rootBits coefficientBits allowanceBits)) ->
    {last : GeometricCheckedCell rootBits coefficientBits allowanceBits} ->
    (sequence : GeneratedCellSequence (cell :: remaining) last) ->
    SummarizedGeneratedCenteredRunRange cell last
  | cell, [], _, .single _ =>
      { range :=
          { run := singleton cell
            start_eq := singleton_start cell
            finish_eq := singleton_finish cell }
        summary := GeneratedCenteredRunSummary.singleton cell
        parentAllowance := GeneratedParentAllowanceSummary.singleton cell }
  | cell, right :: remaining, _,
      .cons _ _ coordinate_eq sheet_eq sequence =>
      SummarizedGeneratedCenteredRunRange.append
        { range :=
            { run := singleton cell
              start_eq := singleton_start cell
              finish_eq := singleton_finish cell }
          summary := GeneratedCenteredRunSummary.singleton cell
          parentAllowance := GeneratedParentAllowanceSummary.singleton cell }
        (ofCellsSummarized right remaining sequence) coordinate_eq sheet_eq

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
