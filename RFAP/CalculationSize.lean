import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import RFAP.Isolation.CalculationSize
import RFAP.Polynomial.ClearingCalculationSize
import RFAP.Polynomial.NormalizedBezoutResource

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace RFAP.PaperCalculationSize

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev WorkingPolynomial := RFAP.NormalizedSturm.WorkingPolynomial
abbrev WorkingCoordinate := RFAP.NormalizedFraction.ReducedFraction
abbrev Box := RFAP.Boxes.Box
abbrev PolynomialEdge := RFAP.Winding.PolynomialEdge

open RFAP.NormalizedPolynomialResource

/-- Binary width of a natural component, with one displayed bit for zero. -/
def natWidth (value : Nat) : Nat := Nat.log2 value + 1

theorem natWidth_mono {left right : Nat} (order : left ≤ right) :
    natWidth left ≤ natWidth right := by
  unfold natWidth
  by_cases leftZero : left = 0
  · rw [leftZero, Nat.log2_zero]
    omega
  · have rightNonzero : right ≠ 0 := by
      intro rightZero
      rw [rightZero] at order
      exact leftZero (Nat.eq_zero_of_le_zero order)
    apply Nat.add_le_add_right
    exact (Nat.le_log2 rightNonzero).2
      ((Nat.log2_self_le leftZero).trans order)

def normalizedEdgeChain (edge : PolynomialEdge) : List WorkingPolynomial :=
  RFAP.NormalizedSturm.signedRemainderChain
    (RFAP.NormalizedSturm.canonicalPolynomial edge.imagPart)
    (RFAP.NormalizedSturm.canonicalPolynomial edge.realPart)

def edgeMagnitudeBudget (edge : PolynomialEdge) : Nat :=
  max (RFAP.NormalizedSturm.endpointMagnitudeEnvelope
      edge.realPart edge.imagPart edge.start)
    (RFAP.NormalizedSturm.endpointMagnitudeEnvelope
      edge.realPart edge.imagPart edge.stop)

structure EdgeResourcesWithin (edge : PolynomialEdge) (bound : Nat) : Prop where
  chainMember : ∀ {candidate : WorkingPolynomial},
    candidate ∈ normalizedEdgeChain edge →
    RFAP.NormalizedSturm.ChainMemberResource
      (RFAP.NormalizedSturm.canonicalPolynomial edge.imagPart)
      (RFAP.NormalizedSturm.canonicalPolynomial edge.realPart) candidate
  startEnvelope : RFAP.NormalizedSturm.endpointMagnitudeEnvelope
    edge.realPart edge.imagPart edge.start ≤ bound
  stopEnvelope : RFAP.NormalizedSturm.endpointMagnitudeEnvelope
    edge.realPart edge.imagPart edge.stop ≤ bound
  erasesToHeadline : RFAP.NormalizedSturm.cauchyIndex2 edge.realPart
      edge.imagPart edge.start edge.stop = edge.doubledWinding

theorem edge_resource (edge : PolynomialEdge) :
    EdgeResourcesWithin edge (edgeMagnitudeBudget edge) := by
  refine
    { chainMember := ?_
      startEnvelope := le_max_left _ _
      stopEnvelope := le_max_right _ _
      erasesToHeadline := RFAP.NormalizedSturm.cauchyIndex2_eq _ _ _ _ }
  · intro candidate member
    exact RFAP.NormalizedSturm.chainMember_resource
      (RFAP.NormalizedSturm.canonicalPolynomial edge.imagPart)
      (RFAP.NormalizedSturm.canonicalPolynomial edge.realPart)
      candidate member

def listMaximum : List Nat → Nat :=
  List.foldl max 0

private theorem foldl_max_initial_le : ∀ (values : List Nat)
    (initial : Nat), initial ≤ values.foldl max initial
  | [], _ => le_refl _
  | _ :: remaining, _ =>
      (le_max_left _ _).trans (foldl_max_initial_le remaining _)

private theorem member_le_foldl_max : ∀ (values : List Nat)
    (initial candidate : Nat), candidate ∈ values →
      candidate ≤ values.foldl max initial
  | [], _, _, member => by simp at member
  | value :: remaining, initial, candidate, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | tail
      · exact (le_max_right _ _).trans
          (foldl_max_initial_le remaining _)
      · exact member_le_foldl_max remaining (max initial value) candidate tail

private theorem member_le_listMaximum (values : List Nat)
    (candidate : Nat) (member : candidate ∈ values) :
    candidate ≤ listMaximum values :=
  member_le_foldl_max values 0 candidate member

def boxWindingMagnitudeBudget (p : GaussianPolynomial) (box : Box) : Nat :=
  listMaximum ((RFAP.Winding.boxBoundary p box).map edgeMagnitudeBudget)

def BoxWindingResourcesWithin (p : GaussianPolynomial) (box : Box)
    (bound : Nat) : Prop :=
  ∀ edge ∈ RFAP.Winding.boxBoundary p box,
    EdgeResourcesWithin edge bound

theorem boxWinding_resource (p : GaussianPolynomial) (box : Box) :
    BoxWindingResourcesWithin p box (boxWindingMagnitudeBudget p box) := by
  intro edge member
  have budgetMember : edgeMagnitudeBudget edge ∈
      (RFAP.Winding.boxBoundary p box).map edgeMagnitudeBudget := by
    rw [QuotientFreeList.mem_map]
    exact ⟨edge, member, rfl⟩
  let resource := edge_resource edge
  let bound := boxWindingMagnitudeBudget p box
  have edgeLe : edgeMagnitudeBudget edge ≤ bound :=
    member_le_listMaximum _ _ budgetMember
  exact
    { chainMember := resource.chainMember
      startEnvelope := resource.startEnvelope.trans edgeLe
      stopEnvelope := resource.stopEnvelope.trans edgeLe
      erasesToHeadline := resource.erasesToHeadline }

def roundBoxes {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient) : List Box :=
  let grid := RFAP.RawSubdivision.safeRawFourGrid elimination state
  [grid.lowerLeft.box, grid.upperLeft.box,
    grid.lowerRight.box, grid.upperRight.box]

def refinementWindingBoxes
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (depth : Nat) : List Box :=
  (List.range depth).flatMap fun round =>
    roundBoxes elimination (RFAP.RawSubdivision.refineN elimination round state)

def refinementWindingMagnitudeBudget
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (depth : Nat) : Nat :=
  listMaximum ((refinementWindingBoxes elimination state depth).map
    (boxWindingMagnitudeBudget p))

def refinementWindingStepBudget
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (depth : Nat) : Nat :=
  ((refinementWindingBoxes elimination state depth).map
    (RFAP.IsolationCalculationSize.boxWindingFieldOperationBudget p)).sum

def dataEnvelopeAdvanceBudget : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, slots =>
      (2 * slots + 2) + dataEnvelopeAdvanceBudget count (2 * slots) +
        8 * (slots +
          RFAP.NormalizedBezoutResource.dataSlotEnvelope count (2 * slots) +
          count + 1)

def eliminantAdvanceBudget (polynomial : GaussianPolynomial) : Nat :=
  let working := RFAP.NormalizedEliminant.canonicalPolynomial polynomial
  let matrix := RFAP.NormalizedEliminant.separatedSylvester working
  dataEnvelopeAdvanceBudget
    ((RFAP.NormalizedEliminant.erasePolynomial working).natDegree +
      (RFAP.NormalizedEliminant.erasePolynomial working).natDegree)
    (RFAP.NormalizedEliminant.matrixSlotBound matrix)

/-- Coarse clause count for lifting and reflecting the displayed coefficient
list and filling the finite separated-Sylvester matrix. -/
def eliminantPreparationBudget (polynomial : GaussianPolynomial) : Nat :=
  let degree := polynomial.natDegree
  let matrixSide := degree + degree
  8 * polynomial.normalize.coeffs.length + matrixSide * matrixSide

def eliminantOperationBudget (polynomial : GaussianPolynomial) : Nat :=
  eliminantPreparationBudget polynomial + eliminantAdvanceBudget polynomial

structure StageThreeInput where
  polynomial : GaussianPolynomial
  ambient : Box
  degreeBound : Nat
  elimination : RFAP.AxisSafeCuts.AxisEliminationCertificate
    polynomial degreeBound
  state : RFAP.RawSubdivision.RawWindingState polynomial ambient
  threshold : Coordinate

namespace StageThreeInput

/-- The standard calculation-size input obtained from the executable
separated-Sylvester axis certificate. -/
def ofSeparated {polynomial : GaussianPolynomial} {ambient : Box}
    (nonzero : polynomial.isZero = false)
    (degreePositive : 0 < polynomial.natDegree)
    (state : RFAP.RawSubdivision.RawWindingState polynomial ambient)
    (threshold : Coordinate) : StageThreeInput where
  polynomial := polynomial
  ambient := ambient
  degreeBound := RFAP.AxisSafeCuts.separatedEliminationDegree polynomial
  elimination := RFAP.AxisSafeCuts.separatedAxisEliminationCertificate
    polynomial nonzero degreePositive
  state := state
  threshold := threshold

def depth (input : StageThreeInput) : Nat :=
  RFAP.RawSubdivision.refinementDepth input.state input.threshold

def horizontalPolynomial (input : StageThreeInput) : GaussianPolynomial :=
  RFAP.ConstructiveSylvesterBezout.quarterTurn input.polynomial

end StageThreeInput

def safeEvaluationCoefficientMagnitude (input : StageThreeInput) : Nat :=
  max (RFAP.NormalizedSturm.coefficientMagnitude
      (RFAP.NormalizedSturm.canonicalPolynomial input.elimination.vertical))
    (RFAP.NormalizedSturm.coefficientMagnitude
      (RFAP.NormalizedSturm.canonicalPolynomial input.elimination.horizontal))

def safeEvaluationSlotBound (input : StageThreeInput) : Nat :=
  max input.elimination.vertical.coeffs.length
    input.elimination.horizontal.coeffs.length

def safeEvaluationMagnitudeBudget (input : StageThreeInput) : Nat :=
  let pointBound := RFAP.IsolationCalculationSize.refinementMagnitudeEnvelope
    input.degreeBound
    (RFAP.IsolationCalculationSize.boxMagnitude input.state.box) input.depth
  grow rationalModel
    (max (safeEvaluationCoefficientMagnitude input) pointBound)
    (2 * safeEvaluationSlotBound input)

/-- Coarse normalized-field-operation count for building both central-third
candidate lists and evaluating both displayed elimination polynomials in one
subdivision round. -/
def safeCutRoundFieldOperationBudget (input : StageThreeInput) : Nat :=
  14 + (input.degreeBound + 1) *
    (10 + 2 * safeEvaluationSlotBound input) + 4

def safeCutFieldOperationBudget (input : StageThreeInput) : Nat :=
  input.depth * safeCutRoundFieldOperationBudget input

def stageThreeCoreMagnitudeBudget (input : StageThreeInput) : Nat :=
  max (RFAP.NormalizedBezoutResource.separatedDataMagnitudeEnvelope
      input.polynomial)
    (max (RFAP.NormalizedBezoutResource.separatedDataMagnitudeEnvelope
        input.horizontalPolynomial)
      (max (max
          (RFAP.ClearingCalculationSize.coefficientDenominatorProduct
            input.polynomial.normalize.coeffs)
          (RFAP.ClearingCalculationSize.clearedCoefficientMagnitudeEnvelope
            input.polynomial.normalize.coeffs))
        (max (RFAP.IsolationCalculationSize.refinementMagnitudeEnvelope
            input.degreeBound
            (RFAP.IsolationCalculationSize.boxMagnitude input.state.box)
            input.depth)
          (refinementWindingMagnitudeBudget input.elimination input.state
            input.depth))))

def stageThreeMagnitudeBudget (input : StageThreeInput) : Nat :=
  max (stageThreeCoreMagnitudeBudget input)
    (safeEvaluationMagnitudeBudget input)

def stageThreeBitBudget (input : StageThreeInput) : Nat :=
  natWidth (stageThreeMagnitudeBudget input)

def stageThreeStepBudget (input : StageThreeInput) : Nat :=
  RFAP.ClearingCalculationSize.coefficientClearingOperationBudget
      input.polynomial.normalize.coeffs +
    eliminantOperationBudget input.polynomial +
    eliminantOperationBudget input.horizontalPolynomial +
    RFAP.IsolationCalculationSize.subdivisionSearchBudget
      input.degreeBound input.depth +
    safeCutFieldOperationBudget input +
    refinementWindingStepBudget input.elimination input.state input.depth

structure StageThreeResourcesWithin (input : StageThreeInput)
    (steps bits : Nat) : Prop where
  coefficientClearingSteps :
    RFAP.ClearingCalculationSize.coefficientClearingOperationBudget
      input.polynomial.normalize.coeffs ≤ steps
  verticalEliminantSteps : eliminantOperationBudget input.polynomial ≤ steps
  horizontalEliminantSteps :
    eliminantOperationBudget input.horizontalPolynomial ≤ steps
  searchCalls : RFAP.IsolationCalculationSize.subdivisionSearchBudget
      input.degreeBound input.depth ≤ steps
  safeCutSteps : safeCutFieldOperationBudget input ≤ steps
  windingSteps : refinementWindingStepBudget input.elimination input.state
      input.depth ≤ steps
  verticalElimination : PolynomialWithin rationalModel
    (RFAP.NormalizedSturm.canonicalPolynomial input.elimination.vertical)
    (stageThreeMagnitudeBudget input)
  horizontalElimination : PolynomialWithin rationalModel
    (RFAP.NormalizedSturm.canonicalPolynomial input.elimination.horizontal)
    (stageThreeMagnitudeBudget input)
  safeEvaluationEnvelope : safeEvaluationMagnitudeBudget input ≤
    stageThreeMagnitudeBudget input
  verticalBezout : RFAP.NormalizedBezoutResource.DataWithin
    (RFAP.NormalizedEliminant.separatedData
      (RFAP.NormalizedEliminant.canonicalPolynomial input.polynomial))
    (stageThreeMagnitudeBudget input)
  horizontalBezout : RFAP.NormalizedBezoutResource.DataWithin
    (RFAP.NormalizedEliminant.separatedData
      (RFAP.NormalizedEliminant.canonicalPolynomial input.horizontalPolynomial))
    (stageThreeMagnitudeBudget input)
  coefficientScale : RFAP.DenominatorHeight.lcmScale
      input.polynomial.normalize.coeffs ≤ stageThreeMagnitudeBudget input
  clearedCoefficients : ∀ coefficient ∈ input.polynomial.normalize.coeffs,
    max
        (RFAP.DenominatorHeight.scaledGaussianCoefficient
          (RFAP.DenominatorHeight.lcmScale input.polynomial.normalize.coeffs)
          coefficient).re.natAbs
        (RFAP.DenominatorHeight.scaledGaussianCoefficient
          (RFAP.DenominatorHeight.lcmScale input.polynomial.normalize.coeffs)
          coefficient).im.natAbs ≤ stageThreeMagnitudeBudget input
  refinedBox : RFAP.IsolationCalculationSize.BoxWithin
    (RFAP.RawSubdivision.refineTo input.elimination input.state input.threshold).box
    (stageThreeMagnitudeBudget input)
  windingBoxes : ∀ box ∈
      refinementWindingBoxes input.elimination input.state input.depth,
    BoxWindingResourcesWithin input.polynomial box
      (stageThreeMagnitudeBudget input)
  bitBudget : natWidth (stageThreeMagnitudeBudget input) = bits

private theorem dataWithin_mono {count : Nat}
    {data : RFAP.NormalizedBezoutResource.ScaledInverseData count}
    {left right : Nat}
    (resource : RFAP.NormalizedBezoutResource.DataWithin data left)
    (order : left ≤ right) :
    RFAP.NormalizedBezoutResource.DataWithin data right :=
  { scalar := polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
      resource.scalar order
    inverse := fun row column =>
      polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
        (resource.inverse row column) order }

theorem stageThree_resource_certificate (input : StageThreeInput) :
    StageThreeResourcesWithin input (stageThreeStepBudget input)
      (stageThreeBitBudget input) := by
  have verticalLe :
      RFAP.NormalizedBezoutResource.separatedDataMagnitudeEnvelope
          input.polynomial ≤ stageThreeMagnitudeBudget input :=
    (le_max_left _ _).trans (le_max_left _ _)
  have horizontalLe :
      RFAP.NormalizedBezoutResource.separatedDataMagnitudeEnvelope
          input.horizontalPolynomial ≤ stageThreeMagnitudeBudget input :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have clearingLe :
      RFAP.ClearingCalculationSize.clearedCoefficientMagnitudeEnvelope
          input.polynomial.normalize.coeffs ≤ stageThreeMagnitudeBudget input :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans (le_max_left _ _)
  have denominatorProductLe :
      RFAP.ClearingCalculationSize.coefficientDenominatorProduct
          input.polynomial.normalize.coeffs ≤ stageThreeMagnitudeBudget input :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans (le_max_left _ _)
  have refinementLe :
      RFAP.IsolationCalculationSize.refinementMagnitudeEnvelope
          input.degreeBound
          (RFAP.IsolationCalculationSize.boxMagnitude input.state.box)
          input.depth ≤ stageThreeMagnitudeBudget input :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans (le_max_left _ _)
  have windingLe : refinementWindingMagnitudeBudget input.elimination
      input.state input.depth ≤ stageThreeMagnitudeBudget input :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans (le_max_left _ _)
  have safeCoefficientLe : safeEvaluationCoefficientMagnitude input ≤
      safeEvaluationMagnitudeBudget input := by
    exact (le_max_left _ _).trans (bound_le_grow rationalModel _ _)
  have safeEvaluationLe : safeEvaluationMagnitudeBudget input ≤
      stageThreeMagnitudeBudget input := le_max_right _ _
  refine
    { coefficientClearingSteps := ?_
      verticalEliminantSteps := ?_
      horizontalEliminantSteps := ?_
      searchCalls := ?_
      safeCutSteps := ?_
      windingSteps := ?_
      verticalElimination := polynomialWithin_mono rationalModel
        (RFAP.NormalizedSturm.polynomial_within_coefficientMagnitude
          (RFAP.NormalizedSturm.canonicalPolynomial
            input.elimination.vertical))
        ((le_max_left _ _).trans (safeCoefficientLe.trans safeEvaluationLe))
      horizontalElimination := polynomialWithin_mono rationalModel
        (RFAP.NormalizedSturm.polynomial_within_coefficientMagnitude
          (RFAP.NormalizedSturm.canonicalPolynomial
            input.elimination.horizontal))
        ((le_max_right _ _).trans (safeCoefficientLe.trans safeEvaluationLe))
      safeEvaluationEnvelope := safeEvaluationLe
      verticalBezout := dataWithin_mono
        (RFAP.NormalizedBezoutResource.normalizedSeparatedData_within
          input.polynomial) verticalLe
      horizontalBezout := dataWithin_mono
        (RFAP.NormalizedBezoutResource.normalizedSeparatedData_within
          input.horizontalPolynomial) horizontalLe
      coefficientScale := ?_
      clearedCoefficients := ?_
      refinedBox := ?_
      windingBoxes := ?_
      bitBudget := rfl }
  · unfold stageThreeStepBudget
    omega
  · unfold stageThreeStepBudget
    omega
  · unfold stageThreeStepBudget
    omega
  · unfold stageThreeStepBudget
    omega
  · unfold stageThreeStepBudget
    omega
  · unfold stageThreeStepBudget
    omega
  · exact (RFAP.ClearingCalculationSize.lcmScale_le_denominatorProduct
      input.polynomial.normalize.coeffs).trans denominatorProductLe
  · intro coefficient member
    exact (RFAP.ClearingCalculationSize.scaledGaussianCoefficient_component_le
      input.polynomial.normalize.coeffs coefficient member).trans clearingLe
  · have resource := RFAP.IsolationCalculationSize.refineTo_box_within
      input.elimination input.state input.threshold
    exact ⟨resource.1.trans refinementLe,
      resource.2.1.trans refinementLe,
      resource.2.2.1.trans refinementLe,
      resource.2.2.2.trans refinementLe⟩
  · intro box member
    have budgetMember : boxWindingMagnitudeBudget input.polynomial box ∈
        (refinementWindingBoxes input.elimination input.state input.depth).map
          (boxWindingMagnitudeBudget input.polynomial) := by
      rw [QuotientFreeList.mem_map]
      exact ⟨box, member, rfl⟩
    have boxLe := (member_le_listMaximum _ _ budgetMember).trans windingLe
    let resource := boxWinding_resource input.polynomial box
    intro edge edgeMember
    let edgeResource := resource edge edgeMember
    exact
      { chainMember := edgeResource.chainMember
        startEnvelope := edgeResource.startEnvelope.trans boxLe
        stopEnvelope := edgeResource.stopEnvelope.trans boxLe
        erasesToHeadline := edgeResource.erasesToHeadline }

end RFAP.PaperCalculationSize
