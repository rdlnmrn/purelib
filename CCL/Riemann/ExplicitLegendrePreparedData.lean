import CCL.Riemann.FinitePeriodTheorem
import CCL.Progressive.PowerMonodromy

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

namespace CCL.Riemann.ExplicitLegendreBranches

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

def point (x y : Coordinate) : Gaussian := ⟨x, y⟩

def factor (x y : Coordinate) : GaussianPolynomial :=
  RFAP.AffineWinding.translatedCoordinate (point x y)

def factors : GaussianPolynomial :=
  (factor (-1) 0 * factor 0 0) * factor 1 0

def polynomial : GaussianPolynomial :=
  ⟨[1, 0, -1, 0]⟩

theorem polynomial_eq_factors : polynomial = factors := by decide

theorem polynomial_nonzero : polynomial.isZero = false := by decide

theorem polynomial_degree : polynomial.natDegree = 3 := by decide

@[simp] theorem polynomial_eval (z : Gaussian) :
    polynomial.eval z = z ^ 3 - z := by
  unfold polynomial RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

def bezoutLeft : GaussianPolynomial := ⟨[point (-9 / 2) 0, 0]⟩

def bezoutRight : GaussianPolynomial := ⟨[point (3 / 2) 0, 0, -1]⟩

@[simp] theorem bezoutLeft_eval (z : Gaussian) :
    bezoutLeft.eval z = point (-9 / 2) 0 * z := by
  unfold bezoutLeft RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem bezoutRight_eval (z : Gaussian) :
    bezoutRight.eval z = point (3 / 2) 0 * z ^ 2 - 1 := by
  unfold bezoutRight RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem derivative_eval (z : Gaussian) :
    (RFAP.ConstructiveGCD.derivative polynomial).eval z = 3 * z ^ 2 - 1 := by
  unfold polynomial RFAP.ConstructiveGCD.derivative
  rw [RFAP.ComputableDerivative.eval_derivative]
  unfold RFAP.ComputableDerivative.evalDerivativeCoeffs
    RFAP.ComputableDerivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

def polynomial_squarefree :
    RFAP.Squarefree.SquarefreeCertificate polynomial :=
  CCL.PowerMonodromy.squarefreeOfEvalBezout polynomial polynomial_nonzero
    bezoutLeft bezoutRight (by
      intro z
      rw [bezoutLeft_eval, polynomial_eval, bezoutRight_eval, derivative_eval]
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        (factor := 2) (by decide)
      have leftScaled : point (-9 / 2) 0 * 2 = -9 := by decide
      have rightScaled : point (3 / 2) 0 * 2 = 3 := by decide
      calc
        (point (-9 / 2) 0 * z * (z ^ 3 - z) +
              (point (3 / 2) 0 * z ^ 2 - 1) * (3 * z ^ 2 - 1)) * 2 =
            (point (-9 / 2) 0 * 2) * z * (z ^ 3 - z) +
              ((point (3 / 2) 0 * 2) * z ^ 2 - 2) *
                (3 * z ^ 2 - 1) := by ring1
        _ = (-9) * z * (z ^ 3 - z) +
              (3 * z ^ 2 - 2) * (3 * z ^ 2 - 1) := by
          rw [leftScaled, rightScaled]
        _ = 1 * 2 := by ring1)

/-- The rational Legendre member `y² = x (x - 1) (x + 1)`. -/
def curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1 where
  polynomial := polynomial
  nonzero := polynomial_nonzero
  squarefree := polynomial_squarefree
  degreeShape := .odd (by
    change polynomial.natDegree = 3
    exact polynomial_degree)

def boxAt (x : Coordinate) : Box :=
  { xLower := x - 1 / 4
    xUpper := x + 1 / 4
    yLower := -1 / 2
    yUpper := 1 / 2
    x_valid := by
      apply le_of_lt
      calc
        x - 1 / 4 < x := by
          simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
        _ < x + 1 / 4 := by
          simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
            (by decide : (0 : Coordinate) < 1 / 4) x
    y_valid := by decide }

theorem boxAt_proper (x : Coordinate) : (boxAt x).Proper := by
  constructor
  · change x - 1 / 4 < x + 1 / 4
    calc
      x - 1 / 4 < x := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
      _ < x + 1 / 4 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 4) x
  · change (-1 / 2 : Coordinate) < 1 / 2
    decide

def selfClearance (x : Coordinate) :
    RFAP.BoxClearance.BoundaryClearance (factor x 0) (boxAt x) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox
    (point x 0) (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by
      unfold boxAt point
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 4) x)
    (by change (-1 / 2 : Coordinate) < 0; decide)
    (by change (0 : Coordinate) < 1 / 2; decide)

def leftClearance (rootX boxX : Coordinate)
    (separated : rootX < boxX - 1 / 4) :
    RFAP.BoxClearance.BoundaryClearance (factor rootX 0) (boxAt boxX) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_left
    (point rootX 0) (by
      unfold boxAt point
      exact separated)

def rightClearance (rootX boxX : Coordinate)
    (separated : boxX + 1 / 4 < rootX) :
    RFAP.BoxClearance.BoundaryClearance (factor rootX 0) (boxAt boxX) :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_right
    (point rootX 0) (by
      unfold boxAt point
      exact separated)

def clearanceMinusOne :
    RFAP.BoxClearance.BoundaryClearance polynomial (boxAt (-1)) := by
  rw [polynomial_eq_factors]
  exact RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (selfClearance (-1)) (rightClearance 0 (-1) (by decide)))
    (rightClearance 1 (-1) (by decide))

def clearanceZero :
    RFAP.BoxClearance.BoundaryClearance polynomial (boxAt 0) := by
  rw [polynomial_eq_factors]
  exact RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (leftClearance (-1) 0 (by decide)) (selfClearance 0))
    (rightClearance 1 0 (by decide))

def clearanceOne :
    RFAP.BoxClearance.BoundaryClearance polynomial (boxAt 1) := by
  rw [polynomial_eq_factors]
  exact RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul
      (leftClearance (-1) 1 (by decide))
      (leftClearance 0 1 (by decide)))
    (selfClearance 1)

def verticalClearance (x : Coordinate)
    (apartMinusOne : x ≠ -1) (apartZero : x ≠ 0)
    (apartOne : x ≠ 1) :
    RFAP.BoxClearance.VerticalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) x := by
  rw [polynomial_eq_factors]
  exact RFAP.BoxClearance.VerticalLineClearance.mul
    (RFAP.BoxClearance.VerticalLineClearance.mul
      (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
        (point (-1) 0) _ x apartMinusOne)
      (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
        (point 0 0) _ x apartZero))
    (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
      (point 1 0) _ x apartOne)

def horizontalClearance (y : Coordinate) (apartZero : y ≠ 0) :
    RFAP.BoxClearance.HorizontalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) y := by
  rw [polynomial_eq_factors]
  exact RFAP.BoxClearance.HorizontalLineClearance.mul
    (RFAP.BoxClearance.HorizontalLineClearance.mul
      (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
        (point (-1) 0) _ y apartZero)
      (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
        (point 0 0) _ y apartZero))
    (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
      (point 1 0) _ y apartZero)

theorem refinesAmbient (x : Coordinate)
    (lowerX : -RFAP.GlobalWinding.denseLargeSquareRadius polynomial ≤
      (boxAt x).xLower)
    (upperX : (boxAt x).xUpper ≤
      RFAP.GlobalWinding.denseLargeSquareRadius polynomial) :
    (boxAt x).Refines (RFAP.GlobalWinding.largeSquareBox polynomial) := by
  unfold RFAP.Boxes.Box.Refines RFAP.GlobalWinding.largeSquareBox
    RFAP.Boxes.Box.symmetric
  exact ⟨lowerX, upperX,
    (by change -RFAP.GlobalWinding.denseLargeSquareRadius polynomial ≤
      (-1 / 2 : Coordinate); decide),
    (by change (1 / 2 : Coordinate) ≤
      RFAP.GlobalWinding.denseLargeSquareRadius polynomial; decide)⟩

theorem windingMinusOne :
    RFAP.Winding.quadrupledBoxWinding polynomial (boxAt (-1)) = 4 := by
  decide

theorem windingZero :
    RFAP.Winding.quadrupledBoxWinding polynomial (boxAt 0) = 4 := by
  decide

theorem windingOne :
    RFAP.Winding.quadrupledBoxWinding polynomial (boxAt 1) = 4 := by
  decide

def rawMinusOne : RFAP.RawSubdivision.RawWindingState polynomial
    (RFAP.GlobalWinding.largeSquareBox polynomial) where
  box := boxAt (-1)
  refinesAmbient := refinesAmbient (-1) (by decide) (by decide)
  proper := boxAt_proper (-1)
  clearance := clearanceMinusOne
  rawWinding_ne := by rw [windingMinusOne]; decide

def rawZero : RFAP.RawSubdivision.RawWindingState polynomial
    (RFAP.GlobalWinding.largeSquareBox polynomial) where
  box := boxAt 0
  refinesAmbient := refinesAmbient 0 (by decide) (by decide)
  proper := boxAt_proper 0
  clearance := clearanceZero
  rawWinding_ne := by rw [windingZero]; decide

def rawOne : RFAP.RawSubdivision.RawWindingState polynomial
    (RFAP.GlobalWinding.largeSquareBox polynomial) where
  box := boxAt 1
  refinesAmbient := refinesAmbient 1 (by decide) (by decide)
  proper := boxAt_proper 1
  clearance := clearanceOne
  rawWinding_ne := by rw [windingOne]; decide

def stateOfRaw
    (raw : RFAP.RawSubdivision.RawWindingState polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial))
    (windingFour : RFAP.Winding.quadrupledBoxWinding polynomial raw.box = 4)
    (left : RFAP.BoxClearance.VerticalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) raw.box.xLower)
    (right : RFAP.BoxClearance.VerticalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) raw.box.xUpper)
    (bottom : RFAP.BoxClearance.HorizontalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) raw.box.yLower)
    (top : RFAP.BoxClearance.HorizontalLineClearance polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) raw.box.yUpper) :
    RFAP.ShrinkingTrack.WindingOneState polynomial
      (RFAP.GlobalWinding.largeSquareBox polynomial) where
  box := raw.box
  refinesAmbient := raw.refinesAmbient
  proper := raw.proper
  clearance := raw.clearance
  rawWindingFour := windingFour
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

def stateMinusOne := stateOfRaw rawMinusOne windingMinusOne
  (verticalClearance (boxAt (-1)).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt (-1)).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt (-1)).yLower (by decide))
  (horizontalClearance (boxAt (-1)).yUpper (by decide))

def stateZero := stateOfRaw rawZero windingZero
  (verticalClearance (boxAt 0).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt 0).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt 0).yLower (by decide))
  (horizontalClearance (boxAt 0).yUpper (by decide))

def stateOne := stateOfRaw rawOne windingOne
  (verticalClearance (boxAt 1).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt 1).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt 1).yLower (by decide))
  (horizontalClearance (boxAt 1).yUpper (by decide))

def stateAt : Fin 3 → RFAP.ShrinkingTrack.WindingOneState polynomial
    (RFAP.GlobalWinding.largeSquareBox polynomial)
  | ⟨0, _⟩ => stateMinusOne
  | ⟨1, _⟩ => stateZero
  | ⟨2, _⟩ => stateOne

theorem stateAt_pairwise : ∀ left right : Fin 3, left ≠ right →
    (stateAt left).box.Separated (stateAt right).box
  | ⟨0, _⟩, ⟨0, _⟩, different => (different rfl).elim
  | ⟨0, _⟩, ⟨1, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide)
  | ⟨0, _⟩, ⟨2, _⟩, _ => Or.inl (by
      change (-3 / 4 : Coordinate) < 3 / 4
      decide)
  | ⟨1, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) < -1 / 4
      decide))
  | ⟨1, _⟩, ⟨1, _⟩, different => (different rfl).elim
  | ⟨1, _⟩, ⟨2, _⟩, _ => Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide)
  | ⟨2, _⟩, ⟨0, _⟩, _ => Or.inr (Or.inl (by
      change (-3 / 4 : Coordinate) < 3 / 4
      decide))
  | ⟨2, _⟩, ⟨1, _⟩, _ => Or.inr (Or.inl (by
      change (1 / 4 : Coordinate) < 3 / 4
      decide))
  | ⟨2, _⟩, ⟨2, _⟩, different => (different rfl).elim

def curveStateAt (index : Fin curve.polynomial.natDegree) :
    RFAP.ShrinkingTrack.WindingOneState curve.polynomial
      (RFAP.GlobalWinding.largeSquareBox curve.polynomial) :=
  stateAt (Fin.cast polynomial_degree index)

theorem curveStateAt_pairwise
    (left right : Fin curve.polynomial.natDegree) (different : left ≠ right) :
    (curveStateAt left).box.Separated (curveStateAt right).box := by
  apply stateAt_pairwise
  intro equal
  apply different
  apply Fin.ext
  exact congrArg Fin.val equal

theorem degreeGtOne : 1 < curve.polynomial.natDegree := by
  change 1 < polynomial.natDegree
  rw [polynomial_degree]
  decide

def branchData : CCL.Riemann.BranchIsolation.Data curve :=
  CCL.Riemann.BranchIsolation.Data.ofStates curve degreeGtOne
    curveStateAt curveStateAt_pairwise

theorem branchData_siteCount : branchData.siteCount = 3 := rfl

/-! ## Exact quadratic owners at the three finite branch anchors -/

def branchIndex (index : Fin 3) :
    CCL.Riemann.BranchIsolation.Data.Index branchData :=
  Fin.cast branchData_siteCount.symm index

def squareRootEndpointPoint : Fin 3 → Gaussian
  | ⟨0, _⟩ => point (-5 / 4) (-1 / 2)
  | ⟨1, _⟩ => point (-1 / 4) (-1 / 2)
  | ⟨2, _⟩ => point (3 / 4) (-1 / 2)

theorem refinedTrackAnchor_eq_squareRootEndpointPoint : ∀ index : Fin 3,
    CCL.Riemann.BranchCuts.refinedTrackAnchor branchData degreeGtOne
        (branchIndex index) 0 = squareRootEndpointPoint index
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

def squareRootParameter (index : Fin 3) : Gaussian :=
  polynomial.eval (squareRootEndpointPoint index)

def positiveSquareRootCenter : Fin 3 → Gaussian
  | ⟨0, _⟩ => point 1 (-1)
  | ⟨1, _⟩ => point (3 / 4) (1 / 3)
  | ⟨2, _⟩ => point 0 (-1)

def squareRootCenter (index : Fin 3) : Fin 2 → Gaussian
  | ⟨0, _⟩ => positiveSquareRootCenter index
  | ⟨1, _⟩ => -positiveSquareRootCenter index

def squareRootOwnerBox (index : Fin 3) (sheet : Fin 2) : Box :=
  RFAP.AffineWinding.centeredSquare (squareRootCenter index sheet)
    (1 / 2) (by decide)

def squareRootPolynomial (index : Fin 3) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial (squareRootParameter index)
    CCL.Riemann.SquareRootSheets.degreeTwo

theorem squareRootParameter_nonzero :
    ∀ index : Fin 3, squareRootParameter index ≠ 0 := by
  decide +revert

theorem squareRootOwner_leftNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xLower ≠
        0 := by
  decide +revert

theorem squareRootOwner_rightNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xUpper ≠
        0 := by
  decide +revert

theorem squareRootOwner_bottomNonzero :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yLower ≠
        0 := by
  decide +revert

theorem squareRootOwner_topNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yUpper ≠
        0 := by
  decide +revert

theorem squareRootOwner_windingFour :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    RFAP.Winding.quadrupledBoxWinding (squareRootPolynomial index)
      (squareRootOwnerBox index sheet) = 4 := by
  decide +revert

def squareRootOwner (index : Fin 3) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (squareRootParameter index) :=
  CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox
    (squareRootParameter index) (squareRootParameter_nonzero index)
    (squareRootOwnerBox index sheet)
    (RFAP.AffineWinding.centeredSquare_proper
      (squareRootCenter index sheet) (by decide))
    (squareRootOwner_leftNonzero index sheet)
    (squareRootOwner_rightNonzero index sheet)
    (squareRootOwner_bottomNonzero index sheet)
    (squareRootOwner_topNonzero index sheet)
    (squareRootOwner_windingFour index sheet)

def branchSquareRootOwner (index : Fin 3) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (curve.polynomial.eval
        (CCL.Riemann.BranchCuts.refinedTrackAnchor branchData degreeGtOne
          (branchIndex index) 0)) := by
  rw [refinedTrackAnchor_eq_squareRootEndpointPoint]
  exact squareRootOwner index sheet

/-! ## Bounded prepared genus-one cycle banks -/

def connectorOuterDepth : Nat := 5
def boundaryOuterDepth : Nat := 3
def workingInnerDepth : Nat := 3
def workingRootDiameter : Coordinate := 3

theorem workingRootDiameter_positive : 0 < workingRootDiameter := by decide

abbrev WorkingBank {ambient : Box} {start finish : Gaussian}
    (path : CCL.Riemann.BranchCuts.ClearPath curve.polynomial ambient
      start finish)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (curve.polynomial.eval start)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank
    workingInnerDepth workingRootDiameter workingRootDiameter_positive path
      owner

def rawConnector (left right : Fin 3) :=
  CCL.Riemann.BranchCuts.finiteConnectorAt branchData degreeGtOne
    (branchIndex left) (branchIndex right) 0

theorem rawConnector_withinAmbient (left right : Fin 3) :
    (rawConnector left right).WithinAmbient :=
  CCL.Riemann.BranchCuts.finiteConnectorAt_withinAmbient branchData
    degreeGtOne (branchIndex left) (branchIndex right) 0

def workingConnector (left right : Fin 3) :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

theorem workingConnector_withinAmbient (left right : Fin 3) :
    (workingConnector left right).WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

def workingBackwardConnector (left right : Fin 3) :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse (workingConnector left right)

theorem workingBackwardConnector_withinAmbient (left right : Fin 3) :
    (workingBackwardConnector left right).WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
    (workingConnector left right) (workingConnector_withinAmbient left right)

def branchState (index : Fin 3) :=
  CCL.Riemann.BranchCuts.refinedState branchData degreeGtOne
    (branchIndex index) 0

def rawBoundary (index : Fin 3) :=
  CCL.Riemann.BranchCutLifts.ownerBoundaryPath (branchState index)

theorem rawBoundary_withinAmbient (index : Fin 3) :
    (rawBoundary index).WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ownerBoundaryPath_withinAmbient
    (branchState index)

def workingBoundary (index : Fin 3) :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

theorem workingBoundary_withinAmbient (index : Fin 3) :
    (workingBoundary index).WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

def aForwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingConnector 0 1) (workingConnector_withinAmbient 0 1)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aRightBoundaryBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBoundary 1) (workingBoundary_withinAmbient 1)
    (branchSquareRootOwner 1 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aBackwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBackwardConnector 0 1)
    (workingBackwardConnector_withinAmbient 0 1)
    (branchSquareRootOwner 1 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def aLeftBoundaryBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBoundary 0) (workingBoundary_withinAmbient 0)
    (branchSquareRootOwner 0 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def executedABoundaryData
    (forward : WorkingBank (workingConnector 0 1)
      (branchSquareRootOwner 0 0))
    (rightBoundary : WorkingBank (workingBoundary 1)
      (branchSquareRootOwner 1 0))
    (backward : WorkingBank (workingBackwardConnector 0 1)
      (branchSquareRootOwner 1 1))
    (leftBoundary : WorkingBank (workingBoundary 0)
      (branchSquareRootOwner 0 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve :=
  { leftAmbient := CCL.Riemann.BranchCuts.Ambient curve
    rightAmbient := CCL.Riemann.BranchCuts.Ambient curve
    connectorAmbient := CCL.Riemann.BranchCuts.Ambient curve
    leftState := branchState 0
    rightState := branchState 1
    connector := workingConnector 0 1
    rightBoundaryPath := workingBoundary 1
    leftBoundaryPath := workingBoundary 0
    forwardDepth := workingInnerDepth
    rightBoundaryDepth := workingInnerDepth
    backwardDepth := workingInnerDepth
    leftBoundaryDepth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    rightBoundaryOwner := branchSquareRootOwner 1 0
    rightBoundaryChecked := rightBoundary
    backwardOwner := branchSquareRootOwner 1 1
    backwardChecked := backward
    leftBoundaryOwner := branchSquareRootOwner 0 1
    leftBoundaryChecked := leftBoundary }

/-- The unsubdivided owner-boundary cycle represented by the prepared
Legendre A-cycle data. -/
def rawACycleTarget : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
    (branchState 0) (branchState 1) (rawConnector 0 1)

/-- Prepared Legendre cycle data cached together with its raw geometric
realization. -/
structure RealizedPreparedCycle
    (raw : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2) where
  data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve
  realizes :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw data raw

/-- Conservative total A-cycle construction retained as a proof-producing
fallback if an explicitly bounded execution reports failure. -/
def totalPreparedACycleWitness (_ : Unit) :
    RealizedPreparedCycle rawACycleTarget := by
  let boundary :=
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.ofFiniteConnectorAtWithOwners
      branchData degreeGtOne (branchIndex 0) (branchIndex 1) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 1 0)
      (branchSquareRootOwner 1 1) (branchSquareRootOwner 0 1)
  exact
    { data := .finiteCut boundary
      realizes := by
        unfold rawACycleTarget rawConnector branchState branchIndex
        exact .finiteCut boundary rfl rfl }

/-- Data projection of the conservative A-cycle witness. -/
def totalPreparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve :=
  (totalPreparedACycleWitness token).data

/-- Execute all four measured A-cycle banks and cache their raw-realization
proof together with the resulting prepared data. -/
def executedACycleWitness? (token : Unit) :
    Option (RealizedPreparedCycle rawACycleTarget) :=
  match aForwardBank? token with
  | none => none
  | some forward =>
      match aRightBoundaryBank? token with
      | none => none
      | some rightBoundary =>
          match aBackwardBank? token with
          | none => none
          | some backward =>
              match aLeftBoundaryBank? token with
              | none => none
              | some leftBoundary =>
                  let boundary := executedABoundaryData forward rightBoundary
                    backward leftBoundary
                  some
                    { data := .finiteCut boundary
                      realizes :=
                        .finiteCutDyadic boundary (rawConnector 0 1)
                          (rawConnector_withinAmbient 0 1)
                          connectorOuterDepth rfl
                          (rawBoundary_withinAmbient 1) boundaryOuterDepth rfl
                          (rawBoundary_withinAmbient 0) boundaryOuterDepth rfl }

/-- Data-only compatibility projection of the executed A-cycle checker. -/
def executedACycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :=
  match executedACycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached A-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  Opacity shares the
checked selection across downstream elaboration while preserving the same
compiled finite program. -/
opaque preparedACycleWitness (token : Unit) :
    RealizedPreparedCycle rawACycleTarget :=
  match executedACycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedACycleWitness token

/-- Canonical genus-one A cut.  The measured executable banks are preferred;
the total finite theorem remains the constructive fallback. -/
def preparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve :=
  (preparedACycleWitness token).data

def bForwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingConnector 0 2) (workingConnector_withinAmbient 0 2)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def bBackwardBank? (_ : Unit) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    (workingBackwardConnector 0 2)
    (workingBackwardConnector_withinAmbient 0 2)
    (branchSquareRootOwner 2 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

def executedBDoubleData
    (forward : WorkingBank (workingConnector 0 2)
      (branchSquareRootOwner 0 0))
    (backward : WorkingBank (workingBackwardConnector 0 2)
      (branchSquareRootOwner 2 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve :=
  { ambient := CCL.Riemann.BranchCuts.Ambient curve
    start := (branchState 0).box.anchor
    finish := (branchState 2).box.anchor
    basePath := workingConnector 0 2
    depth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    backwardOwner := branchSquareRootOwner 2 1
    backwardChecked := backward }

/-- The unsubdivided double lift represented by the prepared Legendre
B-cycle data. -/
def rawBCycleTarget : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLift (rawConnector 0 2)

/-- Conservative total B-cycle construction retained as a fallback. -/
def totalPreparedBCycleWitness (_ : Unit) :
    RealizedPreparedCycle rawBCycleTarget := by
  let bridge :=
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath.ofFiniteConnectorAtWithOwners
      branchData degreeGtOne (branchIndex 0) (branchIndex 2) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 2 1)
  exact
    { data := .bridge bridge
      realizes := by
        unfold rawBCycleTarget rawConnector branchIndex
        exact .bridge bridge }

/-- Data projection of the conservative B-cycle witness. -/
def totalPreparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve :=
  (totalPreparedBCycleWitness token).data

/-- Execute both measured B-cycle banks and cache their raw-realization proof
together with the resulting prepared data. -/
def executedBCycleWitness? (token : Unit) :
    Option (RealizedPreparedCycle rawBCycleTarget) :=
  match bForwardBank? token with
  | none => none
  | some forward =>
      match bBackwardBank? token with
      | none => none
      | some backward =>
          let bridge := executedBDoubleData forward backward
          some
            { data := .bridge bridge
              realizes :=
                .bridgeDyadic bridge (rawConnector 0 2)
                  (rawConnector_withinAmbient 0 2) connectorOuterDepth rfl }

/-- Data-only compatibility projection of the executed B-cycle checker. -/
def executedBCycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :=
  match executedBCycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached B-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  This is the B-cycle
counterpart of the A-cycle elaboration cache boundary. -/
opaque preparedBCycleWitness (token : Unit) :
    RealizedPreparedCycle rawBCycleTarget :=
  match executedBCycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedBCycleWitness token

/-- Canonical genus-one B bridge, preferring the measured executable banks. -/
def preparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve :=
  (preparedBCycleWitness token).data

def branchFamily :=
  CCL.Riemann.BranchCutLifts.familyOfData curve branchData

end CCL.Riemann.ExplicitLegendreBranches
