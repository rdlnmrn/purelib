import CCL.Riemann.ExplicitLegendreLoopBaseBranches

/-!
# Explicit prepared periods at the Legendre loop base

The generic standard-period constructor is total, but its automatic common
subdivision is intentionally conservative and too expensive for executable
normalization examples.  This module supplies small rational square-root
owners at the three displayed branch anchors and will use measured dyadic
banks for the two genus-one cycles.
-/

namespace CCL.Riemann.ExplicitLegendrePreparedPeriods

open CCL.Riemann.ExplicitLegendreLoopBaseBranches

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

def point (x y : Coordinate) : Gaussian := ⟨x, y⟩

/-- A directly displayed reduced rational.  Using the stored Bézout
certificate avoids replaying normalization of the denominator `2048` in
every quadratic boundary check below. -/
def reducedRational (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    Coordinate where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

def q17_8 : Coordinate :=
  reducedRational 17 8 (by decide) 1 (-2) (by decide)

def qNeg137_512 : Coordinate :=
  reducedRational (-137) 512 (by decide) (-71) 19 (by decide)

def q169_128 : Coordinate :=
  reducedRational 169 128 (by decide) 25 (-33) (by decide)

def qNeg5349_4096 : Coordinate :=
  reducedRational (-5349) 4096 (by decide) (-1811) 2365 (by decide)

def q241_512 : Coordinate :=
  reducedRational 241 512 (by decide) 17 (-8) (by decide)

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

private theorem finTwo_cases (index : Fin 2) : index = 0 ∨ index = 1 := by
  rcases index with ⟨value, bound⟩
  omega0

theorem baseBranchData_siteCount : (baseBranchData ()).siteCount = 3 := rfl

def branchIndex (index : Fin 3) :
    CCL.Riemann.BranchIsolation.Data.Index (baseBranchData ()) :=
  Fin.cast baseBranchData_siteCount.symm index

/-! ## Explicit quadratic sheet owners at the branch-box anchors -/

/-- Lower-left anchors of the three large period boxes. -/
def squareRootEndpointPoint : Fin 3 → Gaussian
  | ⟨0, _⟩ => point (-(1 / 2)) (-(1 / 2))
  | ⟨1, _⟩ => point (1 / 8) (3 / 2)
  | ⟨2, _⟩ => point (15 / 16) (-(1 / 2))

/-- The exact Legendre radicands at the three displayed anchors.  Keeping
these as a three-entry table makes the subsequent finite determinant and
winding checks reduce directly, without unfolding polynomial normalization
inside every decision procedure. -/
def squareRootParameter : Fin 3 → Gaussian
  | ⟨0, _⟩ => point q17_8 (-2)
  | ⟨1, _⟩ => point qNeg137_512 q169_128
  | ⟨2, _⟩ => point qNeg5349_4096 q241_512

theorem basePolynomial_eval_squareRootEndpointPoint (index : Fin 3) :
    baseCurve.polynomial.eval (squareRootEndpointPoint index) =
      squareRootParameter index := by
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rw [baseCurve_polynomial,
      CCL.Riemann.LegendrePaths.polynomial_eval] <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    apply RFAP.CanonicalFraction.Rational.ext <;> rfl

/-- Resultant-optimized rational rectangles around the two square roots of
each endpoint radicand.  The second sheet is the point reflection of the
first.  These deliberately asymmetric boxes keep every side far from both
quadratic roots and therefore avoid repeated moving-owner resets. -/
def squareRootOwnerBox : Fin 3 → Fin 2 → Box
  | ⟨0, _⟩, ⟨0, _⟩ =>
      { xLower := 1 / 8
        xUpper := 2
        yLower := -(2 / 3)
        yUpper := 3 / 2
        x_valid := by decide +revert
        y_valid := by decide +revert }
  | ⟨0, _⟩, ⟨1, _⟩ =>
      { xLower := -2
        xUpper := -(1 / 8)
        yLower := -3 / 2
        yUpper := 2 / 3
        x_valid := by decide +revert
        y_valid := by decide +revert }
  | ⟨1, _⟩, ⟨0, _⟩ =>
      { xLower := 1 / 4
        xUpper := 5 / 4
        yLower := 1 / 4
        yUpper := 3 / 2
        x_valid := by decide +revert
        y_valid := by decide +revert }
  | ⟨1, _⟩, ⟨1, _⟩ =>
      { xLower := -5 / 4
        xUpper := -(1 / 4)
        yLower := -3 / 2
        yUpper := -(1 / 4)
        x_valid := by decide +revert
        y_valid := by decide +revert }
  | ⟨2, _⟩, ⟨0, _⟩ =>
      { xLower := 1 / 16
        xUpper := 3 / 4
        yLower := 1 / 2
        yUpper := 3 / 2
        x_valid := by decide +revert
        y_valid := by decide +revert }
  | ⟨2, _⟩, ⟨1, _⟩ =>
      { xLower := -3 / 4
        xUpper := -(1 / 16)
        yLower := -3 / 2
        yUpper := -(1 / 2)
        x_valid := by decide +revert
        y_valid := by decide +revert }

theorem squareRootOwnerBox_proper (index : Fin 3) (sheet : Fin 2) :
    (squareRootOwnerBox index sheet).Proper := by
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;>
    constructor <;> decide

def squareRootPolynomial (index : Fin 3) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial (squareRootParameter index)
    CCL.Riemann.SquareRootSheets.degreeTwo

theorem squareRootParameter_nonzero :
    ∀ index : Fin 3, squareRootParameter index ≠ 0 := by
  intro index
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

theorem squareRootOwner_leftNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xLower ≠
        0 := by
  intro index sheet
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;> decide

theorem squareRootOwner_rightNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xUpper ≠
        0 := by
  intro index sheet
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;> decide

theorem squareRootOwner_bottomNonzero :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yLower ≠
        0 := by
  intro index sheet
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;> decide

theorem squareRootOwner_topNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yUpper ≠
        0 := by
  intro index sheet
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;> decide

theorem squareRootOwner_windingFour :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    RFAP.Winding.quadrupledBoxWinding (squareRootPolynomial index)
      (squareRootOwnerBox index sheet) = 4 := by
  intro index sheet
  rcases finThree_cases index with h | h | h <;> subst index <;>
    rcases finTwo_cases sheet with h | h <;> subst sheet <;> decide

/-- A complete local owner for either square-root sheet at each displayed
branch anchor, without invoking the generic all-root isolator. -/
def squareRootOwner (index : Fin 3) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (squareRootParameter index) :=
  CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox
    (squareRootParameter index) (squareRootParameter_nonzero index)
    (squareRootOwnerBox index sheet)
    (squareRootOwnerBox_proper index sheet)
    (squareRootOwner_leftNonzero index sheet)
    (squareRootOwner_rightNonzero index sheet)
    (squareRootOwner_bottomNonzero index sheet)
    (squareRootOwner_topNonzero index sheet)
    (squareRootOwner_windingFour index sheet)

theorem refinedTrackAnchor_eq_squareRootEndpointPoint : ∀ index : Fin 3,
    CCL.Riemann.BranchCuts.refinedTrackAnchor (baseBranchData ())
        baseCurve_degree_gt_one (branchIndex index) 0 =
      squareRootEndpointPoint index
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

def branchState (index : Fin 3) :=
  CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseBranchStateAt index

theorem branchState_anchor_eq_squareRootEndpointPoint : ∀ index : Fin 3,
    (branchState index).box.anchor = squareRootEndpointPoint index
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

def branchSquareRootOwner (index : Fin 3) (sheet : Fin 2) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (baseCurve.polynomial.eval
        (branchState index).box.anchor) := by
  rw [branchState_anchor_eq_squareRootEndpointPoint]
  rw [basePolynomial_eval_squareRootEndpointPoint]
  exact squareRootOwner index sheet

/-! ## Explicitly bounded prepared path banks -/

/-- Outer refinement tightens the polynomial majorants on the canonical
connectors before the local continuation checker runs. -/
def connectorOuterDepth : Nat := 4

def boundaryOuterDepth : Nat := 2

/-- Measured outer depths for the two raw A-connector segments.  The
horizontal leg succeeds two levels earlier than the vertical leg. -/
def aConnectorOuterDepths : List Nat := [2, 4]

/-- The B connector is horizontal.  Its second raw segment is stationary, so
subdividing that segment sixteen ways only creates duplicate zero-length cells.
Retaining one stationary segment preserves the canonical raw connector while
removing fifteen redundant outer cells from each direction. -/
def bConnectorOuterDepths : List Nat := [4, 0]

/-- Measured outer depths for the four sides of the right A boundary. -/
def rightBoundaryOuterDepths : List Nat := [2, 2, 2, 3]

/-- The left boundary retains its common successful outer depth, expressed
through the same scheduled interface as the other A pieces. -/
def leftBoundaryOuterDepths : List Nat := [2, 2, 2, 2]

/-- Measured local depths are retained per path piece.  The A connector uses
depth five, the scheduled right boundary uses four, the left winding boundary
needs seven, and the two B directions share their least common successful
depth three. -/
def connectorInnerDepth : Nat := 5

def rightBoundaryInnerDepth : Nat := 4

def leftBoundaryInnerDepth : Nat := 7

def bConnectorInnerDepth : Nat := 3

/-- Every displayed owner rectangle admits the measured diameter-`11`
reconditioning request used by all six successful path banks.  Retaining the
smallest common tested value materially tightens every downstream period
allowance without changing the certified meshes. -/
def workingRootDiameter : Coordinate := 11

theorem workingRootDiameter_positive : 0 < workingRootDiameter :=
  RFAP.ConstructiveFraction.natCast_pos_direct (by decide)

abbrev WorkingBank (depth : Nat) {ambient : Box} {start finish : Gaussian}
    (path : CCL.Riemann.BranchCuts.ClearPath baseCurve.polynomial ambient
      start finish)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (baseCurve.polynomial.eval start)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank
    depth workingRootDiameter workingRootDiameter_positive path
      owner

def rawConnector (left right : Fin 3) := by
  let leftState := branchState left
  let rightState := branchState right
  exact CCL.Riemann.BranchCuts.ClearPath.cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil rightState.box.anchor))

theorem rawConnector_withinAmbient (left right : Fin 3) :
    (rawConnector left right).WithinAmbient :=
  .cons
    ⟨(branchState left).refinesAmbient.2.2.1,
      (branchState left).box.y_valid.trans
        (branchState left).refinesAmbient.2.2.2⟩
    (.cons
      ⟨(branchState right).refinesAmbient.1,
        (branchState right).box.x_valid.trans
          (branchState right).refinesAmbient.2.1⟩
      (.nil _))

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

/-- Scheduled refinement of the canonical B connector.  This is geometrically
the same refinement used by the former uniform-depth construction, except that
its stationary second segment is retained only once. -/
def workingBConnector :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawConnector 0 2) (rawConnector_withinAmbient 0 2)
      bConnectorOuterDepths

theorem workingBConnector_withinAmbient : workingBConnector.WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawConnector 0 2) (rawConnector_withinAmbient 0 2)
      bConnectorOuterDepths

def workingBBackwardConnector :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse workingBConnector

theorem workingBBackwardConnector_withinAmbient :
    workingBBackwardConnector.WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
    workingBConnector workingBConnector_withinAmbient

def workingAConnector :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawConnector 0 1) (rawConnector_withinAmbient 0 1)
      aConnectorOuterDepths

theorem workingAConnector_withinAmbient : workingAConnector.WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawConnector 0 1) (rawConnector_withinAmbient 0 1)
      aConnectorOuterDepths

def workingABackwardConnector :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse workingAConnector

theorem workingABackwardConnector_withinAmbient :
    workingABackwardConnector.WithinAmbient :=
  CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
    workingAConnector workingAConnector_withinAmbient

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

def workingRightBoundary :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawBoundary 1) (rawBoundary_withinAmbient 1) rightBoundaryOuterDepths

theorem workingRightBoundary_withinAmbient :
    workingRightBoundary.WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawBoundary 1) (rawBoundary_withinAmbient 1) rightBoundaryOuterDepths

def workingLeftBoundary :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
    (rawBoundary 0) (rawBoundary_withinAmbient 0) leftBoundaryOuterDepths

theorem workingLeftBoundary_withinAmbient :
    workingLeftBoundary.WithinAmbient :=
  CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled_withinAmbient
    (rawBoundary 0) (rawBoundary_withinAmbient 0) leftBoundaryOuterDepths

theorem workingLeftBoundary_eq_uniform :
    workingLeftBoundary = workingBoundary 0 := by
  rfl

opaque aForwardBank? (depth : Nat) :
    Option (WorkingBank depth workingAConnector
      (branchSquareRootOwner 0 0)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingAConnector workingAConnector_withinAmbient
    (branchSquareRootOwner 0 0) depth workingRootDiameter
      workingRootDiameter_positive

opaque aRightBoundaryBank? (depth : Nat) :
    Option (WorkingBank depth workingRightBoundary
      (branchSquareRootOwner 1 0)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingRightBoundary workingRightBoundary_withinAmbient
    (branchSquareRootOwner 1 0) depth workingRootDiameter
      workingRootDiameter_positive

opaque aBackwardBank? (depth : Nat) :
    Option (WorkingBank depth workingABackwardConnector
      (branchSquareRootOwner 1 1)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingABackwardConnector workingABackwardConnector_withinAmbient
    (branchSquareRootOwner 1 1) depth workingRootDiameter
      workingRootDiameter_positive

opaque aLeftBoundaryBank? (depth : Nat) :
    Option (WorkingBank depth workingLeftBoundary
      (branchSquareRootOwner 0 1)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingLeftBoundary workingLeftBoundary_withinAmbient
    (branchSquareRootOwner 0 1) depth workingRootDiameter
      workingRootDiameter_positive

opaque bForwardBank? (depth : Nat) :
    Option (WorkingBank depth workingBConnector
      (branchSquareRootOwner 0 0)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingBConnector workingBConnector_withinAmbient
    (branchSquareRootOwner 0 0) depth workingRootDiameter
      workingRootDiameter_positive

opaque bBackwardBank? (depth : Nat) :
    Option (WorkingBank depth workingBBackwardConnector
      (branchSquareRootOwner 2 1)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.execute?
    workingBBackwardConnector workingBBackwardConnector_withinAmbient
    (branchSquareRootOwner 2 1) depth workingRootDiameter
      workingRootDiameter_positive

/-! ## Measured prepared cycles -/

/-- Assemble the four independently measured A-cycle banks. -/
def executedABoundaryData
    (forward : WorkingBank connectorInnerDepth workingAConnector
      (branchSquareRootOwner 0 0))
    (rightBoundary : WorkingBank rightBoundaryInnerDepth workingRightBoundary
      (branchSquareRootOwner 1 0))
    (backward : WorkingBank connectorInnerDepth workingABackwardConnector
      (branchSquareRootOwner 1 1))
    (leftBoundary : WorkingBank leftBoundaryInnerDepth workingLeftBoundary
      (branchSquareRootOwner 0 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath baseCurve :=
  { leftAmbient := CCL.Riemann.BranchCuts.Ambient baseCurve
    rightAmbient := CCL.Riemann.BranchCuts.Ambient baseCurve
    connectorAmbient := CCL.Riemann.BranchCuts.Ambient baseCurve
    leftState := branchState 0
    rightState := branchState 1
    connector := workingAConnector
    rightBoundaryPath := workingRightBoundary
    leftBoundaryPath := workingLeftBoundary
    forwardDepth := connectorInnerDepth
    rightBoundaryDepth := rightBoundaryInnerDepth
    backwardDepth := connectorInnerDepth
    leftBoundaryDepth := leftBoundaryInnerDepth
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
loop-base A-cycle data. -/
def rawACycleTarget (_ : Unit) :
    CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
    (branchState 0) (branchState 1) (rawConnector 0 1)

/-- Prepared loop-base cycle data cached together with its raw geometric
realization.  Carrying the dependent proof with the executable data avoids
reconstructing the large bank value during downstream elaboration. -/
structure RealizedPreparedCycle
    (raw : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2) where
  data : CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve
  realizes :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw data raw

/-- The four successful measured banks which make up the displayed A cycle.
Keeping them in one payload gives downstream programs one owner for the
finite work instead of six independently callable opaque computations. -/
structure PreparedABanks where
  forward : WorkingBank connectorInnerDepth workingAConnector
    (branchSquareRootOwner 0 0)
  rightBoundary : WorkingBank rightBoundaryInnerDepth workingRightBoundary
    (branchSquareRootOwner 1 0)
  backward : WorkingBank connectorInnerDepth workingABackwardConnector
    (branchSquareRootOwner 1 1)
  leftBoundary : WorkingBank leftBoundaryInnerDepth workingLeftBoundary
    (branchSquareRootOwner 0 1)

/-- The first measured A bank whose executable construction failed. -/
inductive ABankFailureStage
  | forward
  | rightBoundary
  | backward
  | leftBoundary
  deriving DecidableEq, Repr

namespace PreparedABanks

/-- Assemble the cached A-bank payload into its prepared boundary path. -/
def boundaryData (banks : PreparedABanks) :=
  executedABoundaryData banks.forward banks.rightBoundary banks.backward
    banks.leftBoundary

/-- The cached A banks together with the already proved raw-cycle
realization they determine. -/
def witness (banks : PreparedABanks) :
    RealizedPreparedCycle (rawACycleTarget ()) :=
  let boundary := banks.boundaryData
  { data := .finiteCut boundary
    realizes := by
      simpa only [boundary, PreparedABanks.boundaryData,
        executedABoundaryData, rawACycleTarget, rawConnector, branchState,
        branchIndex] using
        (CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw.finiteCutDyadicScheduled
          boundary (rawConnector 0 1)
          (rawConnector_withinAmbient 0 1)
          aConnectorOuterDepths (by
            change workingAConnector = _
            rfl)
          (rawBoundary_withinAmbient 1)
          rightBoundaryOuterDepths (by
            change workingRightBoundary = _
            rfl)
          (rawBoundary_withinAmbient 0)
          leftBoundaryOuterDepths (by
            change workingLeftBoundary = _
            rfl)) }

end PreparedABanks

/-- Execute the displayed A banks in dependency order and retain the exact
stage of the first finite failure. -/
def attemptPreparedABanks (_ : Unit) : Except ABankFailureStage PreparedABanks :=
  match aForwardBank? connectorInnerDepth with
  | none => .error .forward
  | some forward =>
      match aRightBoundaryBank? rightBoundaryInnerDepth with
      | none => .error .rightBoundary
      | some rightBoundary =>
          match aBackwardBank? connectorInnerDepth with
          | none => .error .backward
          | some backward =>
              match aLeftBoundaryBank? leftBoundaryInnerDepth with
              | none => .error .leftBoundary
              | some leftBoundary =>
                  .ok { forward, rightBoundary, backward, leftBoundary }

/-- Conservative total A-cycle construction retained as a proof-producing
fallback if an explicitly bounded execution reports failure. -/
def totalPreparedACycleWitness (_ : Unit) :
    RealizedPreparedCycle (rawACycleTarget ()) := by
  let boundary :=
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.ofFiniteConnectorAtWithOwners
      (baseBranchData ()) baseCurve_degree_gt_one (branchIndex 0)
      (branchIndex 1) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 1 0)
      (branchSquareRootOwner 1 1) (branchSquareRootOwner 0 1)
  exact
    { data := .finiteCut boundary
      realizes := by
        unfold rawACycleTarget rawConnector branchState
        exact .finiteCut boundary rfl rfl }

/-- Data projection of the conservative A-cycle witness. -/
def totalPreparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve :=
  (totalPreparedACycleWitness token).data

/-- Execute all four measured A-cycle banks and cache their raw-realization
proof together with the resulting prepared data.  The token delays this
large construction until an actual finite observation requests it. -/
def executedACycleWitness? (_ : Unit) :
    Option (RealizedPreparedCycle (rawACycleTarget ())) :=
  match attemptPreparedABanks () with
  | .error _stage => none
  | .ok banks => some banks.witness

/-- Data-only compatibility projection of the executed A-cycle checker. -/
def executedACycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve) :=
  match executedACycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached A-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback. -/
def preparedACycleWitness (token : Unit) :
    RealizedPreparedCycle (rawACycleTarget ()) :=
  match executedACycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedACycleWitness token

/-- The explicit A cut prefers the measured executable banks while remaining
total by the general finite preparation theorem. -/
def preparedACycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve :=
  (preparedACycleWitness token).data

/-- Assemble the two measured B-cycle connector banks. -/
def executedBDoubleData
    (forward : WorkingBank bConnectorInnerDepth workingBConnector
      (branchSquareRootOwner 0 0))
    (backward : WorkingBank bConnectorInnerDepth
      workingBBackwardConnector (branchSquareRootOwner 2 1)) :
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath baseCurve :=
  { ambient := CCL.Riemann.BranchCuts.Ambient baseCurve
    start := (branchState 0).box.anchor
    finish := (branchState 2).box.anchor
    basePath := workingBConnector
    depth := bConnectorInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    backwardOwner := branchSquareRootOwner 2 1
    backwardChecked := backward }

/-- The unsubdivided double lift represented by the prepared loop-base
B-cycle data. -/
def rawBCycleTarget (_ : Unit) :
    CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.doubleLift (rawConnector 0 2)

/-- The two successful measured banks which make up the displayed B cycle. -/
structure PreparedBBanks where
  forward : WorkingBank bConnectorInnerDepth workingBConnector
    (branchSquareRootOwner 0 0)
  backward : WorkingBank bConnectorInnerDepth
    workingBBackwardConnector (branchSquareRootOwner 2 1)

/-- The first measured B bank whose executable construction failed. -/
inductive BBankFailureStage
  | forward
  | backward
  deriving DecidableEq, Repr

namespace PreparedBBanks

/-- Assemble the cached B-bank payload into its prepared double path. -/
def doubleData (banks : PreparedBBanks) :=
  executedBDoubleData banks.forward banks.backward

/-- The cached B banks together with the raw-cycle realization they
determine. -/
def witness (banks : PreparedBBanks) :
    RealizedPreparedCycle (rawBCycleTarget ()) :=
  let bridge := banks.doubleData
  { data := .bridge bridge
    realizes :=
      .bridgeDyadicScheduled bridge (rawConnector 0 2)
        (rawConnector_withinAmbient 0 2) bConnectorOuterDepths (by
          change workingBConnector = _
          rfl) }

end PreparedBBanks

/-- Execute the displayed B banks in dependency order and retain the exact
stage of the first finite failure. -/
def attemptPreparedBBanks (_ : Unit) : Except BBankFailureStage PreparedBBanks :=
  match bForwardBank? bConnectorInnerDepth with
  | none => .error .forward
  | some forward =>
      match bBackwardBank? bConnectorInnerDepth with
      | none => .error .backward
      | some backward => .ok { forward, backward }

/-- Conservative total B-cycle construction retained as a fallback. -/
def totalPreparedBCycleWitness (_ : Unit) :
    RealizedPreparedCycle (rawBCycleTarget ()) := by
  let bridge :=
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath.ofFiniteConnectorAtWithOwners
      (baseBranchData ()) baseCurve_degree_gt_one (branchIndex 0)
      (branchIndex 2) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 2 1)
  exact
    { data := .bridge bridge
      realizes := by
        unfold rawBCycleTarget rawConnector branchState
        exact .bridge bridge }

/-- Data projection of the conservative B-cycle witness. -/
def totalPreparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve :=
  (totalPreparedBCycleWitness token).data

/-- Execute both displayed B-cycle banks and cache their raw-realization proof
together with the resulting prepared data. -/
def executedBCycleWitness? (_ : Unit) :
    Option (RealizedPreparedCycle (rawBCycleTarget ())) :=
  match attemptPreparedBBanks () with
  | .error _stage => none
  | .ok banks => some banks.witness

/-- Data-only compatibility projection of the executed B-cycle checker. -/
def executedBCycle? (token : Unit) :
    Option (CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve) :=
  match executedBCycleWitness? token with
  | none => none
  | some witnessed => some witnessed.data

/-- Canonical cached B-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback. -/
def preparedBCycleWitness (token : Unit) :
    RealizedPreparedCycle (rawBCycleTarget ()) :=
  match executedBCycleWitness? token with
  | some witnessed => witnessed
  | none => totalPreparedBCycleWitness token

/-- The explicit B bridge, with the total finite theorem as fallback. -/
def preparedBCycle (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData baseCurve :=
  (preparedBCycleWitness token).data

/-- One runtime owner for the two independent measured bank attempts and
their total theorem-facing witnesses.  The A and B thunks are deliberately
separate: an A-only normalization request cannot force either B bank. -/
structure PreparedLegendreContext where
  aAttempt : Thunk (Except ABankFailureStage PreparedABanks)
  bAttempt : Thunk (Except BBankFailureStage PreparedBBanks)
  aWitness : Thunk (RealizedPreparedCycle (rawACycleTarget ()))
  bWitness : Thunk (RealizedPreparedCycle (rawBCycleTarget ()))

/-- Allocate, but do not force, the measured A and B bank computations.  The
total witness thunks share the corresponding attempt thunk, so a successful
measured payload is never reconstructed and a failed attempt falls back only
when a theorem-facing total witness is actually requested. -/
def preparedLegendreContext (_ : Unit) : PreparedLegendreContext :=
  let aAttempt : Thunk (Except ABankFailureStage PreparedABanks) :=
    ⟨fun _ => attemptPreparedABanks ()⟩
  let bAttempt : Thunk (Except BBankFailureStage PreparedBBanks) :=
    ⟨fun _ => attemptPreparedBBanks ()⟩
  { aAttempt
    bAttempt
    aWitness := aAttempt.map fun result =>
      match result with
      | .ok banks => banks.witness
      | .error _stage => totalPreparedACycleWitness ()
    bWitness := bAttempt.map fun result =>
      match result with
      | .ok banks => banks.witness
      | .error _stage => totalPreparedBCycleWitness () }

namespace PreparedLegendreContext

/-- Force the measured A attempt while retaining its precise failure stage. -/
def measuredA (context : PreparedLegendreContext) := context.aAttempt.get

/-- Force the measured B attempt while retaining its precise failure stage. -/
def measuredB (context : PreparedLegendreContext) := context.bAttempt.get

/-- Force the total A witness.  If `measuredA` has already run, this reuses
its cached payload. -/
def preparedA (context : PreparedLegendreContext) := context.aWitness.get

/-- Force the total B witness independently of the A thunk. -/
def preparedB (context : PreparedLegendreContext) := context.bWitness.get

end PreparedLegendreContext

def branchFamily (_ : Unit) :=
  CCL.Riemann.BranchCutLifts.familyOfData baseCurve (baseBranchData ())

private theorem canonicalACycle_eq_rawData :
    (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) =
      CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
        (branchState 0) (branchState 1) (rawConnector 0 1) := by
  unfold branchFamily
  rw [CCL.Riemann.BranchCutLifts.canonicalACycle_liftedPath_ofData]
  rfl

private theorem canonicalBCycle_eq_rawData :
    (((branchFamily ()).symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) =
      CCL.Riemann.BranchCutLifts.doubleLift (rawConnector 0 2) := by
  unfold branchFamily
  rfl

theorem preparedACycle_realizes_basis (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedACycle token)
      (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact (preparedACycleWitness token).realizes

theorem preparedBCycle_realizes_basis (token : Unit) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      (preparedBCycle token)
      (((branchFamily ()).symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalBCycle_eq_rawData]
  exact (preparedBCycleWitness token).realizes

theorem preparedAOfContext_realizes_basis
    (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      context.preparedA.data
      (((branchFamily ()).symplecticCycles.aCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalACycle_eq_rawData]
  exact context.preparedA.realizes

theorem preparedBOfContext_realizes_basis
    (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.RealizesRaw
      context.preparedB.data
      (((branchFamily ()).symplecticCycles.bCycle (0 : Fin 1)).liftedPath 0) := by
  rw [canonicalBCycle_eq_rawData]
  exact context.preparedB.realizes

/-! ## Explicit period schedule -/

/-- Exact nonstationary cell count of the displayed measured A geometry,
computed without constructing any prepared bank. -/
def aPeriodPreflightParentCount : Nat :=
  2 ^ connectorInnerDepth * workingAConnector.segmentCount +
    (2 ^ rightBoundaryInnerDepth * workingRightBoundary.segmentCount +
      (2 ^ connectorInnerDepth *
          workingABackwardConnector.segmentCount +
        2 ^ leftBoundaryInnerDepth * workingLeftBoundary.segmentCount))

/-- Bank-independent fixed-grid preflight data for the measured A cycle.
The token keeps even this small finite fold out of executable startup. -/
def aPeriodPreflightBounds (_ : Unit) :
    CCL.Riemann.PreparedSwitchedRefinements.CycleSourcePreflightBounds :=
  let source := CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1)
  let count : Coordinate :=
    RFAP.CanonicalFraction.fromInt (Int.ofNat aPeriodPreflightParentCount)
  let totalWeight :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
        source workingRootDiameter connectorInnerDepth workingAConnector +
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source workingRootDiameter rightBoundaryInnerDepth
            workingRightBoundary +
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
            source workingRootDiameter connectorInnerDepth
              workingABackwardConnector +
          CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
            source workingRootDiameter leftBoundaryInnerDepth
              workingLeftBoundary))
  let integralNormSqSum :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
        source workingRootDiameter connectorInnerDepth workingAConnector +
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source workingRootDiameter rightBoundaryInnerDepth
            workingRightBoundary +
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
            source workingRootDiameter connectorInnerDepth
              workingABackwardConnector +
          CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
            source workingRootDiameter leftBoundaryInnerDepth
              workingLeftBoundary))
  { aggregateBound := count * totalWeight
    initialSampleNormSqBound := count * integralNormSqSum }

/-- All five measured A preflight scalars retained in one evaluated record. -/
def aPeriodPreflightSummary (token : Unit) :
    CCL.Riemann.PreparedSwitchedRefinements.CycleSourcePreflightSummary :=
  (aPeriodPreflightBounds token).summary

/-- The explicit A-cycle schedule owned by one retained bank context. -/
def aPeriodScheduleOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedClosedSchedule
      baseCurve where
  source := CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1)
  prepared := context.preparedA.data

/-- The explicit A-cycle schedule can be requested independently of the
full symplectic pair.  This is the shortest executable path to the sole
matrix entry needed by genus-one normalization. -/
def aPeriodSchedule (token : Unit) :=
  aPeriodScheduleOfContext (preparedLegendreContext token)

/-- Fully centred implementation retained as the proof source for the compact
executable facade below. -/
private def centeredAPeriodProgramOfContext
    (context : PreparedLegendreContext) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle :=
  (aPeriodScheduleOfContext context).certifiedPeriodProgram (0 : Fin 1)

/-- Certified `dx/y` program on the explicit A-cycle, with compact preflight
scalars.  The actual finite models and uniform differential certificates are
unchanged, while requesting normalization no longer evaluates their initial
coefficient centres merely to obtain a global sample bound. -/
def aPeriodProgramOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle where
  integral :=
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceIntegral baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
  certificates := by
    intro index
    exact (centeredAPeriodProgramOfContext context).certificates index

/-- Direct refinement index selected by the ordinary public sampler for one
explicit A-period request.  Naming this reindexing here lets both finite
lower certificates and retryable normalization use the same exact state. -/
def aPeriodModelIndex (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Nat :=
  let program := aPeriodProgramOfContext context
  CCL.ProgressiveSampling.stateAt program.integral.approximation.toProcess
    (show program.integral.approximation.toProcess.State from (0 : Nat))
      sampleIndex

/-- Chunkable literal rational certificate for the exact direct refinement
state selected by one public A-period sample.  Its concrete payload can be
generated and checked in small pieces without exposing the thousands of
prepared cells in downstream theorem statements. -/
abbrev APeriodPositiveLiteralRealLowerCertificate
    (context : PreparedLegendreContext) (sampleIndex : Nat) :=
  CCL.Riemann.PreparedSwitchedRefinements.CompactSourcePositiveLiteralRealLowerCertificate
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- The literal certificate bounds the canonical compact model selected by
the same public A-period request. -/
theorem APeriodPositiveLiteralRealLowerCertificate.lower_le_model
    {context : PreparedLegendreContext} {sampleIndex : Nat}
    (certificate : APeriodPositiveLiteralRealLowerCertificate
      context sampleIndex) :
    certificate.lower <=
      (CCL.Riemann.PreparedSwitchedRefinements.compactSourceModel
        (CCL.Riemann.PreparedSwitchedRefinements.compactSourceState baseCurve
          (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
          (aPeriodScheduleOfContext context).prepared)
        (aPeriodModelIndex context sampleIndex)).integralSample.re :=
  CCL.Riemann.PreparedSwitchedRefinements.CompactSourcePositiveLiteralRealLowerCertificate.lower_le_model
    certificate

/-- Sign-aware rational lower endpoint for the real part of the explicit
A-period sample selected by one public request. -/
def aPeriodSampleRealLower (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Coordinate :=
  CCL.Riemann.PreparedSwitchedRefinements.compactSourceIntegralRealLower
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- Sharp sign-aware real endpoint obtained from the coefficient process
balls retained at the selected public A-period sample. -/
def aPeriodSampleBallRealLower (context : PreparedLegendreContext)
    (sampleIndex : Nat) : Coordinate :=
  CCL.Riemann.PreparedSwitchedRefinements.compactSourceBallIntegralRealLower
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex)

/-- The displayed finite box endpoint bounds the real coordinate of the
corresponding public A-period sample. -/
theorem aPeriodSampleRealLower_le
    (context : PreparedLegendreContext) (sampleIndex : Nat) :
    aPeriodSampleRealLower context sampleIndex <=
      ((CCL.ProgressiveSampling.approximation
        (aPeriodProgramOfContext context).output.name).sample sampleIndex).re := by
  exact
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceIntegralRealLower_le_model
      baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex) rfl

theorem aPeriodSampleBallRealLower_le
    (context : PreparedLegendreContext) (sampleIndex : Nat) :
    aPeriodSampleBallRealLower context sampleIndex <=
      ((CCL.ProgressiveSampling.approximation
        (aPeriodProgramOfContext context).output.name).sample sampleIndex).re := by
  exact
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceBallIntegralRealLower_le_model
      baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared
        (aPeriodModelIndex context sampleIndex) rfl

/-- Rational lower endpoint for an arbitrary fixed projection of the explicit
A-period sample selected by one public request. -/
def aPeriodSampleDirectionalLower (context : PreparedLegendreContext)
    (direction : Gaussian) (sampleIndex : Nat) : Coordinate :=
  CCL.Riemann.PreparedSwitchedRefinements.compactSourceDirectionalIntegralLower
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex)

/-- Sharp arbitrary-direction endpoint from the retained coefficient process
balls at one public A-period sample. -/
def aPeriodSampleBallDirectionalLower (context : PreparedLegendreContext)
    (direction : Gaussian) (sampleIndex : Nat) : Coordinate :=
  CCL.Riemann.PreparedSwitchedRefinements.compactSourceBallDirectionalIntegralLower
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex)

/-- The displayed directional endpoint bounds the corresponding projection
of the public A-period sample. -/
theorem aPeriodSampleDirectionalLower_le
    (context : PreparedLegendreContext) (direction : Gaussian)
    (sampleIndex : Nat) :
    aPeriodSampleDirectionalLower context direction sampleIndex <=
      direction.re *
          ((CCL.ProgressiveSampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).re +
        direction.im *
          ((CCL.ProgressiveSampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).im := by
  exact
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceDirectionalIntegralLower_le_model
      baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared direction
        (aPeriodModelIndex context sampleIndex) rfl

theorem aPeriodSampleBallDirectionalLower_le
    (context : PreparedLegendreContext) (direction : Gaussian)
    (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLower context direction sampleIndex <=
      direction.re *
          ((CCL.ProgressiveSampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).re +
        direction.im *
          ((CCL.ProgressiveSampling.approximation
            (aPeriodProgramOfContext context).output.name).sample
              sampleIndex).im := by
  exact
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceBallDirectionalIntegralLower_le_model
      baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared direction
          (aPeriodModelIndex context sampleIndex) rfl

/-- Finite lazy A-state prefix owned by one retained Legendre context. -/
abbrev APeriodCache (context : PreparedLegendreContext) (count : Nat) :=
  CCL.Riemann.PreparedSwitchedRefinements.CompactSourceCache baseCurve
    (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
    (aPeriodScheduleOfContext context).prepared count

/-- Allocate, without forcing, the A refinement states below `count`. -/
def aPeriodCacheOfContext (context : PreparedLegendreContext) (count : Nat) :
    APeriodCache context count :=
  CCL.Riemann.PreparedSwitchedRefinements.CompactSourceCache.canonical
    baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).prepared count

/-- Certified A-period program backed by an explicitly retained finite state
prefix.  The path certificates are transported along the cache's canonical
model equality; no geometric proof is recomputed. -/
def aPeriodProgramOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodScheduleOfContext context).cycle where
  integral :=
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceIntegralOfCache
      baseCurve (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
        (aPeriodScheduleOfContext context).prepared cache
  certificates := by
    intro index
    change CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates
      baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (cache.model index).cells
      ((aPeriodScheduleOfContext context).cycle.liftedPath index).path
    rw [cache.model_eq_compactSourceModel]
    exact (centeredAPeriodProgramOfContext context).certificates index

/-- The explicit A-period real lower endpoint read through a retained direct
state cache.  When the public sample's direct index lies in the cache, both
the sample and this endpoint force the identical stored thunk. -/
def aPeriodSampleRealLowerOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) : Coordinate :=
  cache.integralRealLower (aPeriodModelIndex context sampleIndex)

/-- Sharp real endpoint read through the retained direct-state cache. -/
def aPeriodSampleBallRealLowerOfCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) : Coordinate :=
  cache.ballIntegralRealLower (aPeriodModelIndex context sampleIndex)

/-- Directional A-period endpoint read through the retained direct-state
cache selected by the same public sample request. -/
def aPeriodSampleDirectionalLowerOfCache
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) : Coordinate :=
  cache.directionalIntegralLower direction
    (aPeriodModelIndex context sampleIndex)

/-- Sharp directional endpoint read through the retained direct-state cache. -/
def aPeriodSampleBallDirectionalLowerOfCache
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) : Coordinate :=
  cache.ballDirectionalIntegralLower direction
    (aPeriodModelIndex context sampleIndex)

/-- Reading the real endpoint through a cache does not change its exact
rational value. -/
theorem aPeriodSampleRealLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleRealLowerOfCache context cache sampleIndex =
      aPeriodSampleRealLower context sampleIndex := by
  exact cache.integralRealLower_eq_compactSourceIntegralRealLower
    (aPeriodModelIndex context sampleIndex)

theorem aPeriodSampleBallRealLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleBallRealLowerOfCache context cache sampleIndex =
      aPeriodSampleBallRealLower context sampleIndex := by
  exact cache.ballIntegralRealLower_eq_compactSourceBallIntegralRealLower
    (aPeriodModelIndex context sampleIndex)

/-- Runtime sharing does not change the exact directional endpoint. -/
theorem aPeriodSampleDirectionalLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) :
    aPeriodSampleDirectionalLowerOfCache context cache direction sampleIndex =
      aPeriodSampleDirectionalLower context direction sampleIndex := by
  exact cache.directionalIntegralLower_eq_compactSourceDirectionalIntegralLower
    direction (aPeriodModelIndex context sampleIndex)

theorem aPeriodSampleBallDirectionalLowerOfCache_eq
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLowerOfCache context cache direction
        sampleIndex =
      aPeriodSampleBallDirectionalLower context direction sampleIndex := by
  exact
    cache.ballDirectionalIntegralLower_eq_compactSourceBallDirectionalIntegralLower
      direction (aPeriodModelIndex context sampleIndex)

/-- The cached endpoint bounds the cached direct model selected by the public
sample index.  The acquisition layer identifies this direct index with its
cached public sampler state. -/
theorem aPeriodSampleRealLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleRealLowerOfCache context cache sampleIndex <=
      (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re := by
  exact cache.integralRealLower_le_model
    (aPeriodModelIndex context sampleIndex) rfl

theorem aPeriodSampleBallRealLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (sampleIndex : Nat) :
    aPeriodSampleBallRealLowerOfCache context cache sampleIndex <=
      (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re := by
  exact cache.ballIntegralRealLower_le_model
    (aPeriodModelIndex context sampleIndex) rfl

/-- The cached directional endpoint bounds the matching projection of the
cached direct model. -/
theorem aPeriodSampleDirectionalLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) :
    aPeriodSampleDirectionalLowerOfCache context cache direction sampleIndex <=
      direction.re *
          (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.re +
        direction.im *
          (cache.model (aPeriodModelIndex context sampleIndex)).integralSample.im := by
  exact cache.directionalIntegralLower_le_model direction
    (aPeriodModelIndex context sampleIndex) rfl

theorem aPeriodSampleBallDirectionalLowerOfCache_le_model
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count)
    (direction : Gaussian) (sampleIndex : Nat) :
    aPeriodSampleBallDirectionalLowerOfCache context cache direction
        sampleIndex <=
      direction.re *
          (cache.model
            (aPeriodModelIndex context sampleIndex)).integralSample.re +
        direction.im *
          (cache.model
            (aPeriodModelIndex context sampleIndex)).integralSample.im := by
  exact cache.ballDirectionalIntegralLower_le_model direction
    (aPeriodModelIndex context sampleIndex) rfl

/-- A positive real endpoint yields a squared-norm lower bound for the same
public A-period sample. -/
theorem aPeriodSampleRealLower_sq_le_normSq
    (context : PreparedLegendreContext) (sampleIndex : Nat)
    (positive : 0 < aPeriodSampleRealLower context sampleIndex) :
    aPeriodSampleRealLower context sampleIndex ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveSampling.approximation
          (aPeriodProgramOfContext context).output.name).sample sampleIndex) := by
  let value :=
    (CCL.ProgressiveSampling.approximation
      (aPeriodProgramOfContext context).output.name).sample sampleIndex
  have realLower : aPeriodSampleRealLower context sampleIndex <= value.re :=
    aPeriodSampleRealLower_le context sampleIndex
  calc
    aPeriodSampleRealLower context sampleIndex ^ 2 <= value.re ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct positive.le realLower 2
    _ <= RFAP.ConstructiveGaussian.Gaussian.normSq value := by
      unfold RFAP.ConstructiveGaussian.Gaussian.normSq
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct value.im)

/-- Compatibility entry point which allocates one private retained context. -/
def aPeriodProgram (token : Unit) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (aPeriodSchedule token).cycle :=
  aPeriodProgramOfContext (preparedLegendreContext token)

/-- The matching B-cycle schedule remains independent until a normalized
period observation actually requests the B entry. -/
def bPeriodScheduleOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedClosedSchedule
      baseCurve where
  source := CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1)
  prepared := context.preparedB.data

def bPeriodSchedule (token : Unit) :=
  bPeriodScheduleOfContext (preparedLegendreContext token)

private def centeredBPeriodProgramOfContext
    (context : PreparedLegendreContext) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).cycle :=
  (bPeriodScheduleOfContext context).certifiedPeriodProgram (0 : Fin 1)

/-- Compact-preflight counterpart for the independently delayed B period. -/
def bPeriodProgramOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).cycle where
  integral :=
    CCL.Riemann.PreparedSwitchedRefinements.compactSourceIntegral baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodScheduleOfContext context).prepared
  certificates := by
    intro index
    exact (centeredBPeriodProgramOfContext context).certificates index

def bPeriodProgram (token : Unit) :
    CCL.Riemann.AlgebraicDifferentials.CertifiedPeriodProgram baseCurve
      (CCL.Riemann.PeriodMatrix.standardDifferential (0 : Fin 1))
      (bPeriodSchedule token).cycle :=
  bPeriodProgramOfContext (preparedLegendreContext token)

/-- Complete genus-one schedule built from the displayed branch and
quadratic-owner boxes. -/
def periodScheduleOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedRefinementPrograms.StandardSwitchedSymplecticSchedule
      baseCurve where
  aCycle := fun _ => aPeriodScheduleOfContext context
  bCycle := fun _ => bPeriodScheduleOfContext context

def periodSchedule (token : Unit) :=
  periodScheduleOfContext (preparedLegendreContext token)

/-- A retained context's schedule realizes the displayed symplectic
branch-cut basis at every finite refinement. -/
theorem periodScheduleOfContext_realizes_basis
    (context : PreparedLegendreContext) :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      baseCurve (periodScheduleOfContext context).cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          baseCurve (baseBranchData ())).cycles :=
  .switched (periodScheduleOfContext context) (by
    intro index
    have indexZero : index = 0 := by
      apply Fin.ext
      omega0
    subst index
    exact preparedAOfContext_realizes_basis context) (by
      intro index
      have indexZero : index = 0 := by
        apply Fin.ext
        omega0
      subst index
      exact preparedBOfContext_realizes_basis context)

/-- Compatibility theorem for the privately allocated default context. -/
theorem periodSchedule_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      baseCurve (periodSchedule ()).cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          baseCurve (baseBranchData ())).cycles :=
  periodScheduleOfContext_realizes_basis (preparedLegendreContext ())

/-- Canonical switched finite period programs owned by one retained bank
context.  Projecting the sole A entry leaves the independent B thunk
unforced. -/
def periodDataOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.PeriodMatrix.PeriodData baseCurve where
  cycles := (periodScheduleOfContext context).cycles
  aProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact aPeriodProgramOfContext context
  bProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact bPeriodProgramOfContext context

/-- Period data whose A entry reads through a retained finite cache.  The B
entry remains independently delayed and unchanged. -/
def periodDataOfContextWithACache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    CCL.Riemann.PeriodMatrix.PeriodData baseCurve where
  cycles := (periodScheduleOfContext context).cycles
  aProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact aPeriodProgramOfCache context cache
  bProgram := by
    intro differential cycle
    have differentialZero : differential = 0 := by
      apply Fin.ext
      omega0
    have cycleZero : cycle = 0 := by
      apply Fin.ext
      omega0
    subst differential
    subst cycle
    exact bPeriodProgramOfContext context

/-- Compatibility entry point which allocates one private context for the
complete pair. -/
def periodData (token : Unit) :
    CCL.Riemann.PeriodMatrix.PeriodData baseCurve :=
  periodDataOfContext (preparedLegendreContext token)

/-- The one-by-one A matrix projected from a retained context. -/
def aMatrixOfContext (context : PreparedLegendreContext) :
    CCL.Riemann.PeriodMatrix.NamedMatrix 1 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _differential _cycle =>
    (aPeriodProgramOfContext context).output

/-- The one-by-one A matrix backed by a retained finite state prefix. -/
def aMatrixOfContextWithCache (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    CCL.Riemann.PeriodMatrix.NamedMatrix 1 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _differential _cycle =>
    (aPeriodProgramOfCache context cache).output

theorem aMatrixOfContextWithCache_eq_periodData
    (context : PreparedLegendreContext)
    {count : Nat} (cache : APeriodCache context count) :
    aMatrixOfContextWithCache context cache =
      (periodDataOfContextWithACache context cache).aMatrix := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro differential cycle
  have differentialZero : differential = 0 := by
    apply Fin.ext
    omega0
  have cycleZero : cycle = 0 := by
    apply Fin.ext
    omega0
  subst differential
  subst cycle
  rfl

/-- The A-only projection agrees exactly with the A matrix of the complete
period pair.  Keeping the smaller definition executable prevents the B
schedule from being constructed during normalization preflight. -/
theorem aMatrixOfContext_eq_periodData
    (context : PreparedLegendreContext) :
    aMatrixOfContext context = (periodDataOfContext context).aMatrix := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro differential cycle
  have differentialZero : differential = 0 := by
    apply Fin.ext
    omega0
  have cycleZero : cycle = 0 := by
    apply Fin.ext
    omega0
  subst differential
  subst cycle
  rfl

/-- The one-by-one A matrix exposed through the independent compact A-cycle
program.  Its sole coherent entry is definitionally the entry used by
`periodData`. -/
def aMatrix (token : Unit) :
    CCL.Riemann.PeriodMatrix.NamedMatrix 1 :=
  aMatrixOfContext (preparedLegendreContext token)

/-- The explicit prepared programs realize the symplectic branch-cut basis
generated from the same three rational branch owners. -/
theorem periodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      baseCurve (periodData ()).cycles
        (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
          baseCurve (baseBranchData ())).cycles :=
  periodSchedule_realizes_basis

end CCL.Riemann.ExplicitLegendrePreparedPeriods
