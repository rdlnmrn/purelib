import CCL.Riemann.PreparedClearPathModels
import CCL.Riemann.PeriodMatrix

/-!
# Prepared finite models for lifted hyperelliptic cycles

Prepared clear paths already carry uniform algebraic certificates on a fixed
sheet.  This module concatenates those finite pieces with exact stationary
switch cells.  Owner-boundary cycles keep their winding-one boundary paths
explicit before each switch, so a sheet transition is never represented by
an unrelated nonbranch shortcut.
-/

namespace CCL.Riemann.PreparedCycleModels

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev WedgeChart {genus : Nat} (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus) :=
  CCL.Riemann.PreparedSubdivisionModels.WedgeChart curve leftDifferential
    rightDifferential
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev CompatibleConstantPathRefinement :=
  CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
abbrev PreparedPath
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath path owner
abbrev DyadicBank
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (path : ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank depth
    rootDiameter rootDiameterPositive path owner

/-- One finite lifted path together with cell-for-cell uniform algebraic
semantics for a fixed differential. -/
structure CertifiedLift {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {start finish : LiftedPoint 2}
    (path : LiftedPath 2 start finish) where
  cells : List CellModel
  certificates : UniformPathCertificates curve differential cells path

/-- The one-cell lifted path underlying a stationary sheet transition. -/
def stationarySwitchPath (coordinate : Gaussian) (sheet : Fin 2) :
    LiftedPath 2
      { coordinate := coordinate, sheet := sheet }
      { coordinate := coordinate, sheet := otherSheet sheet } :=
  .cons (switchCell coordinate sheet)
    (.nil { coordinate := coordinate, sheet := otherSheet sheet })

/-- The exact-zero local wedge certificate attached to a stationary sheet
transition.  The corresponding integration cell has zero displacement and
the exact zero polynomial model for every differential. -/
def stationaryWedgeChart {genus : Nat}
    (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus) :
    WedgeChart curve leftDifferential rightDifferential where
  coefficient := fun _fraction _inside =>
    CCL.ProgressiveCoherence.CoherentNamed.exact 0
  zero := fun _fraction _inside =>
    CCL.OperationalEquivalence.NamedEquivalent.refl
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

namespace CertifiedLift

/-- Concatenate two certified lifted pieces meeting at the same displayed
lifted point. -/
def append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {start middle finish : LiftedPoint 2}
    {firstPath : LiftedPath 2 start middle}
    {secondPath : LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath) :
    CertifiedLift curve differential (firstPath.append secondPath) where
  cells := first.cells ++ second.cells
  certificates := UniformPathCertificates.append firstPath first.certificates
    second.certificates

@[simp] theorem append_integralSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {start middle finish : LiftedPoint 2}
    {firstPath : LiftedPath 2 start middle}
    {secondPath : LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (first.append second).cells).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          first.cells).integralSample +
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            second.cells).integralSample := by
  exact CCL.ProgressiveGaussianIntegration.PathModel.integralSample_mk_append
    first.cells second.cells

/-- A stationary sheet transition has the exact zero model and therefore
needs no quotient query. -/
def switch {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    CertifiedLift curve differential (stationarySwitchPath coordinate sheet) := by
  let model := CCL.ProgressiveGaussianIntegration.CellModel.exact
    coordinate coordinate (CCL.FiniteGaussianPolynomial.constant 0)
  exact
    { cells := [model]
      certificates := .cons rfl rfl (.stationary rfl) (.nil _) }

@[simp] theorem switch_integralSample {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (switch curve differential coordinate sheet).cells).integralSample = 0 := by
  unfold switch CCL.ProgressiveGaussianIntegration.PathModel.integralSample
    CCL.ProgressiveGaussianIntegration.CellModel.integralSample
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.ProgressiveGaussianIntegration.CellModel.exact
  simp only [List.foldr_cons, List.foldr_nil,
    RFAP.ConstructiveGaussian.Gaussian.sub_self,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add]

/-- Forget the preparation data after retaining its exact refined lift and
uniform certificates. -/
def ofPreparedPath {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    CertifiedLift curve differential
      (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet sheet
        prepared.toClearPath) :=
  let certified := prepared.certify curve differential sheet
  { cells := certified.cells
    certificates := certified.certificates }

/-- Constant-cell evidence is preserved when a prepared clear path is viewed
as one certified lifted bank. -/
def ofPreparedPath_constantCells {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    {ambient : Box} {start finish : Gaussian}
    {path : ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedPath path owner) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (ofPreparedPath curve differential sheet prepared).cells :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.certify_constantCells
    curve differential sheet prepared

/-- A stationary switch uses the exact constant-zero cell. -/
def switch_constantCells {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus)
    (coordinate : Gaussian) (sheet : Fin 2) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (switch curve differential coordinate sheet).cells :=
  .cons
    (CCL.ProgressiveGaussianIntegration.CellModel.exactConstantCertificate
      coordinate coordinate 0)
    .nil

/-- Concatenating certified lifts preserves their constant-cell evidence. -/
def append_constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {start middle finish : LiftedPoint 2}
    {firstPath : LiftedPath 2 start middle}
    {secondPath : LiftedPath 2 middle finish}
    (first : CertifiedLift curve differential firstPath)
    (second : CertifiedLift curve differential secondPath)
    (firstConstant :
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells first.cells)
    (secondConstant :
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells second.cells) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (first.append second).cells :=
  firstConstant.append secondConstant

/-- The model list has exactly one entry for every lifted geometric cell. -/
theorem cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certified : CertifiedLift curve differential path) :
    certified.cells.length = path.cellCount :=
  LiftedPath.followedBy_length
    (UniformPathCertificates.toFollowedBy certified.certificates)

end CertifiedLift

/-- A closed lifted model with all of its finite uniform differential
certificates. -/
structure CertifiedClosedModel {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  lifted : ClosedLiftedPath 2
  cells : List CellModel
  certificates : UniformPathCertificates curve differential cells lifted.path

namespace CertifiedClosedModel

@[simp] theorem cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (model : CertifiedClosedModel curve differential) :
    model.cells.length = model.lifted.cellCount :=
  LiftedPath.followedBy_length
    (UniformPathCertificates.toFollowedBy model.certificates)

end CertifiedClosedModel

/-- Prepared forward and reverse banks of one auxiliary two-bank bridge.
The reverse bank is required to refine the actual reversed base path. -/
structure PreparedDoublePath {genus : Nat}
    (curve : HyperellipticCurve genus) where
  ambient : Box
  start : Gaussian
  finish : Gaussian
  basePath : ClearPath curve.polynomial ambient start finish
  depth : Nat
  rootDiameter : Coordinate
  rootDiameterPositive : 0 < rootDiameter
  forwardOwner : Owner (curve.polynomial.eval start)
  forwardChecked : DyadicBank depth rootDiameter rootDiameterPositive
    basePath forwardOwner
  backwardOwner : Owner (curve.polynomial.eval finish)
  backwardChecked : DyadicBank depth rootDiameter rootDiameterPositive
    (CCL.Riemann.BranchCutLifts.ClearPath.reverse basePath) backwardOwner

namespace PreparedDoublePath

/-- Construct both banks at one computed common depth.  No dyadic acceptance
or clearance comparison is supplied by the caller. -/
def total {genus : Nat} {curve : HyperellipticCurve genus}
    {ambient : Box} {start finish : Gaussian}
    (basePath : ClearPath curve.polynomial ambient start finish)
    (within : basePath.WithinAmbient)
    (forwardOwner : Owner (curve.polynomial.eval start))
    (backwardOwner : Owner (curve.polynomial.eval finish))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    PreparedDoublePath curve := by
  let backwardPath :=
    CCL.Riemann.BranchCutLifts.ClearPath.reverse basePath
  let forwardDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth basePath rootDiameter
  let backwardDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth backwardPath
      rootDiameter
  let depth := max forwardDepth backwardDepth
  exact
    { ambient := ambient
      start := start
      finish := finish
      basePath := basePath
      depth := depth
      rootDiameter := rootDiameter
      rootDiameterPositive := rootDiameterPositive
      forwardOwner := forwardOwner
      forwardChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            basePath within forwardOwner depth rootDiameter rootDiameterPositive
              (by
                dsimp only [depth, forwardDepth]
                exact le_max_left _ _))
      backwardOwner := backwardOwner
      backwardChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            backwardPath
              (CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
                basePath within)
              backwardOwner depth rootDiameter rootDiameterPositive
                (by
                  dsimp only [depth, backwardDepth]
                  exact le_max_right _ _)) }

/-- Total preparation of the canonical connector from two caller-supplied
local square-root owners.  This finite entry point lets audited examples reuse
displayed quadratic boxes instead of rerunning global all-root isolation. -/
def ofFiniteConnectorAtWithOwners {genus : Nat}
    {curve : HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne left refinement)))
    (backwardOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne right refinement))) :
    PreparedDoublePath curve :=
  total
    (finiteConnectorAt branches degreeGtOne left right refinement)
    (finiteConnectorAt_withinAmbient branches degreeGtOne left right refinement)
    forwardOwner backwardOwner 1 (by decide)

/-- Total preparation of the canonical connector between two isolated finite
branch occurrences at one displayed root-box refinement.  The two banks use
the canonical independent square-root owners for sheets zero and one. -/
def ofFiniteConnectorAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat) : PreparedDoublePath curve :=
  total
    (finiteConnectorAt branches degreeGtOne left right refinement)
    (finiteConnectorAt_withinAmbient branches degreeGtOne left right refinement)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent
      (finiteConnectorAt_start_eval_ne_zero branches degreeGtOne left right
        refinement) 0)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent
      (finiteConnectorAt_finish_eval_ne_zero branches degreeGtOne left right
        refinement) 1)
    1 (by decide)

/-- Ambient containment derived from the forward finite mesh certificate. -/
theorem within {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve) : data.basePath.WithinAmbient :=
  data.forwardChecked.within

/-- Forward prepared bank derived from its rational mesh checks. -/
def forward {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    PreparedPath data.basePath data.forwardOwner :=
  data.forwardChecked.prepared

/-- Reverse prepared bank derived from its rational mesh checks. -/
def backward {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    PreparedPath
      (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.basePath)
        data.backwardOwner :=
  data.backwardChecked.prepared

/-- The closed lifted geometry selected by the two prepared banks. -/
def closedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve) : ClosedLiftedPath 2 :=
  { basepoint := { coordinate := data.start, sheet := 0 }
    path :=
      (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 0
        data.forward.toClearPath).append
          ((stationarySwitchPath data.finish 0).append
            ((CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 1
              data.backward.toClearPath).append
                (stationarySwitchPath data.start 1))) }

/-- The mesh-aligned closed bridge: forward on sheet zero, one stationary
switch, the prepared reverse on sheet one, and the closing stationary switch. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) :
    CertifiedClosedModel curve differential := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let atFinish := CertifiedLift.switch curve differential data.finish 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let atStart := CertifiedLift.switch curve differential data.start 1
  let combined := forward.append
    (atFinish.append (backward.append atStart))
  exact
    { lifted := data.closedLift
      cells := combined.cells
      certificates := combined.certificates }

/-- Centre-free real endpoint of the two nonstationary bridge pieces. -/
def integralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) : Coordinate :=
  data.forward.integralRealLower curve differential 0 +
    data.backward.integralRealLower curve differential 1

/-- Centre-free endpoint of the two bridge pieces in one arbitrary rational
direction. -/
def directionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus)
    (direction : Gaussian) : Coordinate :=
  data.forward.directionalIntegralLower curve differential 0 direction +
    data.backward.directionalIntegralLower curve differential 1 direction

theorem certifiedModel_integralSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (data.certifiedModel differential).cells).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (CertifiedLift.ofPreparedPath curve differential 0
            data.forward).cells).integralSample +
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (CertifiedLift.ofPreparedPath curve differential 1
              data.backward).cells).integralSample := by
  unfold certifiedModel
  simp only [CertifiedLift.append_integralSample,
    CertifiedLift.switch_integralSample,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]

theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  have forwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.forward
  have backwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.backward
  rw [data.certifiedModel_integralSample differential,
    RFAP.ConstructiveGaussian.Gaussian.add_re]
  exact add_le_add forwardLower backwardLower

theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  have forwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.forward
  have backwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.backward
  rw [data.certifiedModel_integralSample differential]
  unfold CertifiedLift.ofPreparedPath
  simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im]
  exact (add_le_add forwardLower backwardLower).trans_eq (by ring1)

/-- Every cell of the prepared two-bank bridge is Gaussian constant. -/
def certifiedModel_constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (data.certifiedModel differential).cells := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let atFinish := CertifiedLift.switch curve differential data.finish 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let atStart := CertifiedLift.switch curve differential data.start 1
  exact
    (CertifiedLift.ofPreparedPath_constantCells curve differential 0
      data.forward).append
      ((CertifiedLift.switch_constantCells curve differential data.finish 0).append
        ((CertifiedLift.ofPreparedPath_constantCells curve differential 1
          data.backward).append
            (CertifiedLift.switch_constantCells curve differential data.start 1)))

/-- All nonstationary zero-wedge charts on the two prepared banks, with one
exact-zero chart for each stationary sheet switch. -/
def wedgeCharts {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (leftDifferential rightDifferential : Differential genus) :
    List (WedgeChart curve leftDifferential rightDifferential) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
      leftDifferential rightDifferential 0 data.forward ++
    [stationaryWedgeChart curve leftDifferential rightDifferential] ++
      CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
          leftDifferential rightDifferential 1 data.backward ++
        [stationaryWedgeChart curve leftDifferential rightDifferential]

@[simp] theorem certifiedModel_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      data.forward.stepCount + 1 + (data.backward.stepCount + 1) := by
  rw [← CertifiedClosedModel.cellCount]
  simp only [certifiedModel, CertifiedLift.append, CertifiedLift.switch,
    CertifiedLift.ofPreparedPath, List.length_append, List.length_cons,
    List.length_nil,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.certify_cellCount,
    Nat.zero_add, Nat.add_assoc]

/-- Both banks use the same canonical dyadic mesh, so the complete finite
bridge has an exact executable cell count. -/
theorem certifiedModel_cellCount_eq_dyadic {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (differential : Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      2 * (2 ^ data.depth * data.basePath.segmentCount) + 2 := by
  rw [certifiedModel_cellCount]
  simp only [forward, backward]
  rw [
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    CCL.Riemann.BranchCutLifts.ClearPath.segmentCount_reverse]
  omega0

/-- The closed bridge's local holomorphicity data is cell-for-cell with either
of its differential integration models. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve)
    (leftDifferential rightDifferential : Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  rw [CertifiedClosedModel.cellCount,
    data.certifiedModel_cellCount leftDifferential]
  simp only [wedgeCharts, List.length_append, List.length_cons,
    List.length_nil,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts_length]
  omega0

end PreparedDoublePath

/-- Prepared data for a finite cut whose endpoint transitions are justified
by explicit winding-one owner boundaries.  Both banks share one displayed
connector up to reversal. -/
structure PreparedBoundaryDoublePath {genus : Nat}
    (curve : HyperellipticCurve genus) where
  leftAmbient : Box
  rightAmbient : Box
  connectorAmbient : Box
  leftState : RFAP.ShrinkingTrack.WindingOneState curve.polynomial leftAmbient
  rightState : RFAP.ShrinkingTrack.WindingOneState curve.polynomial rightAmbient
  connector : ClearPath curve.polynomial connectorAmbient
    leftState.box.anchor rightState.box.anchor
  rightBoundaryPath : ClearPath curve.polynomial rightState.box
    rightState.box.anchor rightState.box.anchor
  leftBoundaryPath : ClearPath curve.polynomial leftState.box
    leftState.box.anchor leftState.box.anchor
  forwardDepth : Nat
  rightBoundaryDepth : Nat
  backwardDepth : Nat
  leftBoundaryDepth : Nat
  rootDiameter : Coordinate
  rootDiameterPositive : 0 < rootDiameter
  forwardOwner : Owner (curve.polynomial.eval leftState.box.anchor)
  forwardChecked : DyadicBank forwardDepth rootDiameter rootDiameterPositive
    connector forwardOwner
  rightBoundaryOwner : Owner
    (curve.polynomial.eval rightState.box.anchor)
  rightBoundaryChecked : DyadicBank rightBoundaryDepth rootDiameter
    rootDiameterPositive
    rightBoundaryPath rightBoundaryOwner
  backwardOwner : Owner (curve.polynomial.eval rightState.box.anchor)
  backwardChecked : DyadicBank backwardDepth rootDiameter rootDiameterPositive
    (CCL.Riemann.BranchCutLifts.ClearPath.reverse connector) backwardOwner
  leftBoundaryOwner : Owner
    (curve.polynomial.eval leftState.box.anchor)
  leftBoundaryChecked : DyadicBank leftBoundaryDepth rootDiameter
    rootDiameterPositive
    leftBoundaryPath leftBoundaryOwner

namespace PreparedBoundaryDoublePath

/-- Total preparation of a finite cut.  Each connector orientation and
winding-one boundary retains its own computed sufficient depth, avoiding an
artificial global maximum across unrelated path pieces. -/
def total {genus : Nat} {curve : HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Box}
    (leftState : RFAP.ShrinkingTrack.WindingOneState curve.polynomial
      leftAmbient)
    (rightState : RFAP.ShrinkingTrack.WindingOneState curve.polynomial
      rightAmbient)
    (connector : ClearPath curve.polynomial connectorAmbient
      leftState.box.anchor rightState.box.anchor)
    (connectorWithin : connector.WithinAmbient)
    (forwardOwner : Owner
      (curve.polynomial.eval leftState.box.anchor))
    (rightBoundaryOwner : Owner
      (curve.polynomial.eval rightState.box.anchor))
    (backwardOwner : Owner
      (curve.polynomial.eval rightState.box.anchor))
    (leftBoundaryOwner : Owner
      (curve.polynomial.eval leftState.box.anchor))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    PreparedBoundaryDoublePath curve := by
  let rightBoundary := ownerBoundaryPath rightState
  let backward := CCL.Riemann.BranchCutLifts.ClearPath.reverse connector
  let leftBoundary := ownerBoundaryPath leftState
  let forwardDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth connector rootDiameter
  let rightDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth rightBoundary
      rootDiameter
  let backwardDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth backward rootDiameter
  let leftDepth :=
    CCL.Riemann.PreparedClearPathModels.sufficientDepth leftBoundary
      rootDiameter
  exact
    { leftAmbient := leftAmbient
      rightAmbient := rightAmbient
      connectorAmbient := connectorAmbient
      leftState := leftState
      rightState := rightState
      connector := connector
      rightBoundaryPath := rightBoundary
      leftBoundaryPath := leftBoundary
      forwardDepth := forwardDepth
      rightBoundaryDepth := rightDepth
      backwardDepth := backwardDepth
      leftBoundaryDepth := leftDepth
      rootDiameter := rootDiameter
      rootDiameterPositive := rootDiameterPositive
      forwardOwner := forwardOwner
      forwardChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            connector connectorWithin forwardOwner forwardDepth rootDiameter
              rootDiameterPositive (by exact le_rfl))
      rightBoundaryOwner := rightBoundaryOwner
      rightBoundaryChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            rightBoundary (ownerBoundaryPath_withinAmbient rightState)
              rightBoundaryOwner rightDepth rootDiameter rootDiameterPositive
                (by exact le_rfl))
      backwardOwner := backwardOwner
      backwardChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            backward
              (CCL.Riemann.BranchCutLifts.ClearPath.reverse_withinAmbient
                connector connectorWithin)
              backwardOwner backwardDepth rootDiameter rootDiameterPositive
                (by exact le_rfl))
      leftBoundaryOwner := leftBoundaryOwner
      leftBoundaryChecked :=
        .safe
          (CCL.Riemann.PreparedClearPathModels.PreparedPath.CheckedDyadic.totalAt
            leftBoundary (ownerBoundaryPath_withinAmbient leftState)
              leftBoundaryOwner leftDepth rootDiameter rootDiameterPositive
                (by exact le_rfl)) }

/-- Total preparation of a finite branch cut from four caller-supplied local
square-root owners.  The owners select the two banks at both endpoint boxes;
all continuation depths and mesh checks remain internally computed. -/
def ofFiniteConnectorAtWithOwners {genus : Nat}
    {curve : HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne left refinement)))
    (rightBoundaryOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne right refinement)))
    (backwardOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne right refinement)))
    (leftBoundaryOwner : Owner (curve.polynomial.eval
      (refinedTrackAnchor branches degreeGtOne left refinement))) :
    PreparedBoundaryDoublePath curve :=
  total
    (refinedState branches degreeGtOne left refinement)
    (refinedState branches degreeGtOne right refinement)
    (finiteConnectorAt branches degreeGtOne left right refinement)
    (finiteConnectorAt_withinAmbient branches degreeGtOne left right refinement)
    forwardOwner rightBoundaryOwner backwardOwner leftBoundaryOwner
    1 (by decide)

/-- Total preparation of a finite branch cut at one root-box refinement.
The endpoint winding states, connector, four sheet owners, and common dyadic
depth are all selected constructively from the persistent branch data. -/
def ofFiniteConnectorAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches)
    (refinement : Nat) : PreparedBoundaryDoublePath curve := by
  let leftNonzero :=
    finiteConnectorAt_start_eval_ne_zero branches degreeGtOne left right
      refinement
  let rightNonzero :=
    finiteConnectorAt_finish_eval_ne_zero branches degreeGtOne left right
      refinement
  exact total
    (refinedState branches degreeGtOne left refinement)
    (refinedState branches degreeGtOne right refinement)
    (finiteConnectorAt branches degreeGtOne left right refinement)
    (finiteConnectorAt_withinAmbient branches degreeGtOne left right refinement)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent leftNonzero 0)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent rightNonzero 0)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent rightNonzero 1)
    (CCL.Riemann.SquareRootContinuationChain.Owner.independent leftNonzero 1)
    1 (by decide)

/-- Connector containment derived from its finite mesh certificate. -/
theorem connectorWithin {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    data.connector.WithinAmbient :=
  data.forwardChecked.within

def forward {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.connector data.forwardOwner :=
  data.forwardChecked.prepared

def rightBoundary {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.rightBoundaryPath
      data.rightBoundaryOwner :=
  data.rightBoundaryChecked.prepared

def backward {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath
      (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.connector)
        data.backwardOwner :=
  data.backwardChecked.prepared

def leftBoundary {genus : Nat} {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    PreparedPath data.leftBoundaryPath data.leftBoundaryOwner :=
  data.leftBoundaryChecked.prepared

/-- The closed lifted geometry selected by the prepared connector banks and
the two explicit winding-one boundary loops. -/
def closedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) : ClosedLiftedPath 2 :=
  { basepoint := { coordinate := data.leftState.box.anchor, sheet := 0 }
    path :=
      (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 0
        data.forward.toClearPath).append
        ((CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 0
          data.rightBoundary.toClearPath).append
          ((stationarySwitchPath data.rightState.box.anchor 0).append
            ((CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 1
              data.backward.toClearPath).append
              ((CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 1
                data.leftBoundary.toClearPath).append
                  (stationarySwitchPath data.leftState.box.anchor 1))))) }

/-- The certified finite cut lift.  Each local swap follows its corresponding
winding-one boundary loop, and every nonstationary cell comes from a prepared
uniform model. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) :
    CertifiedClosedModel curve differential := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let rightBoundary :=
    CertifiedLift.ofPreparedPath curve differential 0 data.rightBoundary
  let rightSwitch := CertifiedLift.switch curve differential
    data.rightState.box.anchor 0
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let leftBoundary :=
    CertifiedLift.ofPreparedPath curve differential 1 data.leftBoundary
  let leftSwitch := CertifiedLift.switch curve differential
    data.leftState.box.anchor 1
  let combined := forward.append
    (rightBoundary.append (rightSwitch.append
      (backward.append (leftBoundary.append leftSwitch))))
  exact
    { lifted := data.closedLift
      cells := combined.cells
      certificates := combined.certificates }

/-- Centre-free lower endpoint of the complete finite-cut sample.  The two
stationary sheet transitions contribute exactly zero, so only the four
prepared nonstationary path pieces occur in the finite sum. -/
def integralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) : Coordinate :=
  data.forward.integralRealLower curve differential 0 +
    (data.rightBoundary.integralRealLower curve differential 0 +
      (data.backward.integralRealLower curve differential 1 +
        data.leftBoundary.integralRealLower curve differential 1))

/-- Centre-free directional endpoint of all four nonstationary finite-cut
pieces. -/
def directionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus)
    (direction : Gaussian) : Coordinate :=
  data.forward.directionalIntegralLower curve differential 0 direction +
    (data.rightBoundary.directionalIntegralLower curve differential 0 direction +
      (data.backward.directionalIntegralLower curve differential 1 direction +
        data.leftBoundary.directionalIntegralLower curve differential 1
          direction))

/-- The certified finite-cut sample is the sum of its four nonstationary
prepared path samples.  This named projection prevents downstream lower-bound
proofs from normalizing the complete dependent `CertifiedClosedModel`. -/
theorem certifiedModel_integralSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (data.certifiedModel differential).cells).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (CertifiedLift.ofPreparedPath curve differential 0
            data.forward).cells).integralSample +
          ((CCL.ProgressiveGaussianIntegration.PathModel.mk
            (CertifiedLift.ofPreparedPath curve differential 0
              data.rightBoundary).cells).integralSample +
            ((CCL.ProgressiveGaussianIntegration.PathModel.mk
              (CertifiedLift.ofPreparedPath curve differential 1
                data.backward).cells).integralSample +
              (CCL.ProgressiveGaussianIntegration.PathModel.mk
                (CertifiedLift.ofPreparedPath curve differential 1
                  data.leftBoundary).cells).integralSample)) := by
  unfold certifiedModel
  simp only [CertifiedLift.append_integralSample,
    CertifiedLift.switch_integralSample,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]

/-- The finite-cut endpoint bounds the real coordinate of the exact certified
model assembled from the same four prepared banks. -/
theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  let forward := CertifiedLift.ofPreparedPath curve differential 0 data.forward
  let rightBoundary :=
    CertifiedLift.ofPreparedPath curve differential 0 data.rightBoundary
  let backward := CertifiedLift.ofPreparedPath curve differential 1 data.backward
  let leftBoundary :=
    CertifiedLift.ofPreparedPath curve differential 1 data.leftBoundary
  have forwardLower :
      data.forward.integralRealLower curve differential 0 <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          forward.cells).integralSample.re :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.forward
  have rightLower :
      data.rightBoundary.integralRealLower curve differential 0 <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          rightBoundary.cells).integralSample.re :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 0 exponentZero data.rightBoundary
  have backwardLower :
      data.backward.integralRealLower curve differential 1 <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          backward.cells).integralSample.re :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.backward
  have leftLower :
      data.leftBoundary.integralRealLower curve differential 1 <=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          leftBoundary.cells).integralSample.re :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.integralRealLower_le_certify
      curve differential 1 exponentZero data.leftBoundary
  have componentLower := add_le_add forwardLower
    (add_le_add rightLower (add_le_add backwardLower leftLower))
  rw [data.certifiedModel_integralSample differential]
  simp only [RFAP.ConstructiveGaussian.Gaussian.add_re]
  exact componentLower

theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  have forwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.forward
  have rightLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 0 direction exponentZero data.rightBoundary
  have backwardLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.backward
  have leftLower :=
    CCL.Riemann.PreparedClearPathModels.PreparedPath.directionalIntegralLower_le_certify
      curve differential 1 direction exponentZero data.leftBoundary
  have componentLower := add_le_add forwardLower
    (add_le_add rightLower (add_le_add backwardLower leftLower))
  rw [data.certifiedModel_integralSample differential]
  unfold CertifiedLift.ofPreparedPath
  simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im]
  exact componentLower.trans_eq (by ring1)

/-- Every connector, boundary, and stationary-switch cell of a prepared
finite cut is Gaussian constant. -/
def certifiedModel_constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (data.certifiedModel differential).cells := by
  exact
    (CertifiedLift.ofPreparedPath_constantCells curve differential 0
      data.forward).append
      ((CertifiedLift.ofPreparedPath_constantCells curve differential 0
        data.rightBoundary).append
        ((CertifiedLift.switch_constantCells curve differential
          data.rightState.box.anchor 0).append
          ((CertifiedLift.ofPreparedPath_constantCells curve differential 1
            data.backward).append
            ((CertifiedLift.ofPreparedPath_constantCells curve differential 1
              data.leftBoundary).append
              (CertifiedLift.switch_constantCells curve differential
                data.leftState.box.anchor 1)))))

/-- Zero-wedge charts for every prepared connector or winding-boundary cell,
plus exact-zero charts for the two stationary sheet transitions. -/
def wedgeCharts {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (leftDifferential rightDifferential : Differential genus) :
    List (WedgeChart curve leftDifferential rightDifferential) :=
  CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
      leftDifferential rightDifferential 0 data.forward ++
    CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
        leftDifferential rightDifferential 0 data.rightBoundary ++
      [stationaryWedgeChart curve leftDifferential rightDifferential] ++
        CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
            leftDifferential rightDifferential 1 data.backward ++
          CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts curve
              leftDifferential rightDifferential 1 data.leftBoundary ++
            [stationaryWedgeChart curve leftDifferential rightDifferential]

@[simp] theorem certifiedModel_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      data.forward.stepCount +
        (data.rightBoundary.stepCount + 1 +
          (data.backward.stepCount +
            (data.leftBoundary.stepCount + 1))) := by
  rw [← CertifiedClosedModel.cellCount]
  simp only [certifiedModel, CertifiedLift.append, CertifiedLift.switch,
    CertifiedLift.ofPreparedPath, List.length_append, List.length_cons,
    List.length_nil,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.certify_cellCount,
    Nat.zero_add, Nat.add_assoc]

/-- Exact cell count with the independently minimal dyadic depth retained by
each path piece.  The two additional cells are the stationary sheet
transitions. -/
theorem certifiedModel_cellCount_eq_dyadic {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (differential : Differential genus) :
    (data.certifiedModel differential).lifted.cellCount =
      2 ^ data.forwardDepth * data.connector.segmentCount +
        2 ^ data.rightBoundaryDepth *
            data.rightBoundaryPath.segmentCount +
          2 ^ data.backwardDepth * data.connector.segmentCount +
            2 ^ data.leftBoundaryDepth *
                data.leftBoundaryPath.segmentCount + 2 := by
  rw [certifiedModel_cellCount]
  simp only [forward, rightBoundary, backward, leftBoundary]
  rw [
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.rightBoundaryChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.leftBoundaryChecked,
    CCL.Riemann.BranchCutLifts.ClearPath.segmentCount_reverse]
  omega0

/-- The owner-boundary cycle's local holomorphicity data covers exactly every
cell in either differential integration model. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve)
    (leftDifferential rightDifferential : Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  rw [CertifiedClosedModel.cellCount,
    data.certifiedModel_cellCount leftDifferential]
  simp only [wedgeCharts, List.length_append, List.length_cons,
    List.length_nil,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.wedgeCharts_length]
  omega0

end PreparedBoundaryDoublePath

/-- The two prepared finite cycle geometries needed by the standard basis:
an auxiliary bridge with stationary endpoint switches, or a finite branch cut
whose switches follow explicit winding-one owner boundaries. -/
inductive PreparedCycleData {genus : Nat}
    (curve : HyperellipticCurve genus) : Type
  | bridge (data : PreparedDoublePath curve)
  | finiteCut (data : PreparedBoundaryDoublePath curve)

namespace PreparedCycleData

/-- Forget the preparation certificates while retaining the exact closed
lifted geometry. -/
def closedLift {genus : Nat}
    {curve : HyperellipticCurve genus} :
    PreparedCycleData curve -> ClosedLiftedPath 2
  | .bridge data => data.closedLift
  | .finiteCut data => data.closedLift

/-- Uniformly certify every nonstationary prepared cell and every stationary
switch cell for one differential. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) :
    (data : PreparedCycleData curve) -> CertifiedClosedModel curve differential
  | .bridge data => data.certifiedModel differential
  | .finiteCut data => data.certifiedModel differential

/-- Centre-free real endpoint exposed uniformly across the two supported
prepared-cycle presentations. -/
def integralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) :
    PreparedCycleData curve -> Coordinate
  | .bridge data => data.integralRealLower differential
  | .finiteCut data => data.integralRealLower differential

/-- Directional endpoint exposed uniformly across the two prepared-cycle
presentations. -/
def directionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus) (direction : Gaussian) :
    PreparedCycleData curve -> Coordinate
  | .bridge data => data.directionalIntegralLower differential direction
  | .finiteCut data => data.directionalIntegralLower differential direction

/-- The cycle-level endpoint bounds the certified initial path model without
constructing or inspecting any coefficient centre. -/
theorem integralRealLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differential genus)
    (exponentZero : differential.exponent = 0) :
    data.integralRealLower differential <=
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (data.certifiedModel differential).cells).integralSample.re := by
  cases data with
  | bridge bridge =>
      exact bridge.integralRealLower_le_certifiedModel differential exponentZero
  | finiteCut finiteCut =>
      exact finiteCut.integralRealLower_le_certifiedModel differential
        exponentZero

/-- The uniform directional endpoint bounds the same projection of the
certified initial cycle model. -/
theorem directionalIntegralLower_le_certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    data.directionalIntegralLower differential direction <=
      direction.re *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.re +
        direction.im *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample.im := by
  cases data with
  | bridge bridge =>
      exact bridge.directionalIntegralLower_le_certifiedModel differential
        direction exponentZero
  | finiteCut finiteCut =>
      exact finiteCut.directionalIntegralLower_le_certifiedModel differential
        direction exponentZero

/-- A positive directional endpoint gives a square-root-free norm lower for
the certified cycle sample.  The direction need not be normalized: its exact
rational norm appears explicitly on the right. -/
theorem directionalIntegralLower_sq_le_normSq_mul {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differential genus)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0)
    (positive : 0 < data.directionalIntegralLower differential direction) :
    data.directionalIntegralLower differential direction ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq direction *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (data.certifiedModel differential).cells).integralSample := by
  let sample :=
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (data.certifiedModel differential).cells).integralSample
  let dot := direction.re * sample.re + direction.im * sample.im
  have lowerLe :
      data.directionalIntegralLower differential direction <= dot :=
    data.directionalIntegralLower_le_certifiedModel differential direction
      exponentZero
  have lowerSqLe :
      data.directionalIntegralLower differential direction ^ 2 <= dot ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le lowerLe 2
  have dotSqLe : dot ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq direction *
        RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
    exact RFAP.ConstructiveGaussian.Gaussian.projection_sq_le_normSq_mul
      direction sample
  exact lowerSqLe.trans dotSqLe

/-- Complete cellwise zero-wedge data on either supported prepared cycle
geometry. -/
def wedgeCharts {genus : Nat}
    {curve : HyperellipticCurve genus}
    (leftDifferential rightDifferential : Differential genus) :
    (data : PreparedCycleData curve) ->
      List (WedgeChart curve leftDifferential rightDifferential)
  | .bridge data => data.wedgeCharts leftDifferential rightDifferential
  | .finiteCut data => data.wedgeCharts leftDifferential rightDifferential

/-- A prepared cycle's zero-wedge chart list is aligned with its certified
integration cells. -/
@[simp] theorem wedgeCharts_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differential genus) :
    (data.wedgeCharts leftDifferential rightDifferential).length =
      (data.certifiedModel leftDifferential).cells.length := by
  cases data with
  | bridge bridge => exact bridge.wedgeCharts_length _ _
  | finiteCut finiteCut => exact finiteCut.wedgeCharts_length _ _

/-- Both differential integration models on one prepared closed cycle,
together with the finite chart list proving their local wedge vanishes on
every model cell. -/
structure HolomorphicCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differential genus) where
  leftModel : CertifiedClosedModel curve leftDifferential
  rightModel : CertifiedClosedModel curve rightDifferential
  charts : List (WedgeChart curve leftDifferential rightDifferential)
  charts_match_left : charts.length = leftModel.cells.length
  charts_match_right : charts.length = rightModel.cells.length

/-- Construct the complete closed-cycle local holomorphicity certificate from
prepared geometry alone. -/
def holomorphicCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (leftDifferential rightDifferential : Differential genus) :
    HolomorphicCertificate data leftDifferential rightDifferential where
  leftModel := data.certifiedModel leftDifferential
  rightModel := data.certifiedModel rightDifferential
  charts := data.wedgeCharts leftDifferential rightDifferential
  charts_match_left := data.wedgeCharts_length _ _
  charts_match_right := by
    calc
      (data.wedgeCharts leftDifferential rightDifferential).length =
          (data.certifiedModel leftDifferential).cells.length :=
        data.wedgeCharts_length _ _
      _ = data.closedLift.cellCount := by
        rw [CertifiedClosedModel.cellCount]
        cases data <;> rfl
      _ = (data.certifiedModel rightDifferential).cells.length := by
        rw [CertifiedClosedModel.cellCount]
        cases data <;> rfl

/-- The finite Gaussian path model carried by one prepared closed cycle. -/
def pathModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (data : PreparedCycleData curve) : PathModel :=
  ⟨(data.certifiedModel differential).cells⟩

/-- Prepared cycle models carry the constant-cell invariant needed to derive
canonical self-refinements. -/
def pathModel_constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (data : PreparedCycleData curve) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (data.pathModel differential).cells := by
  cases data with
  | bridge bridge => exact bridge.certifiedModel_constantCells differential
  | finiteCut finiteCut =>
      exact finiteCut.certifiedModel_constantCells differential

@[simp] theorem pathModel_cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    (differential : Differential genus)
    (data : PreparedCycleData curve) :
    (data.pathModel differential).cells =
      (data.certifiedModel differential).cells := rfl

@[simp] theorem certifiedModel_lifted {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedCycleData curve)
    (differential : Differential genus) :
    (data.certifiedModel differential).lifted = data.closedLift := by
  cases data <;> rfl

/-- A prepared cycle realizes one raw branch-cut construction when it was
built from exactly the same displayed bridge, or from exactly the same two
owner states and connector.  This is deliberately weaker than equality of
lifted paths: dyadic preparation inserts cells, and the prepared finite-cut
model moves each recorded sheet transition from the last boundary edge to a
stationary cell at its endpoint. -/
inductive RealizesRaw {genus : Nat}
    {curve : HyperellipticCurve genus} :
    (data : PreparedCycleData curve) -> ClosedLiftedPath 2 -> Prop
  | bridge (data : PreparedDoublePath curve) :
      RealizesRaw (.bridge data)
        (CCL.Riemann.BranchCutLifts.doubleLift data.basePath)
  | finiteCut (data : PreparedBoundaryDoublePath curve)
      (_rightBoundary : data.rightBoundaryPath = ownerBoundaryPath data.rightState)
      (_leftBoundary : data.leftBoundaryPath = ownerBoundaryPath data.leftState) :
      RealizesRaw (.finiteCut data)
        (CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState data.connector)
  | bridgeDyadic (data : PreparedDoublePath curve)
      (rawPath : ClearPath curve.polynomial data.ambient data.start data.finish)
      (rawWithin : rawPath.WithinAmbient) (outerDepth : Nat)
      (_refined : data.basePath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePath rawPath rawWithin
          outerDepth) :
      RealizesRaw (.bridge data)
        (CCL.Riemann.BranchCutLifts.doubleLift rawPath)
  | bridgeDyadicScheduled (data : PreparedDoublePath curve)
      (rawPath : ClearPath curve.polynomial data.ambient data.start data.finish)
      (rawWithin : rawPath.WithinAmbient) (outerDepths : List Nat)
      (_refined : data.basePath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled rawPath
          rawWithin outerDepths) :
      RealizesRaw (.bridge data)
        (CCL.Riemann.BranchCutLifts.doubleLift rawPath)
  | finiteCutDyadic (data : PreparedBoundaryDoublePath curve)
      (rawConnector : ClearPath curve.polynomial data.connectorAmbient
        data.leftState.box.anchor data.rightState.box.anchor)
      (rawWithin : rawConnector.WithinAmbient) (outerDepth : Nat)
      (_refined : data.connector =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePath rawConnector
          rawWithin outerDepth)
      (rightRawWithin : (ownerBoundaryPath data.rightState).WithinAmbient)
      (rightOuterDepth : Nat)
      (_rightRefined : data.rightBoundaryPath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
          (ownerBoundaryPath data.rightState) rightRawWithin rightOuterDepth)
      (leftRawWithin : (ownerBoundaryPath data.leftState).WithinAmbient)
      (leftOuterDepth : Nat)
      (_leftRefined : data.leftBoundaryPath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePath
          (ownerBoundaryPath data.leftState) leftRawWithin leftOuterDepth) :
      RealizesRaw (.finiteCut data)
        (CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState rawConnector)
  | finiteCutDyadicScheduled (data : PreparedBoundaryDoublePath curve)
      (rawConnector : ClearPath curve.polynomial data.connectorAmbient
        data.leftState.box.anchor data.rightState.box.anchor)
      (rawWithin : rawConnector.WithinAmbient) (connectorDepths : List Nat)
      (_refined : data.connector =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
          rawConnector rawWithin connectorDepths)
      (rightRawWithin : (ownerBoundaryPath data.rightState).WithinAmbient)
      (rightDepths : List Nat)
      (_rightRefined : data.rightBoundaryPath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
          (ownerBoundaryPath data.rightState) rightRawWithin rightDepths)
      (leftRawWithin : (ownerBoundaryPath data.leftState).WithinAmbient)
      (leftDepths : List Nat)
      (_leftRefined : data.leftBoundaryPath =
        CCL.Riemann.PreparedClearPathModels.dyadicRefinePathScheduled
          (ownerBoundaryPath data.leftState) leftRawWithin leftDepths) :
      RealizesRaw (.finiteCut data)
        (CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
          data.leftState data.rightState rawConnector)

namespace RealizesRaw

/-- The raw cell count attached to a prepared bridge realization. -/
theorem bridge_raw_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedDoublePath curve) :
    (CCL.Riemann.BranchCutLifts.doubleLift data.basePath).cellCount =
      2 * data.basePath.segmentCount + 2 :=
  CCL.Riemann.BranchCutLifts.doubleLift_cellCount data.basePath

/-- The raw cell count attached to a prepared owner-boundary realization. -/
theorem finiteCut_raw_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PreparedBoundaryDoublePath curve) :
    (CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners
        data.leftState data.rightState data.connector).cellCount =
      2 * data.connector.segmentCount + 8 :=
  CCL.Riemann.BranchCutLifts.doubleLiftWithBoundaryOwners_cellCount
    data.leftState data.rightState data.connector

end RealizesRaw

end PreparedCycleData

/-- A differential-independent persistent family of prepared finite cycle
geometries. -/
structure CycleSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  data : Nat -> PreparedCycleData curve

namespace CycleSchedule

/-- The persistent lifted cycle underlying one prepared geometric schedule. -/
def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : CycleSchedule curve) : LiftedCycleRefinement 2 where
  liftedPath := fun index => (schedule.data index).closedLift

/-- Every prepared refinement in a schedule comes from the corresponding raw
finite branch-cut construction.  The witness is finite and local at each
requested refinement; it does not identify two differently subdivided path
values. -/
structure Realizes {genus : Nat}
    {curve : HyperellipticCurve genus}
    (schedule : CycleSchedule curve)
    (raw : LiftedCycleRefinement 2) where
  refinement : forall index,
    PreparedCycleData.RealizesRaw (schedule.data index) (raw.liftedPath index)

end CycleSchedule

/-- A persistent family of certified closed finite models together with the
single Gaussian refinement program whose displayed cells are those models. -/
structure Schedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : Differential genus) where
  model : Nat -> CertifiedClosedModel curve differential
  integral : RefinementProgram
  cells_eq : forall index, (integral.model index).cells = (model index).cells

namespace Schedule

/-- The persistent lifted cycle selected by the certified finite schedule. -/
def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : Schedule curve differential) : LiftedCycleRefinement 2 where
  liftedPath := fun index => (schedule.model index).lifted

/-- Forget the prepared origin only after constructing a period program whose
cells are definitionally tied, index by index, to the same lifted cycle. -/
def toCertifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : Schedule curve differential) :
    CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral
  certificates := by
    intro index
    rw [schedule.cells_eq index]
    exact (schedule.model index).certificates

@[simp] theorem finite_refinement_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (schedule : Schedule curve differential) (index : Nat) :
    (schedule.integral.model index).cells.length =
      (schedule.cycle.liftedPath index).cellCount :=
  schedule.toCertifiedPeriodProgram.finite_refinement_cellCount index

end Schedule

/-- One differential's Gaussian refinement program on a fixed prepared cycle
schedule.  The geometry is independent of the differential; only the finite
cell models and their coefficients vary. -/
structure DifferentialSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differential genus) where
  integral : RefinementProgram
  cells_eq : forall index, (integral.model index).cells =
    ((geometry.data index).certifiedModel differential).cells

namespace DifferentialSchedule

/-- The resulting certified period program follows exactly the common
differential-independent cycle schedule. -/
def toCertifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (schedule : DifferentialSchedule curve geometry differential) :
    CertifiedPeriodProgram curve differential geometry.cycle where
  integral := schedule.integral
  certificates := by
    intro index
    rw [schedule.cells_eq index]
    let certificates :=
      ((geometry.data index).certifiedModel differential).certificates
    have liftedEqual := PreparedCycleData.certifiedModel_lifted
      (geometry.data index) differential
    rw [liftedEqual] at certificates
    exact certificates

@[simp] theorem finite_refinement_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (schedule : DifferentialSchedule curve geometry differential)
    (index : Nat) :
    (schedule.integral.model index).cells.length =
      (geometry.cycle.liftedPath index).cellCount :=
  schedule.toCertifiedPeriodProgram.finite_refinement_cellCount index

end DifferentialSchedule

/-- Consecutive whole-cycle refinement data.  Every displayed mesh need only
refine its immediate predecessor; the generic Gaussian integration kernel
derives all later Cauchy comparisons by finite geometric telescoping. -/
structure SequentialCompatibleDifferentialCore {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differential genus) where
  steps : forall index,
    CompatibleConstantPathRefinement
      ((geometry.data index).pathModel differential).cells
      ((geometry.data (index + 1)).pathModel differential).cells
  stepScale : Coordinate
  stepScale_nonnegative : 0 <= stepScale
  initialAllowance_le :
    ((geometry.data 0).pathModel differential).aggregateAllowance <=
      4 * stepScale
  comparisonAllowance_le : forall index,
    (steps index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius stepScale index

namespace SequentialCompatibleDifferentialCore

/-- Turn immediate prepared parent--child partitions into a certified period
schedule.  Model allowances, all-later closeness, and uniform sample bounds
are consequences rather than additional inputs. -/
def toDifferentialSchedule {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : SequentialCompatibleDifferentialCore curve geometry differential) :
    DifferentialSchedule curve geometry differential where
  integral :=
    ({ model := fun index => (geometry.data index).pathModel differential
       steps := core.steps
       stepScale := core.stepScale
       stepScale_nonneg := core.stepScale_nonnegative
       initialAllowance_le := core.initialAllowance_le
       comparisonAllowance_le := core.comparisonAllowance_le } :
      CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram).toRefinementProgram
  cells_eq := fun _ => rfl

@[simp] theorem integral_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : SequentialCompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    (core.toDifferentialSchedule.integral.model index).cells =
      ((geometry.data index).certifiedModel differential).cells := rfl

end SequentialCompatibleDifferentialCore

/-- Strict whole-cycle refinement data.  Only genuinely later meshes need a
parent--child certificate.  Equal-index comparisons are constructed from the
constant-cell invariant, and the factor-four self-comparison is absorbed into
the resulting error scale. -/
structure StrictCompatibleDifferentialCore {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differential genus) where
  laterRefinements : forall {earlier later : Nat}, earlier < later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  modelScale : Coordinate
  modelScale_nonnegative : 0 <= modelScale
  modelAllowance_le : forall index,
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius modelScale index
  comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier < later),
    (laterRefinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius (4 * modelScale) earlier

/-- Minimal whole-cycle refinement data.  Uniform boundedness is not an
independent input: it follows from comparison with the initial finite model. -/
structure CompatibleDifferentialCore {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differential genus) where
  refinements : forall {earlier later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  errorScale : Coordinate
  errorScale_nonnegative : 0 <= errorScale
  comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (refinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier

namespace StrictCompatibleDifferentialCore

/-- The common modulus after paying the exact factor-four cost of a canonical
self-comparison. -/
def errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    Coordinate :=
  4 * core.modelScale

theorem errorScale_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    0 <= core.errorScale :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    core.modelScale_nonnegative

private theorem quarterRadius_model_le_errorScale
    {scale : Coordinate} (nonnegative : 0 <= scale) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius scale index <=
      CCL.FiniteGeometric.quarterRadius (4 * scale) index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  have powerNonnegative :
      0 <= (1 / 4 : Coordinate) ^ index :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (by
      calc
        scale = 1 * scale := by ring1
        _ <= 4 * scale :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) nonnegative)
    powerNonnegative

/-- Choose a strict supplied comparison when the index increases and the
canonical constant-cell self-comparison when the indices coincide. -/
def refinements {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    {earlier later : Nat} (order : earlier <= later) :
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells := by
  by_cases equal : earlier = later
  · subst later
    exact CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement.refl
      ((geometry.data earlier).pathModel_constantCells differential)
  · exact core.laterRefinements (Nat.lt_of_le_of_ne order equal)

theorem modelAllowance_le_errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius core.errorScale index :=
  (core.modelAllowance_le index).trans
    (quarterRadius_model_le_errorScale core.modelScale_nonnegative index)

theorem refinements_comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential)
    {earlier later : Nat} (order : earlier <= later) :
    (core.refinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius core.errorScale earlier := by
  by_cases equal : earlier = later
  · subst later
    simp only [refinements, dif_pos True.intro]
    rw [CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement.comparisonAllowance_refl_eq]
    calc
      4 * ((geometry.data earlier).pathModel differential).aggregateAllowance <=
          4 * CCL.FiniteGeometric.quarterRadius core.modelScale earlier :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (core.modelAllowance_le earlier) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius core.errorScale earlier := by
        unfold errorScale
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  · simp only [refinements, dif_neg equal]
    exact core.comparisonAllowance_le (Nat.lt_of_le_of_ne order equal)

/-- Expand strict data into the existing core interface. -/
def toCompatibleDifferentialCore {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : StrictCompatibleDifferentialCore curve geometry differential) :
    CompatibleDifferentialCore curve geometry differential where
  refinements := core.refinements
  errorScale := core.errorScale
  errorScale_nonnegative := core.errorScale_nonnegative
  comparisonAllowance_le := core.refinements_comparisonAllowance_le

end StrictCompatibleDifferentialCore

/-- A whole-cycle prepared schedule whose Cauchy estimate is derived from
explicit compatible parent/child cell partitions.  This is the cycle-level
counterpart of `PreparedRefinementPrograms.Schedule`; no arbitrary
`RefinementProgram.later_close` proof is accepted. -/
structure CompatibleDifferentialSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : CycleSchedule curve)
    (differential : Differential genus) where
  refinements : forall {earlier later : Nat}, earlier <= later ->
    CompatibleConstantPathRefinement
      ((geometry.data earlier).pathModel differential).cells
      ((geometry.data later).pathModel differential).cells
  errorScale : Coordinate
  errorScale_nonnegative : 0 <= errorScale
  modelAllowance_le : forall index,
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale index
  comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (refinements order).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonnegative : 0 <= centerBound
  sample_bounded : forall index,
    RFAP.ConstructiveGaussian.Gaussian.normSq
      ((geometry.data index).pathModel differential).integralSample <=
        centerBound

namespace CompatibleDifferentialSchedule

/-- Derive the ordinary whole-cycle schedule from explicit compatible finite
partitions and rational bounds. -/
def toDifferentialSchedule {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (schedule : CompatibleDifferentialSchedule curve geometry differential) :
    DifferentialSchedule curve geometry differential where
  integral :=
    ({ model := fun index => (geometry.data index).pathModel differential
       refinements := schedule.refinements
       errorScale := schedule.errorScale
       errorScale_nonneg := schedule.errorScale_nonnegative
       modelAllowance_le := schedule.modelAllowance_le
       comparisonAllowance_le := schedule.comparisonAllowance_le
       centerBound := schedule.centerBound
       centerBound_nonneg := schedule.centerBound_nonnegative
       sample_bounded := schedule.sample_bounded } :
      CCL.ProgressiveGaussianIntegration.CompatibleConstantRefinementProgram).toRefinementProgram
  cells_eq := fun _ => rfl

@[simp] theorem integral_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (schedule : CompatibleDifferentialSchedule curve geometry differential)
    (index : Nat) :
    ((schedule.toDifferentialSchedule).integral.model index).cells =
      ((geometry.data index).certifiedModel differential).cells := rfl

end CompatibleDifferentialSchedule

namespace CompatibleDifferentialCore

/-- The child model's semantic allowance is already included in the
comparison allowance.  Applying the supplied comparison modulus to the
reflexive refinement therefore derives the model-allowance bound. -/
theorem modelAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    ((geometry.data index).pathModel differential).aggregateAllowance <=
      CCL.FiniteGeometric.quarterRadius core.errorScale index := by
  calc
    ((geometry.data index).pathModel differential).aggregateAllowance <=
        (core.refinements (Nat.le_refl index)).comparisonAllowance :=
      (core.refinements
        (Nat.le_refl index)).childAggregateAllowance_le_comparisonAllowance
    _ <= CCL.FiniteGeometric.quarterRadius core.errorScale index :=
      core.comparisonAllowance_le (Nat.le_refl index)

/-- Canonical uniform squared bound obtained by comparing every sample with
the displayed initial sample. -/
def centerBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    Coordinate :=
  2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
      ((geometry.data 0).pathModel differential).integralSample +
    core.errorScale)

theorem centerBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    0 <= core.centerBound := by
  unfold centerBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
      core.errorScale_nonnegative)

private theorem normSq_le_initial_bound
    (current initial : RFAP.ConstructiveGaussian.Gaussian)
    (scale : Coordinate)
    (movement : RFAP.ConstructiveGaussian.Gaussian.normSq
      (current - initial) <= scale) :
    RFAP.ConstructiveGaussian.Gaussian.normSq current <=
      2 * (RFAP.ConstructiveGaussian.Gaussian.normSq initial + scale) := by
  have sumBound :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two
      (current - initial) initial
  have identity : current - initial + initial = current := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [identity] at sumBound
  apply sumBound.trans
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
    (show (0 : Coordinate) <= 2 by decide)
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (current - initial) +
        RFAP.ConstructiveGaussian.Gaussian.normSq initial <=
      scale + RFAP.ConstructiveGaussian.Gaussian.normSq initial :=
        add_le_add movement (le_refl _)
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq initial + scale := by ring1

private theorem sample_sub_initial_bounded {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((geometry.data index).pathModel differential).integralSample -
          ((geometry.data 0).pathModel differential).integralSample) <=
      core.errorScale := by
  calc
    _ <= (core.refinements (Nat.zero_le index)).comparisonAllowance :=
      (core.refinements (Nat.zero_le index)).integral_difference_le
    _ <= CCL.FiniteGeometric.quarterRadius core.errorScale 0 :=
      core.comparisonAllowance_le (Nat.zero_le index)
    _ <= core.errorScale :=
      CCL.FiniteGeometric.quarterRadius_le_scale
        core.errorScale_nonnegative 0

/-- Parent/child compatibility bounds every later finite integral sample by
the canonical initial-sample bound. -/
theorem sample_bounded {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential)
    (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((geometry.data index).pathModel differential).integralSample <=
      core.centerBound := by
  let initial := ((geometry.data 0).pathModel differential).integralSample
  let current := ((geometry.data index).pathModel differential).integralSample
  exact normSq_le_initial_bound current initial core.errorScale
    (sample_sub_initial_bounded core index)

/-- Expand the minimal core into the existing compatible schedule; both
boundedness fields are derived. -/
def toCompatibleDifferentialSchedule {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : CycleSchedule curve}
    {differential : Differential genus}
    (core : CompatibleDifferentialCore curve geometry differential) :
    CompatibleDifferentialSchedule curve geometry differential where
  refinements := core.refinements
  errorScale := core.errorScale
  errorScale_nonnegative := core.errorScale_nonnegative
  modelAllowance_le := core.modelAllowance_le
  comparisonAllowance_le := core.comparisonAllowance_le
  centerBound := core.centerBound
  centerBound_nonnegative := core.centerBound_nonnegative
  sample_bounded := core.sample_bounded

end CompatibleDifferentialCore

/-- Prepared geometric schedules for every member of one symplectic basis. -/
structure SymplecticCycleSchedule {genus : Nat}
    (curve : HyperellipticCurve genus) where
  aCycle : Fin genus -> CycleSchedule curve
  bCycle : Fin genus -> CycleSchedule curve

namespace SymplecticCycleSchedule

/-- Forget preparation while retaining the common persistent lifted A/B
cycle family. -/
def cycles {genus : Nat}
    {curve : HyperellipticCurve genus}
    (geometry : SymplecticCycleSchedule curve) :
    LiftedSymplecticCycles 2 genus where
  aCycle := fun index => (geometry.aCycle index).cycle
  bCycle := fun index => (geometry.bCycle index).cycle

/-- A prepared A/B schedule realizes a raw symplectic cycle family refinement
by refinement, using the exact finite bridge or owner-boundary constructor in
each case. -/
structure Realizes {genus : Nat}
    {curve : HyperellipticCurve genus}
    (geometry : SymplecticCycleSchedule curve)
    (raw : LiftedSymplecticCycles 2 genus) where
  aCycle : forall index, CycleSchedule.Realizes
    (geometry.aCycle index) (raw.aCycle index)
  bCycle : forall index, CycleSchedule.Realizes
    (geometry.bCycle index) (raw.bCycle index)

end SymplecticCycleSchedule

/-- Finite evidence that one persistent symplectic cycle family represents
another.  Literal equality remains available for unrefined programs; prepared
programs instead carry their common geometry and its raw-construction
realization. -/
inductive SymplecticCycleRealization {genus : Nat}
    (curve : HyperellipticCurve genus) :
    LiftedSymplecticCycles 2 genus -> LiftedSymplecticCycles 2 genus -> Prop
  | exact {cycles : LiftedSymplecticCycles 2 genus} :
      SymplecticCycleRealization curve cycles cycles
  | prepared (geometry : SymplecticCycleSchedule curve)
      {raw : LiftedSymplecticCycles 2 genus}
      (realizes : geometry.Realizes raw) :
      SymplecticCycleRealization curve geometry.cycles raw

namespace SymplecticCycleRealization

/-- Convert an explicitly displayed equality to a cycle realization without
using any extensional or choice principle. -/
theorem ofEq {genus : Nat} {curve : HyperellipticCurve genus}
    {left right : LiftedSymplecticCycles 2 genus}
    (equal : left = right) : SymplecticCycleRealization curve left right := by
  cases equal
  exact .exact

end SymplecticCycleRealization

/-- All differential-specific finite programs over one common prepared
symplectic cycle schedule. -/
structure PeriodSchedules {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  aSchedule : forall differential cycle : Fin genus,
    DifferentialSchedule curve (geometry.aCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
  bSchedule : forall differential cycle : Fin genus,
    DifferentialSchedule curve (geometry.bCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)

/-- Consecutive A/B refinement cores.  This is the directly constructible
schedule interface for recursively refined prepared cycle geometries. -/
structure SequentialCompatiblePeriodCores {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  aCore : forall differential cycle : Fin genus,
    SequentialCompatibleDifferentialCore curve (geometry.aCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
  bCore : forall differential cycle : Fin genus,
    SequentialCompatibleDifferentialCore curve (geometry.bCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)

/-- All A/B programs supplied through explicit compatible prepared cell
partitions rather than arbitrary convergence fields. -/
structure CompatiblePeriodSchedules {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  aSchedule : forall differential cycle : Fin genus,
    CompatibleDifferentialSchedule curve (geometry.aCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
  bSchedule : forall differential cycle : Fin genus,
    CompatibleDifferentialSchedule curve (geometry.bCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)

/-- Strict A/B refinement cores.  Equal-index comparisons for every entry are
derived from its prepared constant-cell invariant. -/
structure StrictCompatiblePeriodCores {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  aCore : forall differential cycle : Fin genus,
    StrictCompatibleDifferentialCore curve (geometry.aCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
  bCore : forall differential cycle : Fin genus,
    StrictCompatibleDifferentialCore curve (geometry.bCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)

/-- Minimal A/B refinement cores.  Uniform sample bounds for every entry are
derived when these cores are expanded into compatible schedules. -/
structure CompatiblePeriodCores {genus : Nat}
    (curve : HyperellipticCurve genus)
    (geometry : SymplecticCycleSchedule curve) where
  aCore : forall differential cycle : Fin genus,
    CompatibleDifferentialCore curve (geometry.aCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)
  bCore : forall differential cycle : Fin genus,
    CompatibleDifferentialCore curve (geometry.bCycle cycle)
      (CCL.Riemann.PeriodMatrix.standardDifferential differential)

namespace SequentialCompatiblePeriodCores

/-- Assemble ordinary prepared period schedules entry by entry from
consecutive compatible refinements. -/
def toPeriodSchedules {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : SequentialCompatiblePeriodCores curve geometry) :
    PeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (cores.aCore differential cycle).toDifferentialSchedule
  bSchedule := fun differential cycle =>
    (cores.bCore differential cycle).toDifferentialSchedule

end SequentialCompatiblePeriodCores

namespace CompatiblePeriodCores

/-- Expand all minimal entry cores, deriving rather than requesting their
uniform centre bounds. -/
def toCompatiblePeriodSchedules {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : CompatiblePeriodCores curve geometry) :
    CompatiblePeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (cores.aCore differential cycle).toCompatibleDifferentialSchedule
  bSchedule := fun differential cycle =>
    (cores.bCore differential cycle).toCompatibleDifferentialSchedule

end CompatiblePeriodCores

namespace StrictCompatiblePeriodCores

/-- Derive the ordinary compatible cores entry by entry. -/
def toCompatiblePeriodCores {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : StrictCompatiblePeriodCores curve geometry) :
    CompatiblePeriodCores curve geometry where
  aCore := fun differential cycle =>
    (cores.aCore differential cycle).toCompatibleDifferentialCore
  bCore := fun differential cycle =>
    (cores.bCore differential cycle).toCompatibleDifferentialCore

/-- Expand strict entry data all the way to compatible period schedules. -/
def toCompatiblePeriodSchedules {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (cores : StrictCompatiblePeriodCores curve geometry) :
    CompatiblePeriodSchedules curve geometry :=
  cores.toCompatiblePeriodCores.toCompatiblePeriodSchedules

end StrictCompatiblePeriodCores

namespace CompatiblePeriodSchedules

/-- Construct the ordinary prepared period schedules after deriving every
whole-cycle refinement program. -/
def toPeriodSchedules {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry) :
    PeriodSchedules curve geometry where
  aSchedule := fun differential cycle =>
    (schedules.aSchedule differential cycle).toDifferentialSchedule
  bSchedule := fun differential cycle =>
    (schedules.bSchedule differential cycle).toDifferentialSchedule

end CompatiblePeriodSchedules

namespace PeriodSchedules

/-- Assemble the actual A/B period programs; every matrix row shares the same
geometric cycle family by construction. -/
def toPeriodData {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry) :
    CCL.Riemann.PeriodMatrix.PeriodData curve where
  cycles := geometry.cycles
  aProgram := fun differential cycle =>
    (schedules.aSchedule differential cycle).toCertifiedPeriodProgram
  bProgram := fun differential cycle =>
    (schedules.bSchedule differential cycle).toCertifiedPeriodProgram

/-- Attach one constructive fraction-free nondegeneracy certificate to the
period data assembled from prepared schedules. -/
def normalized {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry)
    (inverse : CCL.Riemann.PeriodMatrix.ScaledInverseCertificate
      schedules.toPeriodData.aMatrix) :
    CCL.Riemann.PeriodMatrix.NormalizedPeriodData curve where
  toPeriodData := schedules.toPeriodData
  aInverse := inverse

/-- Period data assembled from prepared schedules realizes any raw basis
realized by their common differential-independent geometry. -/
theorem cyclesRealization {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : PeriodSchedules curve geometry)
    {raw : LiftedSymplecticCycles 2 genus}
    (realizes : geometry.Realizes raw) :
    SymplecticCycleRealization curve schedules.toPeriodData.cycles raw := by
  exact .prepared geometry realizes

end PeriodSchedules

namespace CompatiblePeriodSchedules

/-- Period data with every convergence estimate derived from compatible
prepared partitions. -/
def toPeriodData {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry) :
    CCL.Riemann.PeriodMatrix.PeriodData curve :=
  schedules.toPeriodSchedules.toPeriodData

/-- Normalize compatible prepared schedules after one synchronized scaled
inverse and its apartness witness have been supplied. -/
def normalized {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry)
    (inverse : CCL.Riemann.PeriodMatrix.ScaledInverseCertificate
      schedules.toPeriodData.aMatrix) :
    CCL.Riemann.PeriodMatrix.NormalizedPeriodData curve :=
  schedules.toPeriodSchedules.normalized inverse

/-- The derived period data retains the common prepared-to-raw basis
realization. -/
theorem cyclesRealization {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry : SymplecticCycleSchedule curve}
    (schedules : CompatiblePeriodSchedules curve geometry)
    {raw : LiftedSymplecticCycles 2 genus}
    (realizes : geometry.Realizes raw) :
    SymplecticCycleRealization curve schedules.toPeriodData.cycles raw :=
  schedules.toPeriodSchedules.cyclesRealization realizes

end CompatiblePeriodSchedules

end CCL.Riemann.PreparedCycleModels
