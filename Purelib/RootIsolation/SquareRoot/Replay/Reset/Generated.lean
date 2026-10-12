module
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Riemann.PreparedEightStepSameBox
import Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Certificate.Raw
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Certificate.Raw
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Certificate
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Examples.Riemann.PreparedEightStepSameBox (ParametricResetStep)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
  (DirectBoundaryBounds
   MovingRecenter
   QuadraticAmbientBudget
   QuadraticAmbientSideMajorantBounds
   QuadraticBoxSideMajorantBounds)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Generated moving-reset certificate bridge

This module replays one Python-selected moving recenter.  Python owns every
cross-record rational comparison; a concrete curve bridge only identifies
the displayed evaluations and the finite moving-window branch.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.Reset.Generated

open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier

/-- Finite checked data for one prescribed quadratic source reset.

Retain the exact source and target parameters, polynomial variation, endpoint boxes and predicted-movement floor for the
supplied generated cell. -/
structure GeneratedResetCellCertificate
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    (segment : ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (data : PreparedResetCellBoundsData)
    (left : Endpoint) (request : StepRequest) : Prop where
  /-- The retained source parameter equals the exact evaluation prescribed by the cell. -/ sourceParameter :
    polynomial.eval (segment.pointAt left.parameter) =
      (data.source.sourceParameter 0).toGaussian
  /-- The retained target parameter equals the exact evaluation prescribed by the cell. -/ targetParameter :
    polynomial.eval (segment.pointAt request.endpoint.parameter) =
      (data.source.targetParameter 0).toGaussian
  /-- The retained polynomial-variation reading equals the prescribed exact upper bound. -/ variation :
    Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter = data.source.variationUpper.toRational
  /-- The retained source and target parameters are distinct. -/ different :
    polynomial.eval (segment.pointAt left.parameter) ≠
      polynomial.eval (segment.pointAt request.endpoint.parameter)
  /-- The retained before owner's box meets the required strict diameter bound. -/ beforeBoxSmall :
    data.beforeCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained after owner's box meets the required strict diameter bound. -/ afterBoxSmall :
    data.afterCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained before owner's box refines the required root ambient box. -/ beforeBoxRefines :
    data.beforeCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The retained after owner's box refines the required root ambient box. -/ afterBoxRefines :
    data.afterCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The original predicted movement is bounded by the retained transport floor. -/ predictedLeFloor :
    preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.marginFloor.toRational

namespace GeneratedResetCellCertificate

/-- Construct the retained quadratic reset step from the supplied finite cell certificate.

The original inherited and strengthened owners fail the carrying test; the actual moving-recenter result supplies the
prepared source, exact cache identities and certified transport bounds. -/
theorem step
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {data : PreparedResetCellBoundsData}
    {left : Endpoint} {request : StepRequest}
    (certificate : SquareRoot.Replay.Reset.Generated.GeneratedResetCellCertificate segment within data left
      request)
    (owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (state : ParametricSameBoxState segment left owner
      data.beforeCell.box.toBox data.beforeUpper.toRational
        data.marginFloor.toRational)
    (clearanceLe : owner.track.initial.clearance.bound ≤
      data.beforeUpper.toRational ^ 2 / 4) :
    ParametricResetStep segment within left owner request
      data.afterCell.box.toBox data.afterUpper.toRational
        data.marginFloor.toRational := by
  have ready : AlreadyPrepared segment left owner request := by
    refine ⟨?_, ?_, ?_⟩
    · rw [state.boxEq]
      exact certificate.beforeBoxSmall
    · exact certificate.predictedLeFloor.trans state.clearanceFloor
    · rw [state.boxEq]
      exact certificate.beforeBoxRefines
  have notCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < owner.track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact clearanceLe.trans data.beforeQuarter_le_variation
  have sourceDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.beforeCell.box.toBox data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [certificate.sourceParameter, ← data.sourceBox_eq_before]
    exact data.source.directBoundaryBounds 0
  let sourceCache :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          owner.track.initial.box data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [state.boxEq]
    exact sourceDirectBounds
  have strengthenedLeVariation :
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound ≤
          data.source.variationUpper.toRational := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
      owner sourceCache.leftNonzero sourceCache.rightNonzero
        sourceCache.bottomNonzero sourceCache.topNonzero]
    exact Fraction.Order.Basic.max_le (clearanceLe.trans data.beforeQuarter_le_variation)
      (sourceCache.le_upper.trans data.sourceUpper_le_variation)
  have strengthenedNotCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact strengthenedLeVariation
  have oldBoxProper : data.beforeCell.box.toBox.Proper := by
    rw [← state.boxEq]
    exact owner.track.initial.proper
  have resetBoxProjection
      (parameterNonzero : polynomial.eval (segment.pointAt left.parameter) ≠ 0)
      (sourceProper : data.beforeCell.box.toBox.Proper) :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
          (polynomial.eval (segment.pointAt left.parameter)) parameterNonzero
            data.beforeCell.box.toBox sourceProper =
        some data.afterCell.box.toBox := by
    have generated := data.resetBoxProjection
      (certificate.sourceParameter ▸ parameterNonzero) sourceProper
    simpa only [certificate.sourceParameter] using generated
  let movingCache :
      { reset : MovingRecenter _ owner //
        SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
          some reset } := by
    generalize found :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner = result
    cases result with
    | none =>
        have succeeds : Option.map (fun reset => reset.ownerBox)
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
              some data.afterCell.box.toBox := by
          rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
            owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
            resetBoxProjection owner.parameterNonzero oldBoxProper]
        rw [found] at succeeds
        cases succeeds
    | some reset => exact ⟨reset, rfl⟩
  let moving := movingCache.1
  have movingFound :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
        some moving := movingCache.2
  have recenteredEq : recentered owner = moving.owner :=
    recentered_eq_of_movingRecenter_eq_some owner moving movingFound
  have movingBoxEq : moving.ownerBox = data.afterCell.box.toBox := by
    have mapped : Option.map (fun reset => reset.ownerBox)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
          some data.afterCell.box.toBox := by
      rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
        owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
        resetBoxProjection owner.parameterNonzero oldBoxProper]
    rw [movingFound] at mapped
    exact Option.some.inj mapped
  have finalSourceParameter :
      polynomial.eval (segment.pointAt left.parameter) =
        (data.final.sourceParameter 0).toGaussian :=
    certificate.sourceParameter.trans data.sourceParameter_eq_final
  have finalDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [finalSourceParameter, ← data.finalBox_eq_after]
    exact data.final.directBoundaryBounds 0
  have movingDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter)) moving.ownerBox
          data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [movingBoxEq]
    exact finalDirectBounds
  have movingClearanceLower : data.final.directLower.toRational ≤
      moving.owner.track.initial.clearance.bound := by
    rw [moving.ownerDirectClearanceBound]
    exact movingDirectBounds.lower_le
  have selectedSmall :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < moving.owner.track.initial.clearance.bound := by
    rw [certificate.variation]
    exact data.variation_lt_finalLower.trans_le movingClearanceLower
  have recenteredReady : AlreadyPrepared segment left (recentered owner)
      request := by
    rw [recenteredEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [moving.ownerInitialBox, movingBoxEq]
      exact certificate.afterBoxSmall
    · exact certificate.predictedLeFloor.trans
        (data.transportFloor_le_finalLower.trans movingClearanceLower)
    · rw [moving.ownerInitialBox, movingBoxEq]
      exact certificate.afterBoxRefines
  have recenteredCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound := by
    rw [recenteredEq]
    exact selectedSmall
  have preparedEqRecentered : prepared segment left owner request =
      recentered owner :=
    prepared_eq_recentered_of_ready segment left owner request ready notCarries
      strengthenedNotCarries recenteredReady recenteredCarries
  have preparedEqMoving : prepared segment left owner request = moving.owner :=
    preparedEqRecentered.trans recenteredEq
  have sourceNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter)) ≤ (256 : Fraction.Rational) := by
    rw [certificate.sourceParameter]
    exact (data.source.sourceNormSq_le 0).trans
      data.sourceNormSqUpper_le_twoHundredFiftySix
  have movingBudget :
      QuadraticAmbientBudget
        moving.owner := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
      moving.owner data.afterCell.box.toBox
    · exact moving.ownerInitialBox.trans movingBoxEq
    · exact moving.ownerAmbientBox.trans movingBoxEq
    · exact sourceNormSqLe
    · simpa only [← data.finalBox_eq_after] using data.finalLeftCoordinate_ne
    · simpa only [← data.finalBox_eq_after] using data.finalRightCoordinate_ne
    · simpa only [← data.finalBox_eq_after] using data.finalBottomCoordinate_ne
    · simpa only [← data.finalBox_eq_after] using data.finalTopCoordinate_ne
    · have bound := data.final.leftXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.rightXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.bottomYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
    · have bound := data.final.topYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
  have movingAmbientLeftLe :
      moving.owner.track.initial.ambientLeftClearance.bound ≤
        data.afterUpper.toRational := by
    rw [moving.ownerAmbientLeftClearanceBound]
    exact movingDirectBounds.le_upper.trans data.finalUpper_le_afterUpper
  have movingMargin : data.source.residualMarginFloor.toRational ≤
      moving.owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    apply data.resetResidual_le_finalLower_sub_displacement.trans
    apply Fraction.Order.Arithmetic.sub_le_sub_direct movingClearanceLower
    rw [certificate.sourceParameter, certificate.targetParameter]
    exact data.source.displacement_le 0
  have targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤
          (256 : Fraction.Rational) := by
    rw [certificate.targetParameter]
    exact (data.source.targetNormSq_le 0).trans
      data.targetNormSqUpper_le_twoHundredFiftySix
  have finalBoxSideBounds :
      QuadraticBoxSideMajorantBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.sideMajorantUpper.toRational := by
    have bounds := data.final.quadraticBoxSideMajorantBounds 0
      data.final.sideMajorantUpper.toRational data.one_le_finalSideMajorant le_rfl
    rw [← finalSourceParameter, data.finalBox_eq_after] at bounds
    exact bounds
  have movingSideBounds :
      QuadraticAmbientSideMajorantBounds
        moving.owner data.final.sideMajorantUpper.toRational := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box
      moving.owner data.afterCell.box.toBox data.final.sideMajorantUpper.toRational
    · exact moving.ownerInitialBox.trans movingBoxEq
    · rw [moving.ownerAmbientBox, movingBoxEq]
      exact Box.refines_refl _
    · exact finalBoxSideBounds
  let cached := CachedSource.canonical segment left owner request
  have cachedSmall :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact selectedSmall
  have cachedInitialBox : cached.preparedOwner.track.initial.box =
      data.afterCell.box.toBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerInitialBox.trans movingBoxEq
  have cachedAmbientBox : cached.preparedOwner.ambient =
      data.afterCell.box.toBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerAmbientBox.trans movingBoxEq
  have cachedDominance :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.AmbientClearanceDominance
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerDominance
  have cachedBudget :
      QuadraticAmbientBudget
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingBudget
  have cachedMargin : data.source.residualMarginFloor.toRational ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingMargin
  have cachedSideBounds :
      QuadraticAmbientSideMajorantBounds
        cached.preparedOwner data.final.sideMajorantUpper.toRational := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingSideBounds
  have cachedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        data.afterUpper.toRational := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingAmbientLeftLe
  let advanceCache := retainedFloorQuadraticAdvanceCache segment within left
    owner request cached cachedSmall certificate.different
      data.marginFloor.toRational data.source.residualMarginFloor.toRational
        data.final.sideMajorantUpper.toRational certificate.predictedLeFloor
          cachedDominance data.resetResidual_positive cachedMargin
          cachedSideBounds data.retainedFloorTradeoff_sound cachedBudget
              targetNormSqLe
  have cachedQuarterLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        data.afterUpper.toRational ^ 2 / 4 := by
    change cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
        (4 : Coordinate)⁻¹ ≤ data.afterUpper.toRational ^ 2 *
          (4 : Coordinate)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
          cachedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Coordinate) < 4)).le
  refine
    { canonicalSmall := ?_
      preparedBox := cachedInitialBox
      nextState :=
        { boxEq := advanceCache.initialBox.trans cachedInitialBox
          clearanceFloor := advanceCache.clearanceFloor
          dominance := advanceCache.dominance
          budget := advanceCache.budget
          ambientLeftLe := (advanceCache.ambientLeftQuarterSq.trans
            cachedQuarterLe).trans data.after_contracts
          ambientRefines := ?_ }
      nextAmbientLeftLeQuarter :=
        advanceCache.ambientLeftQuarterSq.trans cachedQuarterLe
      nextClearanceLeQuarter :=
        advanceCache.clearanceQuarterSq.trans cachedQuarterLe }
  · rw [preparedEqMoving]
    exact selectedSmall
  · rw [advanceCache.ambientBox, cachedAmbientBox]
    exact Box.refines_refl _

end GeneratedResetCellCertificate

/-- Finite checked data for a quadratic reset with separate source and target transport floors.

The certificate retains exact parameter evaluations, the variation value, both original boxes and their required ambient
refinements. -/
structure GeneratedParametricResetCellCertificate
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    (segment : ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (data : PreparedParametricResetCellBoundsData)
    (left : Endpoint) (request : StepRequest) : Prop where
  /-- The retained source parameter equals the exact evaluation prescribed by the cell. -/ sourceParameter :
    polynomial.eval (segment.pointAt left.parameter) =
      (data.source.sourceParameter 0).toGaussian
  /-- The retained target parameter equals the exact evaluation prescribed by the cell. -/ targetParameter :
    polynomial.eval (segment.pointAt request.endpoint.parameter) =
      (data.source.targetParameter 0).toGaussian
  /-- The retained polynomial-variation reading equals the prescribed exact upper bound. -/ variation :
    Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter = data.source.variationUpper.toRational
  /-- The retained source and target parameters are distinct. -/ different :
    polynomial.eval (segment.pointAt left.parameter) ≠
      polynomial.eval (segment.pointAt request.endpoint.parameter)
  /-- The retained before owner's box meets the required strict diameter bound. -/ beforeBoxSmall :
    data.beforeCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained after owner's box meets the required strict diameter bound. -/ afterBoxSmall :
    data.afterCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained before owner's box refines the required root ambient box. -/ beforeBoxRefines :
    data.beforeCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The retained after owner's box refines the required root ambient box. -/ afterBoxRefines :
    data.afterCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The original predicted movement is bounded by the retained before transport floor. -/ predictedLeBeforeFloor :
    preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.beforeCell.transportMargin.toRational
  /-- The original predicted movement is bounded by the retained after transport floor. -/ predictedLeAfterFloor :
    preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.afterCell.transportMargin.toRational

/-- Semantic geometry needed to select the second moving recenter on one
generated edge.  All branch inequalities and both box projections are stored
in `data`; this record only connects them to the concrete segment. -/
structure GeneratedParametricDoubleResetCellCertificate
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    (segment : ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (data : PreparedParametricDoubleResetCellBoundsData)
    (left : Endpoint) (request : StepRequest) : Prop where
  /-- The retained source parameter equals the exact evaluation prescribed by the cell. -/ sourceParameter :
    polynomial.eval (segment.pointAt left.parameter) =
      (data.source.sourceParameter 0).toGaussian
  /-- The retained target parameter equals the exact evaluation prescribed by the cell. -/ targetParameter :
    polynomial.eval (segment.pointAt request.endpoint.parameter) =
      (data.source.targetParameter 0).toGaussian
  /-- The retained polynomial-variation reading equals the prescribed exact upper bound. -/ variation :
    Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter = data.source.variationUpper.toRational
  /-- The retained source and target parameters are distinct. -/ different :
    polynomial.eval (segment.pointAt left.parameter) ≠
      polynomial.eval (segment.pointAt request.endpoint.parameter)
  /-- The retained before owner's box meets the required strict diameter bound. -/ beforeBoxSmall :
    data.beforeCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained intermediate owner's box meets the required strict diameter bound. -/ intermediateBoxSmall :
    data.intermediate.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained after owner's box meets the required strict diameter bound. -/ afterBoxSmall :
    data.afterCell.box.toBox.diagonalSq < request.rootDiameter
  /-- The retained before owner's box refines the required root ambient box. -/ beforeBoxRefines :
    data.beforeCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The retained intermediate owner's box refines the required root ambient box. -/ intermediateBoxRefines :
    data.intermediate.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The retained after owner's box refines the required root ambient box. -/ afterBoxRefines :
    data.afterCell.box.toBox.Refines
    (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)
  /-- The original predicted movement is bounded by the retained before transport floor. -/ predictedLeBeforeFloor :
    preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.beforeCell.transportMargin.toRational
  /-- The original predicted movement is bounded by the retained intermediate transport floor. -/
    predictedLeIntermediateFloor : preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.intermediateMargin.toRational
  /-- The original predicted movement is bounded by the retained after transport floor. -/ predictedLeAfterFloor :
    preparedClearanceLower segment left request ≤
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
      data.afterCell.transportMargin.toRational

namespace GeneratedParametricResetCellCertificate

/-- Construct the original parametric quadratic reset using the retained before and after floors.

The checked recentering result determines the same prepared owner and its advance cache; all transport bounds refer to
those retained endpoints. -/
theorem step
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {data : PreparedParametricResetCellBoundsData}
    {left : Endpoint} {request : StepRequest}
    (certificate : SquareRoot.Replay.Reset.Generated.GeneratedParametricResetCellCertificate segment within data left
      request)
    (owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (state : ParametricSameBoxState segment left owner
      data.beforeCell.box.toBox data.beforeUpper.toRational
        data.beforeCell.transportMargin.toRational)
    (clearanceLeQuarter : owner.track.initial.clearance.bound ≤
      data.beforeUpper.toRational ^ 2 / 4) :
    ParametricResetStep segment within left owner request
      data.afterCell.box.toBox data.afterUpper.toRational
        data.afterCell.transportMargin.toRational := by
  have ready : AlreadyPrepared segment left owner request := by
    refine ⟨?_, ?_, ?_⟩
    · rw [state.boxEq]
      exact certificate.beforeBoxSmall
    · exact certificate.predictedLeBeforeFloor.trans state.clearanceFloor
    · rw [state.boxEq]
      exact certificate.beforeBoxRefines
  have notCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < owner.track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact clearanceLeQuarter.trans data.beforeQuarter_le_variation
  have sourceDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.beforeCell.box.toBox data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [certificate.sourceParameter, ← data.sourceBox_eq_before]
    exact data.source.directBoundaryBounds 0
  let sourceCache :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          owner.track.initial.box data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [state.boxEq]
    exact sourceDirectBounds
  have strengthenedLeVariation :
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound ≤
          data.source.variationUpper.toRational := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
      owner sourceCache.leftNonzero sourceCache.rightNonzero
        sourceCache.bottomNonzero sourceCache.topNonzero]
    exact Fraction.Order.Basic.max_le
      (clearanceLeQuarter.trans data.beforeQuarter_le_variation)
      (sourceCache.le_upper.trans data.sourceUpper_le_variation)
  have strengthenedNotCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact strengthenedLeVariation
  have oldBoxProper : data.beforeCell.box.toBox.Proper := by
    rw [← state.boxEq]
    exact owner.track.initial.proper
  have resetBoxProjection
      (parameterNonzero : polynomial.eval (segment.pointAt left.parameter) ≠ 0)
      (sourceProper : data.beforeCell.box.toBox.Proper) :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
          (polynomial.eval (segment.pointAt left.parameter)) parameterNonzero
            data.beforeCell.box.toBox sourceProper =
        some data.afterCell.box.toBox := by
    have generated := data.resetBoxProjection
      (certificate.sourceParameter ▸ parameterNonzero) sourceProper
    simpa only [certificate.sourceParameter] using generated
  let movingCache :
      { reset : MovingRecenter _ owner //
        SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
          some reset } := by
    generalize found :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner = result
    cases result with
    | none =>
        have succeeds : Option.map (fun reset => reset.ownerBox)
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
              some data.afterCell.box.toBox := by
          rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
            owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
            resetBoxProjection owner.parameterNonzero oldBoxProper]
        rw [found] at succeeds
        cases succeeds
    | some reset => exact ⟨reset, rfl⟩
  let moving := movingCache.1
  have movingFound :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
        some moving := movingCache.2
  have recenteredEq : recentered owner = moving.owner :=
    recentered_eq_of_movingRecenter_eq_some owner moving movingFound
  have movingBoxEq : moving.ownerBox = data.afterCell.box.toBox := by
    have mapped : Option.map (fun reset => reset.ownerBox)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
          some data.afterCell.box.toBox := by
      rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
        owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
        resetBoxProjection owner.parameterNonzero oldBoxProper]
    rw [movingFound] at mapped
    exact Option.some.inj mapped
  have finalSourceParameter :
      polynomial.eval (segment.pointAt left.parameter) =
        (data.final.sourceParameter 0).toGaussian :=
    certificate.sourceParameter.trans data.sourceParameter_eq_final
  have finalDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [finalSourceParameter, ← data.finalBox_eq_after]
    exact data.final.directBoundaryBounds 0
  have movingDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter)) moving.ownerBox
          data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [movingBoxEq]
    exact finalDirectBounds
  have movingClearanceLower : data.final.directLower.toRational ≤
      moving.owner.track.initial.clearance.bound := by
    rw [moving.ownerDirectClearanceBound]
    exact movingDirectBounds.lower_le
  have selectedSmall :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < moving.owner.track.initial.clearance.bound := by
    rw [certificate.variation]
    exact data.variation_lt_finalLower.trans_le movingClearanceLower
  have recenteredReady : AlreadyPrepared segment left (recentered owner)
      request := by
    rw [recenteredEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [moving.ownerInitialBox, movingBoxEq]
      exact certificate.afterBoxSmall
    · exact certificate.predictedLeAfterFloor.trans
        (data.transportFloor_le_finalLower.trans movingClearanceLower)
    · rw [moving.ownerInitialBox, movingBoxEq]
      exact certificate.afterBoxRefines
  have recenteredCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound := by
    rw [recenteredEq]
    exact selectedSmall
  have preparedEqRecentered : prepared segment left owner request =
      recentered owner :=
    prepared_eq_recentered_of_ready segment left owner request ready notCarries
      strengthenedNotCarries recenteredReady recenteredCarries
  have preparedEqMoving : prepared segment left owner request = moving.owner :=
    preparedEqRecentered.trans recenteredEq
  have sourceNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter)) ≤ (256 : Fraction.Rational) := by
    rw [certificate.sourceParameter]
    exact (data.source.sourceNormSq_le 0).trans
      data.sourceNormSqUpper_le_twoHundredFiftySix
  have movingBudget :
      QuadraticAmbientBudget
        moving.owner := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box_all
      moving.owner data.afterCell.box.toBox
    · exact moving.ownerInitialBox.trans movingBoxEq
    · exact moving.ownerAmbientBox.trans movingBoxEq
    · exact sourceNormSqLe
    · have bound := data.final.leftXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.rightXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.bottomYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
    · have bound := data.final.topYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
  have movingAmbientLeftLe :
      moving.owner.track.initial.ambientLeftClearance.bound ≤
        data.afterUpper.toRational := by
    rw [moving.ownerAmbientLeftClearanceBound]
    exact movingDirectBounds.le_upper.trans data.finalUpper_le_afterUpper
  have movingMargin : data.source.residualMarginFloor.toRational ≤
      moving.owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    apply data.resetResidual_le_finalLower_sub_displacement.trans
    apply Fraction.Order.Arithmetic.sub_le_sub_direct movingClearanceLower
    rw [certificate.sourceParameter, certificate.targetParameter]
    exact data.source.displacement_le 0
  have targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤
          (256 : Fraction.Rational) := by
    rw [certificate.targetParameter]
    exact (data.source.targetNormSq_le 0).trans
      data.targetNormSqUpper_le_twoHundredFiftySix
  have finalBoxSideBounds :
      QuadraticBoxSideMajorantBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.sideMajorantUpper.toRational := by
    have bounds := data.final.quadraticBoxSideMajorantBounds 0
      data.final.sideMajorantUpper.toRational data.one_le_finalSideMajorant le_rfl
    rw [← finalSourceParameter, data.finalBox_eq_after] at bounds
    exact bounds
  have movingSideBounds :
      QuadraticAmbientSideMajorantBounds
        moving.owner data.final.sideMajorantUpper.toRational := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box
      moving.owner data.afterCell.box.toBox data.final.sideMajorantUpper.toRational
    · exact moving.ownerInitialBox.trans movingBoxEq
    · rw [moving.ownerAmbientBox, movingBoxEq]
      exact Box.refines_refl _
    · exact finalBoxSideBounds
  let cached := CachedSource.canonical segment left owner request
  have cachedSmall :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact selectedSmall
  have cachedInitialBox : cached.preparedOwner.track.initial.box =
      data.afterCell.box.toBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerInitialBox.trans movingBoxEq
  have cachedAmbientBox : cached.preparedOwner.ambient =
      data.afterCell.box.toBox := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerAmbientBox.trans movingBoxEq
  have cachedDominance :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.AmbientClearanceDominance
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact moving.ownerDominance
  have cachedBudget :
      QuadraticAmbientBudget
        cached.preparedOwner := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingBudget
  have cachedMargin : data.source.residualMarginFloor.toRational ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingMargin
  have cachedSideBounds :
      QuadraticAmbientSideMajorantBounds
        cached.preparedOwner data.final.sideMajorantUpper.toRational := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingSideBounds
  have cachedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        data.afterUpper.toRational := by
    rw [show cached.preparedOwner = prepared segment left owner request by rfl,
      preparedEqMoving]
    exact movingAmbientLeftLe
  let advanceCache := retainedFloorQuadraticAdvanceCache segment within left
    owner request cached cachedSmall certificate.different
      data.afterCell.transportMargin.toRational
        data.source.residualMarginFloor.toRational
        data.final.sideMajorantUpper.toRational certificate.predictedLeAfterFloor
          cachedDominance data.resetResidual_positive cachedMargin
          cachedSideBounds data.retainedFloorTradeoff_sound cachedBudget
              targetNormSqLe
  have cachedQuarterLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        data.afterUpper.toRational ^ 2 / 4 := by
    change cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
        (4 : Coordinate)⁻¹ ≤ data.afterUpper.toRational ^ 2 *
          (4 : Coordinate)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
          cachedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Coordinate) < 4)).le
  refine
    { canonicalSmall := ?_
      preparedBox := cachedInitialBox
      nextState :=
        { boxEq := advanceCache.initialBox.trans cachedInitialBox
          clearanceFloor := advanceCache.clearanceFloor
          dominance := advanceCache.dominance
          budget := advanceCache.budget
          ambientLeftLe := (advanceCache.ambientLeftQuarterSq.trans
            cachedQuarterLe).trans data.after_contracts
          ambientRefines := ?_ }
      nextAmbientLeftLeQuarter :=
        advanceCache.ambientLeftQuarterSq.trans cachedQuarterLe
      nextClearanceLeQuarter :=
        advanceCache.clearanceQuarterSq.trans cachedQuarterLe }
  · rw [preparedEqMoving]
    exact selectedSmall
  · rw [advanceCache.ambientBox, cachedAmbientBox]
    exact Box.refines_refl _

end GeneratedParametricResetCellCertificate

namespace GeneratedParametricDoubleResetCellCertificate

/-- Construct the checked quadratic transport that performs two original moving recenters.

The first recentered owner is ready but still fails the carrying test, while the second supplies the actual prepared
source and exact cached transport bounds. -/
theorem
  step
    {polynomial : CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient
      start finish}
    {within : segment.WithinAmbient}
    {data : PreparedParametricDoubleResetCellBoundsData}
    {left : Endpoint} {request : StepRequest}
    (certificate : SquareRoot.Replay.Reset.Generated.GeneratedParametricDoubleResetCellCertificate segment within
      data left request)
    (owner : SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (state : ParametricSameBoxState segment left owner
      data.beforeCell.box.toBox data.beforeUpper.toRational
        data.beforeCell.transportMargin.toRational)
    (clearanceLeQuarter : owner.track.initial.clearance.bound ≤
      data.beforeUpper.toRational ^ 2 / 4) :
    ParametricResetStep segment within left owner request
      data.afterCell.box.toBox data.afterUpper.toRational
        data.afterCell.transportMargin.toRational := by
  have ready : AlreadyPrepared segment left owner request := by
    refine ⟨?_, ?_, ?_⟩
    · rw [state.boxEq]
      exact certificate.beforeBoxSmall
    · exact certificate.predictedLeBeforeFloor.trans state.clearanceFloor
    · rw [state.boxEq]
      exact certificate.beforeBoxRefines
  have notCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter < owner.track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact clearanceLeQuarter.trans data.beforeQuarter_le_variation
  have sourceDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.beforeCell.box.toBox data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [certificate.sourceParameter, ← data.sourceBox_eq_before]
    exact data.source.directBoundaryBounds 0
  let sourceCache :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          owner.track.initial.box data.source.directLower.toRational
            data.source.directUpper.toRational := by
    rw [state.boxEq]
    exact sourceDirectBounds
  have strengthenedLeVariation :
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound ≤
          data.source.variationUpper.toRational := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
      owner sourceCache.leftNonzero sourceCache.rightNonzero
        sourceCache.bottomNonzero sourceCache.topNonzero]
    exact Fraction.Order.Basic.max_le
      (clearanceLeQuarter.trans data.beforeQuarter_le_variation)
      (sourceCache.le_upper.trans data.sourceUpper_le_variation)
  have strengthenedNotCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound := by
    apply not_lt_of_ge
    rw [certificate.variation]
    exact strengthenedLeVariation
  have oldBoxProper : data.beforeCell.box.toBox.Proper := by
    rw [← state.boxEq]
    exact owner.track.initial.proper
  have firstResetBoxProjection
      (parameterNonzero : polynomial.eval
        (segment.pointAt left.parameter) ≠ 0)
      (sourceProper : data.beforeCell.box.toBox.Proper) :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
          (polynomial.eval (segment.pointAt left.parameter)) parameterNonzero
            data.beforeCell.box.toBox sourceProper =
        some data.intermediate.box.toBox := by
    have generated := data.firstResetBoxProjection
      (certificate.sourceParameter ▸ parameterNonzero) sourceProper
    simpa only [certificate.sourceParameter] using generated
  let firstMovingCache :
      { reset : MovingRecenter _ owner //
        SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
          some reset } := by
    generalize found :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner = result
    cases result with
    | none =>
        have succeeds : Option.map (fun reset => reset.ownerBox)
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
              some data.intermediate.box.toBox := by
          rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
            owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
            firstResetBoxProjection owner.parameterNonzero oldBoxProper]
        rw [found] at succeeds
        cases succeeds
    | some reset => exact ⟨reset, rfl⟩
  let firstMoving := firstMovingCache.1
  have firstMovingFound :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner =
        some firstMoving := firstMovingCache.2
  have firstRecenteredEq : recentered owner = firstMoving.owner :=
    recentered_eq_of_movingRecenter_eq_some owner firstMoving firstMovingFound
  have firstMovingBoxEq :
      firstMoving.ownerBox = data.intermediate.box.toBox := by
    have mapped : Option.map (fun reset => reset.ownerBox)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner) =
          some data.intermediate.box.toBox := by
      rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
        owner data.beforeCell.box.toBox oldBoxProper state.boxEq,
        firstResetBoxProjection owner.parameterNonzero oldBoxProper]
    rw [firstMovingFound] at mapped
    exact Option.some.inj mapped
  have intermediateSourceParameter :
      polynomial.eval (segment.pointAt left.parameter) =
        (data.intermediate.sourceParameter 0).toGaussian :=
    certificate.sourceParameter.trans data.sourceParameter_eq_intermediate
  have intermediateDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.intermediate.box.toBox data.intermediate.directLower.toRational
            data.intermediate.directUpper.toRational := by
    rw [intermediateSourceParameter]
    exact data.intermediate.directBoundaryBounds 0
  have firstMovingDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter)) firstMoving.ownerBox
          data.intermediate.directLower.toRational
            data.intermediate.directUpper.toRational := by
    rw [firstMovingBoxEq]
    exact intermediateDirectBounds
  have firstMovingClearanceLower :
      data.intermediate.directLower.toRational ≤
        firstMoving.owner.track.initial.clearance.bound := by
    rw [firstMoving.ownerDirectClearanceBound]
    exact firstMovingDirectBounds.lower_le
  have firstMovingClearanceUpper :
      firstMoving.owner.track.initial.clearance.bound ≤
        data.intermediate.directUpper.toRational := by
    rw [firstMoving.ownerDirectClearanceBound]
    exact firstMovingDirectBounds.le_upper
  let firstMovingInitialDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          firstMoving.owner.track.initial.box
            data.intermediate.directLower.toRational
              data.intermediate.directUpper.toRational := by
    rw [firstMoving.ownerInitialBox]
    exact firstMovingDirectBounds
  have firstReady : AlreadyPrepared segment left (recentered owner)
      request := by
    rw [firstRecenteredEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [firstMoving.ownerInitialBox, firstMovingBoxEq]
      exact certificate.intermediateBoxSmall
    · exact certificate.predictedLeIntermediateFloor.trans
        (data.transportFloor_le_intermediateLower.trans
          firstMovingClearanceLower)
    · rw [firstMoving.ownerInitialBox, firstMovingBoxEq]
      exact certificate.intermediateBoxRefines
  have firstNotCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound := by
    rw [firstRecenteredEq]
    apply not_lt_of_ge
    rw [certificate.variation]
    exact firstMovingClearanceUpper.trans data.intermediateUpper_le_variation
  have firstStrengthenedLeVariation :
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        firstMoving.owner).track.initial.clearance.bound ≤
          data.source.variationUpper.toRational := by
    exact (Examples.Riemann.PreparedEightStepSameBox.strengthenQuadraticOwner_clearance_le_upper_of_directBounds
      firstMoving.owner data.intermediate.directLower.toRational
        data.intermediate.directUpper.toRational firstMovingInitialDirectBounds
          firstMovingClearanceUpper).trans data.intermediateUpper_le_variation
  have firstStrengthenedNotCarries : ¬
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          (recentered owner)).track.initial.clearance.bound := by
    rw [firstRecenteredEq]
    apply not_lt_of_ge
    rw [certificate.variation]
    exact firstStrengthenedLeVariation
  have intermediateProper : data.intermediate.box.toBox.Proper := by
    rw [← firstMovingBoxEq, ← firstMoving.ownerInitialBox]
    exact firstMoving.owner.track.initial.proper
  have secondResetBoxProjection
      (parameterNonzero : polynomial.eval
        (segment.pointAt left.parameter) ≠ 0)
      (sourceProper : data.intermediate.box.toBox.Proper) :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
          (polynomial.eval (segment.pointAt left.parameter)) parameterNonzero
            data.intermediate.box.toBox sourceProper =
        some data.afterCell.box.toBox := by
    have generated := data.secondResetBoxProjection
      (certificate.sourceParameter ▸ parameterNonzero) sourceProper
    simpa only [certificate.sourceParameter] using generated
  let secondMovingCache :
      { reset : MovingRecenter _
          firstMoving.owner //
        SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
          firstMoving.owner = some reset } := by
    generalize found :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
        firstMoving.owner = result
    cases result with
    | none =>
        have succeeds : Option.map (fun reset => reset.ownerBox)
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
              firstMoving.owner) = some data.afterCell.box.toBox := by
          rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
            firstMoving.owner data.intermediate.box.toBox intermediateProper
              (firstMoving.ownerInitialBox.trans firstMovingBoxEq),
            secondResetBoxProjection firstMoving.owner.parameterNonzero
              intermediateProper]
        rw [found] at succeeds
        cases succeeds
    | some reset => exact ⟨reset, rfl⟩
  let secondMoving := secondMovingCache.1
  have secondMovingFound :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
        firstMoving.owner = some secondMoving := secondMovingCache.2
  have secondRecenteredEq :
      recentered firstMoving.owner = secondMoving.owner :=
    recentered_eq_of_movingRecenter_eq_some firstMoving.owner secondMoving
      secondMovingFound
  have recenteredTwiceEq :
      recentered (recentered owner) = secondMoving.owner := by
    rw [firstRecenteredEq]
    exact secondRecenteredEq
  have secondMovingBoxEq :
      secondMoving.ownerBox = data.afterCell.box.toBox := by
    have mapped : Option.map (fun reset => reset.ownerBox)
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
          firstMoving.owner) = some data.afterCell.box.toBox := by
      rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
        firstMoving.owner data.intermediate.box.toBox intermediateProper
          (firstMoving.ownerInitialBox.trans firstMovingBoxEq),
        secondResetBoxProjection firstMoving.owner.parameterNonzero
          intermediateProper]
    rw [secondMovingFound] at mapped
    exact Option.some.inj mapped
  have finalSourceParameter :
      polynomial.eval (segment.pointAt left.parameter) =
        (data.final.sourceParameter 0).toGaussian :=
    certificate.sourceParameter.trans data.sourceParameter_eq_final
  have finalDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [finalSourceParameter, ← data.finalBox_eq_after]
    exact data.final.directBoundaryBounds 0
  have secondMovingDirectBounds :
      DirectBoundaryBounds
        (polynomial.eval (segment.pointAt left.parameter)) secondMoving.ownerBox
          data.final.directLower.toRational
            data.final.directUpper.toRational := by
    rw [secondMovingBoxEq]
    exact finalDirectBounds
  have secondMovingClearanceLower : data.final.directLower.toRational ≤
      secondMoving.owner.track.initial.clearance.bound := by
    rw [secondMoving.ownerDirectClearanceBound]
    exact secondMovingDirectBounds.lower_le
  have selectedSmall :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        secondMoving.owner.track.initial.clearance.bound := by
    rw [certificate.variation]
    exact data.variation_lt_finalLower.trans_le secondMovingClearanceLower
  have secondReady : AlreadyPrepared segment left
      (recentered (recentered owner)) request := by
    rw [recenteredTwiceEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [secondMoving.ownerInitialBox, secondMovingBoxEq]
      exact certificate.afterBoxSmall
    · exact certificate.predictedLeAfterFloor.trans
        (data.transportFloor_le_finalLower.trans secondMovingClearanceLower)
    · rw [secondMoving.ownerInitialBox, secondMovingBoxEq]
      exact certificate.afterBoxRefines
  have secondCarries :
      Riemann.Branches.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (recentered (recentered owner)).track.initial.clearance.bound := by
    rw [recenteredTwiceEq]
    exact selectedSmall
  have preparedEqRecenteredTwice :
      prepared segment left owner request = recentered (recentered owner) :=
    prepared_eq_recentered_twice_of_ready segment left owner request ready
      notCarries strengthenedNotCarries firstReady firstNotCarries
        firstStrengthenedNotCarries secondReady secondCarries
  have preparedEqMoving :
      prepared segment left owner request = secondMoving.owner :=
    preparedEqRecenteredTwice.trans recenteredTwiceEq
  have sourceNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter)) ≤ (256 : Fraction.Rational) := by
    rw [certificate.sourceParameter]
    exact (data.source.sourceNormSq_le 0).trans
      data.sourceNormSqUpper_le_twoHundredFiftySix
  have secondMovingBudget :
      QuadraticAmbientBudget
        secondMoving.owner := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box_all
      secondMoving.owner data.afterCell.box.toBox
    · exact secondMoving.ownerInitialBox.trans secondMovingBoxEq
    · exact secondMoving.ownerAmbientBox.trans secondMovingBoxEq
    · exact sourceNormSqLe
    · have bound := data.final.leftXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.rightXSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalXSqUpper_le_sixteen
    · have bound := data.final.bottomYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
    · have bound := data.final.topYSq_le
      rw [data.finalBox_eq_after] at bound
      exact bound.trans data.finalYSqUpper_le_sixteen
  have secondMovingAmbientLeftLe :
      secondMoving.owner.track.initial.ambientLeftClearance.bound ≤
        data.afterUpper.toRational := by
    rw [secondMoving.ownerAmbientLeftClearanceBound]
    exact secondMovingDirectBounds.le_upper.trans
      data.finalUpper_le_afterUpper
  have secondMovingResidual : data.source.residualMarginFloor.toRational ≤
      secondMoving.owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) := by
    apply data.resetResidual_le_finalLower_sub_displacement.trans
    apply Fraction.Order.Arithmetic.sub_le_sub_direct secondMovingClearanceLower
    rw [certificate.sourceParameter, certificate.targetParameter]
    exact data.source.displacement_le 0
  have targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤
          (256 : Fraction.Rational) := by
    rw [certificate.targetParameter]
    exact (data.source.targetNormSq_le 0).trans
      data.targetNormSqUpper_le_twoHundredFiftySix
  have finalBoxSideBounds :
      QuadraticBoxSideMajorantBounds
        (polynomial.eval (segment.pointAt left.parameter))
          data.afterCell.box.toBox data.final.sideMajorantUpper.toRational := by
    have bounds := data.final.quadraticBoxSideMajorantBounds 0
      data.final.sideMajorantUpper.toRational data.one_le_finalSideMajorant
        le_rfl
    rw [← finalSourceParameter, data.finalBox_eq_after] at bounds
    exact bounds
  have secondMovingSideBounds :
      QuadraticAmbientSideMajorantBounds
        secondMoving.owner data.final.sideMajorantUpper.toRational := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box
      secondMoving.owner data.afterCell.box.toBox
        data.final.sideMajorantUpper.toRational
    · exact secondMoving.ownerInitialBox.trans secondMovingBoxEq
    · rw [secondMoving.ownerAmbientBox, secondMovingBoxEq]
      exact Box.refines_refl _
    · exact finalBoxSideBounds
  exact Examples.Riemann.PreparedEightStepSameBox.retainedParametricResetStepOfPreparedOwner segment within left owner
    request data.afterCell.box.toBox data.afterUpper.toRational
      data.afterCell.transportMargin.toRational
        data.source.residualMarginFloor.toRational
          data.final.sideMajorantUpper.toRational secondMoving.owner
            preparedEqMoving selectedSmall
              (secondMoving.ownerInitialBox.trans secondMovingBoxEq)
              (secondMoving.ownerAmbientBox.trans secondMovingBoxEq)
              secondMoving.ownerDominance secondMovingBudget
              secondMovingAmbientLeftLe data.after_contracts certificate.different
              certificate.predictedLeAfterFloor data.resetResidual_positive
              secondMovingResidual secondMovingSideBounds
              data.retainedFloorTradeoff_sound targetNormSqLe

end GeneratedParametricDoubleResetCellCertificate

end Purelib.RootIsolation.SquareRoot.Replay.Reset.Generated

end
