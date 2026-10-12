module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic.Eight
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Examples.Riemann.PreparedEightStepSameBox
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.SquareRoot.Replay.Eight.Configuration
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-! # Cached eight-step preparation with a reset at edge three -/

namespace Purelib.RootIsolation.SquareRoot.Replay.Eight.ResetAtThree

open Purelib.Riemann.Branches.PreparedSheetContinuation
  (ParametricSameBoxState ParametricSameBoxStep CachedSource Subdivision)
open Purelib.Examples.Riemann.PreparedEightStepSameBox
  (ParametricResetStep EightStepSameBoxResult eightStepNextCached_terminalOwner_heq)

/-- The original canonical Gaussian-rational coordinate type. -/
private abbrev Gaussian := Canonical
/-- The original rational box type. -/
private abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner type. -/
private abbrev Owner :=
  Riemann.Topology.SquareRootContinuationChain.Owner

/-- Thread a three-edge same-box prefix, one generated reset at edge three,
and a four-edge same-box suffix. -/
def eightStepResetAtThree
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval
        (segment.pointAt (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0).parameter)))
    (oldBox newBox : Purelib.Geometry.Rational.Box)
    (beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor :
      Fraction.Rational)
    (initialState : ParametricSameBoxState segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0)
      ownerZero oldBox beforeUpper marginFloor)
    (beforeContracts : beforeUpper ^ 2 / 4 ≤ beforeUpper)
    (afterContracts : afterUpper ^ 2 / 4 ≤ afterUpper)
    (ordered : ∀ edge : Fin 8,
      (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
        edge)).parameter ≤
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge).endpoint.parameter)
    (beforeStep : ∀ (edge : Fin 8)
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt
            (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner oldBox
            beforeUpper marginFloor -> edge.val < 3 ->
        ParametricSameBoxStep segment within
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner
            (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge) oldBox beforeDirectLower beforeUpper
              marginFloor)
    (resetStep : ∀
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3).parameter))),
      ParametricSameBoxState segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) owner oldBox
          beforeUpper marginFloor ->
      owner.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 ->
        ParametricResetStep segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) owner
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3) newBox afterUpper marginFloor)
    (afterStep : ∀ (edge : Fin 8)
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt
            (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner newBox
            afterUpper marginFloor -> 4 ≤ edge.val ->
        ParametricSameBoxStep segment within
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner
            (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge) newBox afterDirectLower afterUpper
              marginFloor) :
    EightStepSameBoxResult segment within ownerZero newBox afterUpper
      marginFloor := by
  let stepZero := beforeStep 0 ownerZero initialState (by decide)
  let ownerOne := stepZero.nextOwner
  let stateOne := stepZero.nextState initialState beforeContracts
  let stepOne := beforeStep 1 ownerOne stateOne (by decide)
  let ownerTwo := stepOne.nextOwner
  let stateTwo := stepOne.nextState stateOne beforeContracts
  let stepTwo := beforeStep 2 ownerTwo stateTwo (by decide)
  let ownerThree := stepTwo.nextOwner
  let stateThree := stepTwo.nextState stateTwo beforeContracts
  have ownerThreeClearanceLe :
      ownerThree.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 := by
    apply stepTwo.advanceCache.clearanceQuarterSq.trans
    change
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest
            2)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Fraction.Rational)⁻¹ ≤
        beforeUpper ^ 2 * (4 : Fraction.Rational)⁻¹
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    · exact Fraction.Order.Arithmetic.pow_le_pow_direct
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest
            2)).preparedOwner.track.initial.ambientLeftClearance.positive.le
            stepTwo.preparedAmbientLeftLe 2
    · exact (Fraction.Order.Field.inv_pos_direct
        (by decide : (0 : Fraction.Rational) < 4)).le
  let resetThree := resetStep ownerThree stateThree ownerThreeClearanceLe
  let ownerFour := resetThree.nextOwner
  let stateFour := resetThree.nextState
  let stepFour := afterStep 4 ownerFour stateFour (by decide)
  let ownerFive := stepFour.nextOwner
  let stateFive := stepFour.nextState stateFour afterContracts
  let stepFive := afterStep 5 ownerFive stateFive (by decide)
  let ownerSix := stepFive.nextOwner
  let stateSix := stepFive.nextState stateFive afterContracts
  let stepSix := afterStep 6 ownerSix stateSix (by decide)
  let ownerSeven := stepSix.nextOwner
  let stateSeven := stepSix.nextState stateSix afterContracts
  let stepSeven := afterStep 7 ownerSeven stateSeven (by decide)
  let ownerEight := stepSeven.nextOwner
  let stateEight := stepSeven.nextState stateSeven afterContracts
  let tailEight : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 8)
      ownerEight := .stop _ _
  let tailSeven : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7)
      ownerSeven :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7) ownerSeven
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 7)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7) ownerSeven
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 7)) (ordered 7) stepSeven.canonicalSmall
            stepSeven.canonicalSmall tailEight
  let tailSix : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 6) ownerSix :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 6) ownerSix
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 6)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 6) ownerSix
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 6)) (ordered 6) stepSix.canonicalSmall
            stepSix.canonicalSmall tailSeven
  let tailFive : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 5) ownerFive :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 5) ownerFive
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 5)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 5) ownerFive
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 5)) (ordered 5) stepFive.canonicalSmall
            stepFive.canonicalSmall tailSix
  let tailFour : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 4) ownerFour :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 4) ownerFour
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 4)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 4) ownerFour
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 4)) (ordered 4) stepFour.canonicalSmall
            stepFour.canonicalSmall tailFive
  let tailThree : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3)
      ownerThree :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) ownerThree
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) ownerThree
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3)) (ordered 3) resetThree.canonicalSmall
            resetThree.canonicalSmall tailFour
  let tailTwo : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 2)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 2)) (ordered 2) stepTwo.canonicalSmall
            stepTwo.canonicalSmall tailThree
  let tailOne : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 1) ownerOne :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 1) ownerOne
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 1)
        (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 1) ownerOne
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 1)) (ordered 1) stepOne.canonicalSmall
            stepOne.canonicalSmall tailTwo
  let subdivision : Subdivision segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0)
      ownerZero :=
    Subdivision.nextCached segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0) ownerZero
      (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 0)
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0) ownerZero
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 0)) (ordered 0) stepZero.canonicalSmall
            stepZero.canonicalSmall tailOne
  have preparedBoxZero :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0) ownerZero
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 0)).preparedOwner.track.initial.box = oldBox :=
    stepZero.advanceCache.initialBox.symm.trans stepZero.nextOwnerBox
  have preparedBoxOne :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 1) ownerOne
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 1)).preparedOwner.track.initial.box = oldBox :=
    stepOne.advanceCache.initialBox.symm.trans stepOne.nextOwnerBox
  have preparedBoxTwo :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2) ownerTwo
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 2)).preparedOwner.track.initial.box = oldBox :=
    stepTwo.advanceCache.initialBox.symm.trans stepTwo.nextOwnerBox
  have preparedBoxThree :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) ownerThree
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3)).preparedOwner.track.initial.box = newBox :=
    resetThree.preparedBox
  have preparedBoxFour :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 4) ownerFour
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 4)).preparedOwner.track.initial.box = newBox :=
    stepFour.advanceCache.initialBox.symm.trans stepFour.nextOwnerBox
  have preparedBoxFive :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 5) ownerFive
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 5)).preparedOwner.track.initial.box = newBox :=
    stepFive.advanceCache.initialBox.symm.trans stepFive.nextOwnerBox
  have preparedBoxSix :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 6) ownerSix
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 6)).preparedOwner.track.initial.box = newBox :=
    stepSix.advanceCache.initialBox.symm.trans stepSix.nextOwnerBox
  have preparedBoxSeven :
      (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7) ownerSeven
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 7)).preparedOwner.track.initial.box = newBox :=
    stepSeven.advanceCache.initialBox.symm.trans stepSeven.nextOwnerBox
  have tailEightPreparedBoxes : tailEight.preparedBoxes = [] := by
    rfl
  have tailSevenPreparedBoxes : tailSeven.preparedBoxes = [newBox] := by
    simp only [tailSeven, Subdivision.nextCached_preparedBoxes,
      preparedBoxSeven]
    exact congrArg (fun boxes => newBox :: boxes) tailEightPreparedBoxes
  have tailSixPreparedBoxes : tailSix.preparedBoxes = [newBox, newBox] := by
    simp only [tailSix, Subdivision.nextCached_preparedBoxes,
      preparedBoxSix]
    exact congrArg (fun boxes => newBox :: boxes) tailSevenPreparedBoxes
  have tailFivePreparedBoxes : tailFive.preparedBoxes =
      [newBox, newBox, newBox] := by
    simp only [tailFive, Subdivision.nextCached_preparedBoxes,
      preparedBoxFive]
    exact congrArg (fun boxes => newBox :: boxes) tailSixPreparedBoxes
  have tailFourPreparedBoxes : tailFour.preparedBoxes =
      [newBox, newBox, newBox, newBox] := by
    simp only [tailFour, Subdivision.nextCached_preparedBoxes,
      preparedBoxFour]
    exact congrArg (fun boxes => newBox :: boxes) tailFivePreparedBoxes
  have tailThreePreparedBoxes : tailThree.preparedBoxes =
      [newBox, newBox, newBox, newBox, newBox] := by
    simp only [tailThree, Subdivision.nextCached_preparedBoxes,
      preparedBoxThree]
    exact congrArg (fun boxes => newBox :: boxes) tailFourPreparedBoxes
  have tailTwoPreparedBoxes : tailTwo.preparedBoxes =
      [oldBox, newBox, newBox, newBox, newBox, newBox] := by
    simp only [tailTwo, Subdivision.nextCached_preparedBoxes,
      preparedBoxTwo]
    exact congrArg (fun boxes => oldBox :: boxes) tailThreePreparedBoxes
  have tailOnePreparedBoxes : tailOne.preparedBoxes =
      [oldBox, oldBox, newBox, newBox, newBox, newBox, newBox] := by
    simp only [tailOne, Subdivision.nextCached_preparedBoxes,
      preparedBoxOne]
    exact congrArg (fun boxes => oldBox :: boxes) tailTwoPreparedBoxes
  have subdivisionPreparedBoxes : subdivision.preparedBoxes =
      [oldBox, oldBox, oldBox, newBox, newBox, newBox, newBox, newBox] := by
    simp only [subdivision, Subdivision.nextCached_preparedBoxes,
      preparedBoxZero]
    exact congrArg (fun boxes => oldBox :: boxes) tailOnePreparedBoxes
  exact
    { ownerEight := ownerEight
      terminalState := stateEight
      terminalAmbientLeftLeQuarter := stepSeven.nextAmbientLeftLeQuarter
      terminalClearanceLeQuarter := by
        apply stepSeven.advanceCache.clearanceQuarterSq.trans
        change
          (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7) ownerSeven
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
              (4 : Fraction.Rational)⁻¹ ≤
            afterUpper ^ 2 * (4 : Fraction.Rational)⁻¹
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact Fraction.Order.Arithmetic.pow_le_pow_direct
            (CachedSource.canonical segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7) ownerSeven
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest
                7)).preparedOwner.track.initial.ambientLeftClearance.positive.le
                stepSeven.preparedAmbientLeftLe 2
        · exact (Fraction.Order.Field.inv_pos_direct
            (by decide : (0 : Fraction.Rational) < 4)).le
      preparedBox := fun edge => if edge.val < 3 then oldBox else newBox
      subdivision := subdivision
      preparedBoxes_eq := by
        change subdivision.preparedBoxes =
          [oldBox, oldBox, oldBox, newBox,
            newBox, newBox, newBox, newBox]
        exact subdivisionPreparedBoxes
      terminalOwner_heq := by
        change HEq subdivision.terminalOwner ownerEight
        exact
          (eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
            ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
              ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                  ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                    ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                      ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                        ((eightStepNextCached_terminalOwner_heq _ _ _ _ _ _ _ _ _ _).trans
                          (by rfl))))))))
      endpoint_eq := by
        simp only [subdivision, tailOne,
          Subdivision.nextCached_endpoint]
        rfl
      requests_eq := by
        simp only [subdivision, tailOne]
        change [SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 0,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 1,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 2,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 4,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 5,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 6,
            SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 7] = _
        exact SquareRoot.Subdivision.Dyadic.Eight.ExplicitQuarticPreparedSecondCellCertificate.secondDyadicRequests.symm
      parameterEdges_eq := by
        simp only [subdivision, tailOne,
          Subdivision.nextCached_parameterEdges]
        change
          [{ left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 0).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 1,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 1).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 2,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 2).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 4,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 4).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 5,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 5).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 6,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 6).endpoint },
            { left := SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 7,
              right := (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 7).endpoint }] =
            Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicEdges 3
              Riemann.Paths.PreparedClearPathModels.zeroEndpoint
                Riemann.Paths.PreparedClearPathModels.oneEndpoint
        with_unfolding_all rfl }

/-- The edge-three reset constructor records the inherited box on edges zero
through two and the reset box on edges three through seven. -/
theorem eightStepResetAtThree_preparedBox
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient
      start finish)
    (within : segment.WithinAmbient)
    (ownerZero : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval
        (segment.pointAt (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0).parameter)))
    (oldBox newBox : Purelib.Geometry.Rational.Box)
    (beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor :
      Fraction.Rational)
    (initialState : ParametricSameBoxState segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 0)
      ownerZero oldBox beforeUpper marginFloor)
    (beforeContracts : beforeUpper ^ 2 / 4 ≤ beforeUpper)
    (afterContracts : afterUpper ^ 2 / 4 ≤ afterUpper)
    (ordered : ∀ edge : Fin 8,
      (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
        edge)).parameter ≤
        (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge).endpoint.parameter)
    (beforeStep : ∀ (edge : Fin 8)
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt
            (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner oldBox
            beforeUpper marginFloor -> edge.val < 3 ->
        ParametricSameBoxStep segment within
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner
            (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge) oldBox beforeDirectLower beforeUpper
              marginFloor)
    (resetStep : ∀
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3).parameter))),
      ParametricSameBoxState segment (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) owner oldBox
          beforeUpper marginFloor ->
      owner.track.initial.clearance.bound ≤ beforeUpper ^ 2 / 4 ->
        ParametricResetStep segment within (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint 3) owner
          (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest 3) newBox afterUpper marginFloor)
    (afterStep : ∀ (edge : Fin 8)
      (owner : Riemann.Topology.SquareRootContinuationChain.Owner
        (polynomial.eval
          (segment.pointAt
            (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
              (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter))),
      ParametricSameBoxState segment
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner newBox
            afterUpper marginFloor -> 4 ≤ edge.val ->
        ParametricSameBoxStep segment within
          (SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource
            edge)) owner
            (SquareRoot.Subdivision.Dyadic.Eight.secondEdgeRequest edge) newBox afterDirectLower afterUpper
              marginFloor)
    (edge : Fin 8) :
    (eightStepResetAtThree segment within ownerZero oldBox newBox
      beforeDirectLower afterDirectLower beforeUpper afterUpper marginFloor
      initialState beforeContracts afterContracts ordered beforeStep resetStep
        afterStep).preparedBox edge =
      if edge.val < 3 then oldBox else newBox := by
  rfl

end Purelib.RootIsolation.SquareRoot.Replay.Eight.ResetAtThree

end
