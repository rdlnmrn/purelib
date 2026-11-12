module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Clearance
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! A finite request tree for restoring the original moving reset. Each
winding reply carries its canonical equation; the completed value retains the
original owner and bridge, including the original refiner. -/

namespace Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

set_option genInjectivity false in
/-- At most `budget` winding computations remain. This finite tree exposes
only queries reached in the original left-first branch order. -/
inductive QueryPlan (Query : Type) (Reply : Query → Type) (Result : Type) : Nat → Type where
  /-- Finish the plan with the retained result and no further query. -/ | done {budget : Nat} (value : Result) :
    MovingRecenterReplay.QueryPlan Query Reply Result budget
  /-- Issue the retained query and continue on its actual reply with one less query available. -/ | query {budget : Nat}
    (request : Query)
      (next : Reply request → MovingRecenterReplay.QueryPlan Query Reply Result
        budget) :
      MovingRecenterReplay.QueryPlan Query Reply Result (budget + 1)

constructive_injectivity QueryPlan

/-- Map the terminal result of a bounded query plan while preserving every query and reply-dependent branch. -/
def QueryPlan.map {Query : Type} {Reply : Query → Type} {Result Target : Type}
    {budget : Nat} (f : Result → Target) :
    QueryPlan Query Reply Result budget →
      QueryPlan Query Reply Target budget
  | .done value => .done (f value)
  | .query request next => .query request (fun reply => (next reply).map f)

/-- A finite winding-query plan whose retained replies carry their exact box-winding values. -/
abbrev Plan (polynomial : GaussianPolynomial)
  (Result : Type) (budget : Nat) :=
  QueryPlan
    Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box (fun box =>
    {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding polynomial box}) Result budget

/-- Every queried reply on the executed plan branch equals the canonical winding computation. -/
abbrev Checked {Result : Type} (specification : Result) :=
  {value : Result // value = specification}

/-- Canonical finite interpretation of a winding query tree. -/
def Plan.run {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {Result : Type} {budget : Nat} : Plan polynomial Result budget → Result
  | .done value => value
  | .query box next => Plan.run (next
    ⟨Winding.Box.Basic.quadrupledBoxWinding polynomial box, rfl⟩)

/-- Decorate a replay plan with equality to its original finite interpretation.
The supplied reply is used for every executable branch; the canonical winding
appears only in erased source equations. -/
def Plan.checked {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {Result : Type} {budget : Nat} (plan : Plan polynomial Result budget) :
    Plan polynomial (Checked
      (Plan.run plan)) budget :=
  match plan with
  | .done value => .done ⟨value, rfl⟩
  | .query box next => .query box fun reply =>
      (Plan.checked (next reply)).map fun result =>
        ⟨result.val, by
          have same : reply = ⟨Winding.Box.Basic.quadrupledBoxWinding polynomial box, rfl⟩ :=
            Subtype.ext reply.property
          cases same
          exact result.property⟩

/-- Construct the direct quadratic owner through at most one retained winding query.

The original four-side resultant checks precede the query; its actual checked reply determines whether the same box
yields a certified owner. -/
def direct {budget : Nat} (parameter :
  Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) (proper : box.Proper) :
    Plan (rootPolynomial
      parameter)
      (Checked
        (directOwnerOnBox? parameter parameterNonzero box proper))
        (budget + 1) := by
  if leftNonzero : Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
    if rightNonzero : Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
      if bottomNonzero : Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0
        then
        if topNonzero : Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0
          then
          exact .query box fun winding => by
            if windingFour : winding.val = 4 then
              have canonicalFour : Winding.Box.Basic.quadrupledBoxWinding
                (rootPolynomial parameter) box = 4 :=
                winding.property.symm.trans windingFour
              let restored : DirectBoxOwner parameter box :=
                DirectBoxOwner.mk
                  (directOwnerOfBox parameter parameterNonzero box
                    proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  rfl
                  (directOwnerOfBox_initial_box parameter
                    parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  (directOwnerOfBox_ambient parameter parameterNonzero
                    box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  (directOwnerOfBox_ambientClearanceDominance
                    parameter parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  leftNonzero rightNonzero bottomNonzero topNonzero
                  (directOwnerOfBox_initial_clearance_bound parameter
                    parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  rfl
              exact .done ⟨some restored, by
                unfold directOwnerOnBox?
                rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_pos topNonzero, dif_pos
                  canonicalFour]⟩
            else
              have canonicalMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                (rootPolynomial parameter) box = 4 := by
                rw [← winding.property]
                exact windingFour
              exact .done ⟨none, by
                unfold directOwnerOnBox?
                rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_pos topNonzero, dif_neg
                  canonicalMiss]⟩
        else
          exact .done ⟨none, by
            unfold directOwnerOnBox?
            rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_neg topNonzero]⟩
      else
        exact .done ⟨none, by
          unfold directOwnerOnBox?
          rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_neg bottomNonzero]⟩
    else
      exact .done ⟨none, by
        unfold directOwnerOnBox?
        rw [dif_pos leftNonzero, dif_neg rightNonzero]⟩
  else
    exact .done ⟨none, by
      unfold directOwnerOnBox?
      rw [dif_neg leftNonzero]⟩

/-- Restore the chosen replacement without rerunning its winding calculation.
Failure of this candidate ends the original reset; it does not try another child. -/
def candidate {budget : Nat} {parameter :
  Gaussian} (source :
  Owner parameter)
    (child : Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) (childRefines : child.Refines
      source.track.initial.box)
    (bridgeOwner : Owner parameter) (bridgeBox :
      bridgeOwner.track.initial.box = child) :
    Plan (rootPolynomial
      parameter)
      (Checked
        (movingCandidate? source child childRefines bridgeOwner
        bridgeBox)) (budget + 1) := open Purelib.Data.Rat in by
  let sourceBox := source.track.initial.box
  let radius := sourceBox.widthX / 2
  have radiusPositive : 0 < radius :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct source.track.initial.proper.1) (by decide)
  let replacement := Box.Square.Centered.Affine.centeredSquare
    (gentleCenter sourceBox child) radius radiusPositive.le
  if childStrict : child.StrictInterior replacement then
    exact (direct parameter source.parameterNonzero replacement
      (Box.Square.Centered.centeredSquare_proper
        (gentleCenter sourceBox child) radiusPositive)).map fun
          restored => by
      rcases restored with ⟨restored, equal⟩
      cases restored with
      | none =>
          refine ⟨none, ?_⟩
          unfold movingCandidate?
          unfold movingCandidateData?
          rw [dif_pos childStrict, ← equal]
      | some moved =>
          let reset : MovingRecenter parameter source :=
            { owner := (DirectBoxOwner.owner moved)
              deferred := (DirectBoxOwner.deferred moved)
              ownerBox := replacement
              ownerInitialBox := (DirectBoxOwner.initialBox moved)
              ownerAmbientBox := (DirectBoxOwner.ambientBox moved)
              ownerDominance := (DirectBoxOwner.dominance moved)
              bridgeOwner := bridgeOwner
              bridgeRefinesSource := by
                rw [bridgeBox]
                exact childRefines
              bridgeStrictOwner := by
                rw [bridgeBox, (DirectBoxOwner.initialBox moved)]
                exact childStrict
              ownerLeftNonzero := (DirectBoxOwner.leftNonzero moved)
              ownerRightNonzero := (DirectBoxOwner.rightNonzero moved)
              ownerBottomNonzero := (DirectBoxOwner.bottomNonzero
                moved)
              ownerTopNonzero := (DirectBoxOwner.topNonzero moved)
              ownerDirectClearanceBound :=
                (DirectBoxOwner.initialClearanceBound moved)
              ownerAmbientLeftClearanceBound :=
                (DirectBoxOwner.ambientLeftClearanceBound moved) }
          refine ⟨some reset, ?_⟩
          unfold movingCandidate?
          unfold movingCandidateData?
          rw [dif_pos childStrict, ← equal]
  else
    refine .done ⟨none, ?_⟩
    unfold movingCandidate?
    unfold movingCandidateData?
    rw [dif_neg childStrict]

/-- The original reset needs at most four child queries and one replacement
query. Its bridge owner is constructed from the original source state. -/
def moving {parameter : Gaussian} (source :
  Owner parameter) :
    Plan (rootPolynomial
      parameter) (Checked
      (movingRecenter? source)) 5 := by
  let box := source.track.initial.box
  let proper := source.track.initial.proper
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero : Clearance.QuadraticAxisElimination.verticalDeterminant parameter xCut ≠ 0 then
    if yNonzero : Clearance.QuadraticAxisElimination.horizontalDeterminant parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      exact .query grid.lowerLeft fun reply0 => by
        if lowerLeft : reply0.val = 4 then
          have lowerLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
            (rootPolynomial parameter) grid.lowerLeft = 4 :=
            reply0.property.symm.trans lowerLeft
          let childClearances :=
            grid.childClearances source.track.initial.clearance
          let bridgeState := childState source grid.lowerLeft
            grid.lowerLeft_refines
            ⟨(midpoint_strict proper.1).1,
              (midpoint_strict proper.2).1⟩
            childClearances.1 lowerLeftWinding
            (Lines.leftOfBoundary source.track.initial.clearance)
            grid.verticalClearance
            (Lines.bottomOfBoundary source.track.initial.clearance)
            grid.horizontalClearance
          let bridgeOwner := ownerOfState source.parameterNonzero
            bridgeState
          exact (candidate source grid.lowerLeft grid.lowerLeft_refines
            bridgeOwner rfl).map fun restored =>
            ⟨restored.val, by
              unfold movingRecenter?
              dsimp only
              rw [dif_pos xNonzero, dif_pos yNonzero, dif_pos lowerLeftWinding]
              exact restored.property⟩
        else
          have lowerLeftMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
            (rootPolynomial parameter) grid.lowerLeft = 4 := by
            rw [← reply0.property]
            exact lowerLeft
          exact .query grid.upperLeft fun reply1 => by
            if upperLeft : reply1.val = 4 then
              have upperLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
                (rootPolynomial parameter) grid.upperLeft = 4 :=
                reply1.property.symm.trans upperLeft
              let childClearances :=
                grid.childClearances source.track.initial.clearance
              let bridgeState := childState source grid.upperLeft
                grid.upperLeft_refines
                ⟨(midpoint_strict proper.1).1,
                  (midpoint_strict proper.2).2⟩
                childClearances.2.1 upperLeftWinding
                (Lines.leftOfBoundary source.track.initial.clearance)
                grid.verticalClearance grid.horizontalClearance
                (Lines.topOfBoundary source.track.initial.clearance)
              let bridgeOwner := ownerOfState source.parameterNonzero
                bridgeState
              exact (candidate source grid.upperLeft grid.upperLeft_refines
                bridgeOwner rfl).map fun restored =>
                ⟨restored.val, by
                  unfold movingRecenter?
                  dsimp only
                  rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_pos upperLeftWinding]
                  exact restored.property⟩
            else
              have upperLeftMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                (rootPolynomial parameter) grid.upperLeft = 4 := by
                rw [← reply1.property]
                exact upperLeft
              exact .query grid.lowerRight fun reply2 => by
                if lowerRight : reply2.val = 4 then
                  have lowerRightWinding : Winding.Box.Basic.quadrupledBoxWinding
                    (rootPolynomial parameter) grid.lowerRight = 4 :=
                    reply2.property.symm.trans lowerRight
                  let childClearances :=
                    grid.childClearances source.track.initial.clearance
                  let bridgeState := childState source grid.lowerRight
                    grid.lowerRight_refines
                    ⟨(midpoint_strict proper.1).2,
                      (midpoint_strict proper.2).1⟩
                    childClearances.2.2.1 lowerRightWinding grid.verticalClearance
                    (Lines.rightOfBoundary source.track.initial.clearance)
                    (Lines.bottomOfBoundary source.track.initial.clearance)
                    grid.horizontalClearance
                  let bridgeOwner := ownerOfState
                    source.parameterNonzero bridgeState
                  exact (candidate source grid.lowerRight grid.lowerRight_refines
                    bridgeOwner rfl).map fun restored =>
                    ⟨restored.val, by
                      unfold movingRecenter?
                      dsimp only
                      rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_pos
                        lowerRightWinding]
                      exact restored.property⟩
                else
                  have lowerRightMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                    (rootPolynomial parameter) grid.lowerRight = 4 :=
                    by
                    rw [← reply2.property]
                    exact lowerRight
                  exact .query grid.upperRight fun reply3 => by
                    if upperRight : reply3.val = 4 then
                      have upperRightWinding : Winding.Box.Basic.quadrupledBoxWinding
                        (rootPolynomial parameter) grid.upperRight = 4
                        :=
                        reply3.property.symm.trans upperRight
                      let childClearances :=
                        grid.childClearances source.track.initial.clearance
                      let bridgeState := childState source
                        grid.upperRight
                        grid.upperRight_refines
                        ⟨(midpoint_strict proper.1).2,
                          (midpoint_strict proper.2).2⟩
                        childClearances.2.2.2 upperRightWinding grid.verticalClearance
                        (Lines.rightOfBoundary source.track.initial.clearance)
                        grid.horizontalClearance
                        (Lines.topOfBoundary source.track.initial.clearance)
                      let bridgeOwner := ownerOfState
                        source.parameterNonzero bridgeState
                      exact (candidate source grid.upperRight
                        grid.upperRight_refines bridgeOwner rfl).map fun restored =>
                        ⟨restored.val, by
                          unfold movingRecenter?
                          dsimp only
                          rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_neg
                            lowerRightMiss, dif_pos upperRightWinding]
                          exact restored.property⟩
                    else
                      have upperRightMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                        (rootPolynomial parameter) grid.upperRight = 4
                        := by
                        rw [← reply3.property]
                        exact upperRight
                      exact .done ⟨none, by
                        unfold movingRecenter?
                        dsimp only
                        rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_neg
                          lowerRightMiss, dif_neg upperRightMiss]⟩
    else
      exact .done ⟨none, by unfold movingRecenter?; dsimp only; rw
        [dif_pos xNonzero, dif_neg yNonzero]⟩
  else
    exact .done ⟨none, by unfold movingRecenter?; dsimp only; rw
      [dif_neg xNonzero]⟩

end Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
