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
    Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay.QueryPlan Query Reply Result budget
  /-- Issue the retained query and continue on its actual reply with one less query available. -/ | query {budget : Nat}
    (request : Query)
      (next : Reply request → Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay.QueryPlan Query Reply Result
        budget) :
      Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay.QueryPlan Query Reply Result (budget + 1)

constructive_injectivity QueryPlan

/-- Map the terminal result of a bounded query plan while preserving every query and reply-dependent branch. -/
def QueryPlan.map {Query : Type} {Reply : Query → Type} {Result Target : Type}
    {budget : Nat} (f : Result → Target) :
    SquareRoot.Replay.MovingRecenterReplay.QueryPlan Query Reply Result budget →
      SquareRoot.Replay.MovingRecenterReplay.QueryPlan Query Reply Target budget
  | .done value => .done (f value)
  | .query request next => .query request (fun reply => (next reply).map f)

/-- A finite winding-query plan whose retained replies carry their exact box-winding values. -/
abbrev Plan (polynomial : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.GaussianPolynomial)
  (Result : Type) (budget : Nat) :=
  SquareRoot.Replay.MovingRecenterReplay.QueryPlan
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box (fun box =>
    {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding polynomial box}) Result budget

/-- Every queried reply on the executed plan branch equals the canonical winding computation. -/
abbrev Checked {Result : Type} (specification : Result) :=
  {value : Result // value = specification}

/-- Canonical finite interpretation of a winding query tree. -/
def Plan.run {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {Result : Type} {budget : Nat} : SquareRoot.Replay.MovingRecenterReplay.Plan polynomial Result budget → Result
  | .done value => value
  | .query box next => Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay.Plan.run (next
    ⟨Winding.Box.Basic.quadrupledBoxWinding polynomial box, rfl⟩)

/-- Decorate a replay plan with equality to its original finite interpretation.
The supplied reply is used for every executable branch; the canonical winding
appears only in erased source equations. -/
def Plan.checked {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {Result : Type} {budget : Nat} (plan : SquareRoot.Replay.MovingRecenterReplay.Plan polynomial Result budget) :
    SquareRoot.Replay.MovingRecenterReplay.Plan polynomial (SquareRoot.Replay.MovingRecenterReplay.Checked
      (SquareRoot.Replay.MovingRecenterReplay.Plan.run plan)) budget :=
  match plan with
  | .done value => .done ⟨value, rfl⟩
  | .query box next => .query box fun reply =>
      (Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay.Plan.checked (next reply)).map fun result =>
        ⟨result.val, by
          have same : reply = ⟨Winding.Box.Basic.quadrupledBoxWinding polynomial box, rfl⟩ :=
            Subtype.ext reply.property
          cases same
          exact result.property⟩

/-- Construct the direct quadratic owner through at most one retained winding query.

The original four-side resultant checks precede the query; its actual checked reply determines whether the same box
yields a certified owner. -/
def direct {budget : Nat} (parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) (proper : box.Proper) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      parameter)
      (SquareRoot.Replay.MovingRecenterReplay.Checked
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox? parameter parameterNonzero box proper))
        (budget + 1) := by
  if leftNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
    if rightNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
      if bottomNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0
        then
        if topNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0
          then
          exact .query box fun winding => by
            if windingFour : winding.val = 4 then
              have canonicalFour : Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) box = 4 :=
                winding.property.symm.trans windingFour
              let restored : SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner parameter box :=
                SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.mk
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox parameter parameterNonzero box
                    proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  rfl
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox_initial_box parameter
                    parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox_ambient parameter parameterNonzero
                    box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox_ambientClearanceDominance
                    parameter parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  leftNonzero rightNonzero bottomNonzero topNonzero
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox_initial_clearance_bound parameter
                    parameterNonzero box proper
                    leftNonzero rightNonzero bottomNonzero topNonzero canonicalFour)
                  rfl
              exact .done ⟨some restored, by
                unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
                rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_pos topNonzero, dif_pos
                  canonicalFour]⟩
            else
              have canonicalMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) box = 4 := by
                rw [← winding.property]
                exact windingFour
              exact .done ⟨none, by
                unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
                rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_pos topNonzero, dif_neg
                  canonicalMiss]⟩
        else
          exact .done ⟨none, by
            unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
            rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_neg topNonzero]⟩
      else
        exact .done ⟨none, by
          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
          rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_neg bottomNonzero]⟩
    else
      exact .done ⟨none, by
        unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
        rw [dif_pos leftNonzero, dif_neg rightNonzero]⟩
  else
    exact .done ⟨none, by
      unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOnBox?
      rw [dif_neg leftNonzero]⟩

/-- Restore the chosen replacement without rerunning its winding calculation.
Failure of this candidate ends the original reset; it does not try another child. -/
def candidate {budget : Nat} {parameter :
  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian} (source :
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.Owner parameter)
    (child : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Box) (childRefines : child.Refines
      source.track.initial.box)
    (bridgeOwner : SquareRoot.Clearance.ExactQuadraticOwnerClearance.Owner parameter) (bridgeBox :
      bridgeOwner.track.initial.box = child) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      parameter)
      (SquareRoot.Replay.MovingRecenterReplay.Checked
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidate? source child childRefines bridgeOwner
        bridgeBox)) (budget + 1) := open Purelib.Data.Rat in by
  let sourceBox := source.track.initial.box
  let radius := sourceBox.widthX / 2
  have radiusPositive : 0 < radius :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct source.track.initial.proper.1) (by decide)
  let replacement := Box.Square.Centered.Affine.centeredSquare
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.gentleCenter sourceBox child) radius radiusPositive.le
  if childStrict : child.StrictInterior replacement then
    exact (SquareRoot.Replay.MovingRecenterReplay.direct parameter source.parameterNonzero replacement
      (Box.Square.Centered.centeredSquare_proper
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.gentleCenter sourceBox child) radiusPositive)).map fun
          restored => by
      rcases restored with ⟨restored, equal⟩
      cases restored with
      | none =>
          refine ⟨none, ?_⟩
          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidate?
          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidateData?
          rw [dif_pos childStrict, ← equal]
      | some moved =>
          let reset : SquareRoot.Clearance.ExactQuadraticOwnerClearance.MovingRecenter parameter source :=
            { owner := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.owner moved)
              deferred := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.deferred moved)
              ownerBox := replacement
              ownerInitialBox := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.initialBox moved)
              ownerAmbientBox := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.ambientBox moved)
              ownerDominance := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.dominance moved)
              bridgeOwner := bridgeOwner
              bridgeRefinesSource := by
                rw [bridgeBox]
                exact childRefines
              bridgeStrictOwner := by
                rw [bridgeBox, (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.initialBox moved)]
                exact childStrict
              ownerLeftNonzero := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.leftNonzero moved)
              ownerRightNonzero := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.rightNonzero moved)
              ownerBottomNonzero := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.bottomNonzero
                moved)
              ownerTopNonzero := (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.topNonzero moved)
              ownerDirectClearanceBound :=
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.initialClearanceBound moved)
              ownerAmbientLeftClearanceBound :=
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoxOwner.ambientLeftClearanceBound moved) }
          refine ⟨some reset, ?_⟩
          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidate?
          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidateData?
          rw [dif_pos childStrict, ← equal]
  else
    refine .done ⟨none, ?_⟩
    unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidate?
    unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidateData?
    rw [dif_neg childStrict]

/-- The original reset needs at most four child queries and one replacement
query. Its bridge owner is constructed from the original source state. -/
def moving {parameter : SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.Gaussian} (source :
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.Owner parameter) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      parameter) (SquareRoot.Replay.MovingRecenterReplay.Checked
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? source)) 5 := by
  let box := source.track.initial.box
  let proper := source.track.initial.proper
  let xCut := SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint box.xLower box.xUpper
  let yCut := SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint box.yLower box.yUpper
  if xNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant parameter xCut ≠ 0 then
    if yNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant parameter yCut ≠ 0 then
      let grid := SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpointGrid parameter box proper xNonzero yNonzero
      exact .query grid.lowerLeft fun reply0 => by
        if lowerLeft : reply0.val = 4 then
          have lowerLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.lowerLeft = 4 :=
            reply0.property.symm.trans lowerLeft
          let childClearances :=
            grid.childClearances source.track.initial.clearance
          let bridgeState := SquareRoot.Clearance.ExactQuadraticOwnerClearance.childState source grid.lowerLeft
            grid.lowerLeft_refines
            ⟨(SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.1).1,
              (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.2).1⟩
            childClearances.1 lowerLeftWinding
            (Clearance.Box.Boundary.Lines.leftOfBoundary source.track.initial.clearance)
            grid.verticalClearance
            (Clearance.Box.Boundary.Lines.bottomOfBoundary source.track.initial.clearance)
            grid.horizontalClearance
          let bridgeOwner := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState source.parameterNonzero
            bridgeState
          exact (SquareRoot.Replay.MovingRecenterReplay.candidate source grid.lowerLeft grid.lowerLeft_refines
            bridgeOwner rfl).map fun restored =>
            ⟨restored.val, by
              unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
              dsimp only
              rw [dif_pos xNonzero, dif_pos yNonzero, dif_pos lowerLeftWinding]
              exact restored.property⟩
        else
          have lowerLeftMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
            (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.lowerLeft = 4 := by
            rw [← reply0.property]
            exact lowerLeft
          exact .query grid.upperLeft fun reply1 => by
            if upperLeft : reply1.val = 4 then
              have upperLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.upperLeft = 4 :=
                reply1.property.symm.trans upperLeft
              let childClearances :=
                grid.childClearances source.track.initial.clearance
              let bridgeState := SquareRoot.Clearance.ExactQuadraticOwnerClearance.childState source grid.upperLeft
                grid.upperLeft_refines
                ⟨(SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.1).1,
                  (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.2).2⟩
                childClearances.2.1 upperLeftWinding
                (Clearance.Box.Boundary.Lines.leftOfBoundary source.track.initial.clearance)
                grid.verticalClearance grid.horizontalClearance
                (Clearance.Box.Boundary.Lines.topOfBoundary source.track.initial.clearance)
              let bridgeOwner := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState source.parameterNonzero
                bridgeState
              exact (SquareRoot.Replay.MovingRecenterReplay.candidate source grid.upperLeft grid.upperLeft_refines
                bridgeOwner rfl).map fun restored =>
                ⟨restored.val, by
                  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
                  dsimp only
                  rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_pos upperLeftWinding]
                  exact restored.property⟩
            else
              have upperLeftMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.upperLeft = 4 := by
                rw [← reply1.property]
                exact upperLeft
              exact .query grid.lowerRight fun reply2 => by
                if lowerRight : reply2.val = 4 then
                  have lowerRightWinding : Winding.Box.Basic.quadrupledBoxWinding
                    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.lowerRight = 4 :=
                    reply2.property.symm.trans lowerRight
                  let childClearances :=
                    grid.childClearances source.track.initial.clearance
                  let bridgeState := SquareRoot.Clearance.ExactQuadraticOwnerClearance.childState source grid.lowerRight
                    grid.lowerRight_refines
                    ⟨(SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.1).2,
                      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.2).1⟩
                    childClearances.2.2.1 lowerRightWinding grid.verticalClearance
                    (Clearance.Box.Boundary.Lines.rightOfBoundary source.track.initial.clearance)
                    (Clearance.Box.Boundary.Lines.bottomOfBoundary source.track.initial.clearance)
                    grid.horizontalClearance
                  let bridgeOwner := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState
                    source.parameterNonzero bridgeState
                  exact (SquareRoot.Replay.MovingRecenterReplay.candidate source grid.lowerRight grid.lowerRight_refines
                    bridgeOwner rfl).map fun restored =>
                    ⟨restored.val, by
                      unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
                      dsimp only
                      rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_pos
                        lowerRightWinding]
                      exact restored.property⟩
                else
                  have lowerRightMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.lowerRight = 4 :=
                    by
                    rw [← reply2.property]
                    exact lowerRight
                  exact .query grid.upperRight fun reply3 => by
                    if upperRight : reply3.val = 4 then
                      have upperRightWinding : Winding.Box.Basic.quadrupledBoxWinding
                        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.upperRight = 4
                        :=
                        reply3.property.symm.trans upperRight
                      let childClearances :=
                        grid.childClearances source.track.initial.clearance
                      let bridgeState := SquareRoot.Clearance.ExactQuadraticOwnerClearance.childState source
                        grid.upperRight
                        grid.upperRight_refines
                        ⟨(SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.1).2,
                          (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint_strict proper.2).2⟩
                        childClearances.2.2.2 upperRightWinding grid.verticalClearance
                        (Clearance.Box.Boundary.Lines.rightOfBoundary source.track.initial.clearance)
                        grid.horizontalClearance
                        (Clearance.Box.Boundary.Lines.topOfBoundary source.track.initial.clearance)
                      let bridgeOwner := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState
                        source.parameterNonzero bridgeState
                      exact (SquareRoot.Replay.MovingRecenterReplay.candidate source grid.upperRight
                        grid.upperRight_refines bridgeOwner rfl).map fun restored =>
                        ⟨restored.val, by
                          unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
                          dsimp only
                          rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_neg
                            lowerRightMiss, dif_pos upperRightWinding]
                          exact restored.property⟩
                    else
                      have upperRightMiss : ¬ Winding.Box.Basic.quadrupledBoxWinding
                        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter) grid.upperRight = 4
                        := by
                        rw [← reply3.property]
                        exact upperRight
                      exact .done ⟨none, by
                        unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?
                        dsimp only
                        rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftMiss, dif_neg upperLeftMiss, dif_neg
                          lowerRightMiss, dif_neg upperRightMiss]⟩
    else
      exact .done ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?; dsimp only; rw
        [dif_pos xNonzero, dif_neg yNonzero]⟩
  else
    exact .done ⟨none, by unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter?; dsimp only; rw
      [dif_neg xNonzero]⟩

end Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
