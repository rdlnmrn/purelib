module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Accelerated
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Newton.Search.Attempt.Replay

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
import Purelib.Riemann.Transport.PreparedCenterReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.State.WindingOne.Raw

open Purelib.Riemann.Topology

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Exact quadratic samples through checked fast refinements

The accelerated and deferred quadratic owner constructors share their first
bounded Newton attempt.  Its successful output identifies the canonical
next state, even when only the incoming box has been restored.
An unsuccessful attempt does not certify failure of the total root track.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay

open Purelib.Riemann.Integration
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Transport

/-- The exact rational coordinate type of the quadratic replay. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian parameter type of the quadratic polynomial. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational rectangular box retained by the quadratic state. -/
abbrev Box := Geometry.Rational.Box
/-- The original winding-one state for the quadratic parameter and its ambient box. -/
abbrev State (parameter : Gaussian) (ambient :
  Box) :=
  State.WindingOne.Basic.WindingOneState
    (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo)
      ambient

/-- The two retained constructions of a quadratic winding-one track.

Choose the accelerated or deferred constructor without changing either constructor's initial state or total fallback. -/
inductive Recipe where
  /-- Use the accelerated quadratic track constructor and its original total refinement function. -/ | accelerated
  /-- Use the deferred quadratic track constructor and its original total refinement function. -/ | deferred
deriving DecidableEq
derive_exposed_repr QuadraticSampleReplay.Recipe

/-- Construct the selected original track from the nonzero quadratic parameter and its retained initial state. -/
@[expose] def Recipe.track (recipe : Recipe) {parameter :
  Gaussian} {ambient : Box}
    (nonzero : parameter ≠ 0) (initial : State parameter ambient) :
    Track.Basic.WindingOneTrack
      (Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo)
        ambient
        :=
  match recipe with
  | .accelerated => (SquareRootContinuationChain.Owner.ofState nonzero initial).track
  | .deferred => (Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero initial).track

/-- Run the original bounded Newton proposal search for the retained quadratic state and requested width. -/
@[expose] def attempt {parameter : Gaussian} {ambient :
  Box}
    (current : State parameter ambient) (epsilon :
      Coordinate) :=
  Newton.Search.Attempt.attempt (Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
    current.raw epsilon (Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances parameter)

/-- Quadratic states with the same box produce exactly the same bounded first-attempt result. -/
theorem attempt_eq_of_box_eq {parameter : Gaussian} {ambient :
  Box}
    (left right : State parameter ambient) (same : left.box = right.box)
    (epsilon : Coordinate) :
    (attempt left epsilon).map (fun result => result.state) =
    (attempt right epsilon).map (fun result => result.state) :=
  Newton.Search.Attempt.Replay.attempt_state_eq_of_box_eq _ _ _ same _ _

/-- A successful first attempt is the next state of the selected original track.

The equation leaves the track's total fallback unchanged when the bounded attempt fails. -/
theorem refine_eq_of_attempt {parameter : Gaussian} {ambient :
  Box}
    (recipe : Recipe) (nonzero : parameter ≠ 0) (initial current :
      State parameter ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (accepted : Refinement current.raw epsilon)
    (found : attempt current epsilon = some accepted) :
    (recipe.track nonzero initial).refine current epsilon positive = accepted.state := by
  unfold attempt at found
  cases recipe with
  | accelerated =>
      change (Track.Accelerated.refinement _ _ current epsilon positive _).state = _
      unfold Track.Accelerated.refinement
      with_unfolding_all rw [found]
  | deferred =>
      unfold Recipe.track
        Clearance.ExactQuadraticOwnerClearance.ownerOfState
      conv_lhs => whnf
      with_unfolding_all split
      · rename_i fast equation
        conv at equation => lhs; whnf
        erw [found] at equation
        cases equation
        rfl
      · rename_i equation
        conv at equation => lhs; whnf
        erw [found] at equation
        cases equation

/-- A successful attempt on a state with the same box determines the original track's refinement state. -/
theorem refine_eq_of_same_box_attempt {parameter : Gaussian} {ambient :
  Box}
    (recipe : Recipe) (nonzero : parameter ≠ 0) (initial current restored :
      State parameter ambient)
    (same : restored.box = current.box) (epsilon : Coordinate) (positive : 0 <
      epsilon)
    (accepted : Refinement restored.raw epsilon)
    (found : attempt restored epsilon = some accepted) :
    (recipe.track nonzero initial).refine current epsilon positive = accepted.state := by
  have agree := attempt_eq_of_box_eq restored current same epsilon
  rw [found] at agree
  cases original : attempt current epsilon with
  | none => simp only [original, Option.map] at agree; cases agree
  | some result =>
      simp only [original, Option.map, -eq_self, -iff_self] at agree
      have agree := Option.some.inj agree
      exact (refine_eq_of_attempt recipe nonzero initial current epsilon
        positive result original).trans agree.symm

/-- Both track recipes retain the supplied initial winding-one state exactly. -/
theorem Recipe.initial_eq {parameter : Gaussian} {ambient :
  Box}
    (recipe : Recipe) (nonzero : parameter ≠ 0) (initial :
      State parameter ambient) :
    (recipe.track nonzero initial).initial = initial := by
  cases recipe <;> rfl

/-- An equality of the actual owner constructor, not an arbitrary assertion
that two tracks approximate the same root. -/
@[expose] def Recipe.Matches {parameter : Gaussian} (recipe :
  Recipe) (owner : SquareRootContinuationChain.Owner parameter)
  : Prop :=
  recipe.track owner.parameterNonzero owner.track.initial = owner.track

/-- The accelerated recipe reconstructs the owner built directly from the supplied state. -/
theorem matches_ofState {parameter : Gaussian} {ambient :
  Box}
    (nonzero : parameter ≠ 0) (initial : State parameter ambient) :
    Recipe.Matches .accelerated
      (SquareRootContinuationChain.Owner.ofState nonzero initial) := rfl

/-- The deferred recipe reconstructs the exact quadratic owner built from the supplied state. -/
theorem matches_ownerOfState {parameter : Gaussian} {ambient :
  Box}
    (nonzero : parameter ≠ 0) (initial : State parameter ambient) :
    Recipe.Matches .deferred
      (Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero initial) := rfl

/-- Quadratic owner strengthening yields an owner with a retained matching track recipe. -/
theorem matches_strengthen {parameter : Gaussian} (owner :
  SquareRootContinuationChain.Owner parameter) :
    Recipe.Matches .deferred
      (Clearance.QuadraticCoefficientClearance.strengthen owner) := rfl

/-- The diameter-preparation checker itself selects the deferred recipe.
Successful callers do not have to supply an owner-history classification. -/
theorem matches_checkedPreparation
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
      Coordinate)
    (owner : SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt parameter))) (diameter
      : Coordinate)
    (accepted : CheckedSquareRootPreparation.Result segment parameter owner diameter)
    (found :
      (CheckedSquareRootPreparation.attempt segment parameter owner diameter).value =
        some accepted) :
    Recipe.Matches .deferred accepted.value := by
  letI (box ambient : Box) : Decidable (box.Refines ambient) := by
    unfold Box.Refines
    infer_instance
  rw [CheckedSquareRootPreparation.attempt_value_eq] at found
  unfold CheckedSquareRootPreparation.acceptedValue
    CheckedSquareRootPreparation.Candidate.check
    CheckedSquareRootPreparation.Candidate.capture at found
  dsimp only at found
  split at found
  · cases found
  · split at found
    · split at found
      · split at found
        · cases found
          exact matches_strengthen _
        · cases found
      · cases found
    · cases found

/-- The successful raw-source replay already determines its refiner recipe;
this classification is derived from its actual branch equation. -/
theorem matches_rawReplay
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : PreparedSourceReplay.Endpoint)
    (source : SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : PreparedSheetContinuation.StepRequest) {rootAmbient :
      Box}
    (restored : PreparedRawStateReplay.Checked _ rootAmbient
      (PreparedRawStateReplay.capture source.track.initial))
    (sameAmbient : rootAmbient = source.ambient)
    (accepted : PreparedSourceReplay.Accepted segment current source request)
    (found : PreparedRawSourceReplay.replay segment current source request restored sameAmbient = .ok
      accepted) :
    Recipe.Matches .deferred accepted.cached.preparedOwner := by
  unfold PreparedRawSourceReplay.replay at found
  dsimp only at found
  split at found
  · cases found
  · split at found
    · cases found
    · rename_i candidate attempted
      split at found
      · cases found
        exact matches_checkedPreparation _ _ _ _ candidate attempted
      · cases found

/-- Stationary quadratic transport preserves a retained matching recipe for the resulting owner. -/
theorem matches_stationaryTransport {source target : Gaussian}
    (recipe : Recipe) (owner :
      SquareRootContinuationChain.Owner source) (ownerRecipe : recipe.Matches owner)
    (nonzero : target ≠ 0)
    (small : Gaussian.Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (reserve : Coordinate) (same : source = target) :
    recipe.Matches (Clearance.ExactQuadraticOwnerClearance.reservedTransport owner nonzero small reserve) :=
      by
  subst target
  rw [Clearance.ExactQuadraticOwnerClearance.reservedTransport, dif_pos rfl]
  exact ownerRecipe

/-- The owner returned by the original prepared base query has a retained matching recipe. -/
theorem matches_baseQuery {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
    (edge : PreparedConstantModels.PreparedEdge curve differential) (recipe :
      Recipe)
    (ownerRecipe : recipe.Matches edge.cached.preparedOwner) :
    recipe.Matches (edge.directQueryOwner 0 edge.baseInside) := by
  unfold PreparedConstantModels.PreparedEdge.directQueryOwner
  apply matches_stationaryTransport recipe _ ownerRecipe
  rw [PreparedSheetContinuation.parameterAt_zero]

end Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay

end
