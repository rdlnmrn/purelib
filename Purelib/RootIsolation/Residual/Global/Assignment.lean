module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
public import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
import Purelib.RootIsolation.Newton.Restart.Seed.State
public import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
public import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Newton.Restart.Seed.Track
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Residual localization with retained finite ownership

A displayed sample with small residual determines an anchored winding-one
seed inside the coefficient-computed isolation square. Its original shrinking
track is assigned to the existing finite isolation, retaining radius and
distance bounds with that selected owner.
-/

namespace Purelib.RootIsolation.Residual.Global.Assignment

open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- The squarefree certificate retained by global residual localization. -/
public abbrev SquarefreeCertificate :=
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate

/-! ## Protected large-square localization and finite ownership -/

/-- Present the coefficient-computed isolation square as a protected ambient.

The original square carries its reflexive refinement, proper endpoint bounds
and coefficient-derived boundary clearance. -/
@[expose] public def largeSquareProtectedAmbient
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    Clearance.Box.Region.ProtectedAmbient p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) where
  box := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  refinesAmbient := Box.refines_refl _
  proper := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper p
  clearance := Clearance.Box.Boundary.RootRadius.largeSquare_boundaryClearance degreePositive

/-- Compute the uniform residual target within the global isolation square.

The target uses the original squarefree input, protected ambient and requested
radius, without selecting a new isolation or displayed point. -/
@[expose] public def insideResidualTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget input.squarefree
    (Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive) epsilon

/-- The uniform inside residual target is positive for a positive request.

The retained squarefree input and protected ambient supply the coefficient
and clearance budgets of the uniform anchored target. -/
public theorem insideResidualTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < Residual.Global.Assignment.insideResidualTarget input epsilon := by
  exact Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget_pos
    input.squarefree (Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive)
      epsilonPositive

/-- Select the residual threshold for a sample inside or outside the large square.

Closed-box containment selects the uniform anchored target inside; outside,
the coefficient-derived exclusion threshold uses the same original polynomial. -/
@[expose] public def residualThreshold
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) : Fraction.Rational :=
  if (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains sample then
    Residual.Global.Assignment.insideResidualTarget input epsilon
  else
    Residual.Global.Bounds.outsideResidualThreshold p

/-- The global residual threshold is positive for a positive requested radius.

Each branch retains its original positive target: the uniform protected-square
budget inside and the leading-term exclusion bound outside. -/
public theorem residualThreshold_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    0 < Residual.Global.Assignment.residualThreshold input sample epsilon := by
  by_cases inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains sample
  · rw [Residual.Global.Assignment.residualThreshold, if_pos inside]
    exact Residual.Global.Assignment.insideResidualTarget_pos input epsilonPositive
  · rw [Residual.Global.Assignment.residualThreshold, if_neg inside]
    exact Residual.Global.Bounds.outsideResidualThreshold_pos input.degreePositive

set_option genInjectivity false in
/-- A localized winding-one state and its owner in the computed finite isolation.

The record retains the chosen radius, complete shrinking track, initial-state
identity and distance bounds from the original displayed sample. -/
public structure AssignedResult
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) where
  /-- The actual positive radius chosen for the localized winding-one band. -/ radius : Fraction.Rational
  /-- The retained localization radius is positive. -/ radiusPositive : 0 < radius
  /-- The retained radius is no larger than the supplied request. -/ radiusLeRequested : radius ≤ epsilon
  /-- The localized winding-one state in the original global isolation square. -/ state :
    State.WindingOne.Basic.WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
  /-- The localized state box lies strictly inside the original global isolation square. -/ stateStrictLargeSquare :
    state.box.StrictInterior (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
  /-- The original polynomial's quadrupled winding on the retained state box is four. -/ windingFour :
    Winding.Box.Basic.quadrupledBoxWinding p state.box = 4
  /-- The retained box's squared diagonal is at most thirty-two times the squared request. -/ diagonalBound :
    state.box.diagonalSq ≤ 32 * epsilon ^ 2
  /-- The original total shrinking track constructed from the retained localization seed. -/ track :
    Track.Basic.WindingOneTrack p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
  /-- The track starts at exactly the retained localized state. -/ trackInitial : track.initial = state
  /-- The selected owner in the already computed isolation of the same original polynomial. -/ owner :
    Exact.Ownership.Basic.OwnerSelection input.isolation track
  /-- Every point in the localized box is within eighteen squared radii of the supplied sample. -/ bandNearSample : ∀ z,
    state.box.Contains z →
    Data.Gaussian.Norm.Basic.normSq (z - sample) ≤ 18 * radius ^ 2
  /-- Every point in the localized box has squared affine chordal distance at most eighteen squared requests from the
    supplied sample. -/ chordalBound : ∀ z, state.box.Contains z →
    Geometry.Projective.Chordal.Affine.affineChordalSq sample z ≤ 18 * epsilon ^ 2

constructive_injectivity AssignedResult

/-- Construct and assign a localized winding-one state from a small inside residual.

The anchored seed retains the original sample and radius. Its complete track
is assigned within the already computed finite isolation, with quantitative
box and chordal-distance bounds. -/
@[expose] public def assignInside
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains
      sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Residual.Global.Assignment.insideResidualTarget input epsilon) :
    Residual.Global.Assignment.AssignedResult input sample epsilon := by
  let parent := Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive
  have localized :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      input.squarefree parent sample inside epsilonPositive residualSmall
  let seed := Newton.Restart.Anchored.Seed.seedOfResidual input.squarefree
    input.elimination parent sample localized.1 epsilonPositive localized.2
  let state := seed.state input.degreeAtLeastTwo
  let track := seed.track input.degreeAtLeastTwo
  have radiusLe :=
    Newton.Restart.Anchored.Seed.seedOfResidual_radius_le_cap input.squarefree
      input.elimination parent sample localized.1 epsilonPositive
        localized.2
  have radiusSquareLe : seed.radius ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct seed.radiusPositive.le
      radiusLe 2
  have diagonal : state.box.diagonalSq ≤ 32 * epsilon ^ 2 := by
    have bandDiagonal := seed.band.diagonalSq_le seed.radiusPositive
    have scaled : 32 * seed.radius ^ 2 ≤ 32 * epsilon ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusSquareLe
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 32) (by decide)).le
    simpa only [state, Newton.Restart.Seed.state,
      Newton.Restart.Seed.band] using bandDiagonal.trans scaled
  have supported : track.initial.box.Refines input.isolation.support := by
    change state.box.Refines (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
    exact state.refinesAmbient
  let owner := (FTA.Squarefree.Build.BoxFTA.prove input).ownership track supported
  exact
    { radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := radiusLe
      state := state
      stateStrictLargeSquare := by
        simpa only [state, parent, Residual.Global.Assignment.largeSquareProtectedAmbient] using
          seed.state_strict_current input.degreeAtLeastTwo
      windingFour := state.rawWindingFour
      diagonalBound := diagonal
      track := track
      trackInitial := rfl
      owner := owner
      bandNearSample := by
        intro z zInside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall zInside
        simpa only [seed, state, parent,
          Newton.Restart.Seed.state,
          Newton.Restart.Seed.band,
          Newton.Restart.Anchored.Seed.seedOfResidual,
          Newton.Restart.Anchored.Basic.AnchoredInput.seed,
          Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
          Box.Square.Anchored.anchoredSquare_anchor] using distance
      chordalBound := by
        intro z zInside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall zInside
        have distanceFromSample : Data.Gaussian.Norm.Basic.normSq (sample - z) ≤
            18 * seed.radius ^ 2 := by
          have swapped : sample - z = -(z - sample) := by
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im] <;>
                ring1
          rw [swapped, Gaussian.Norm.Basic.normSq_neg]
          simpa only [seed, state, parent,
            Newton.Restart.Seed.state,
            Newton.Restart.Seed.band,
            Newton.Restart.Anchored.Seed.seedOfResidual,
            Newton.Restart.Anchored.Basic.AnchoredInput.seed,
            Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
            Box.Square.Anchored.anchoredSquare_anchor] using distance
        have scaled : 18 * seed.radius ^ 2 ≤ 18 * epsilon ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe (by decide)
        exact (Geometry.Projective.Chordal.Affine.affineChordalSq_le_normSq sample z).trans
          (distanceFromSample.trans scaled) }

/-- Assignment retains the requested radius below the uniform reference radius.

The contained sample's residual and the reference-radius bound force the
anchored minimum to choose exactly the original positive request. -/
public theorem assignInside_radius_eq_of_le_uniformReference
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains
      sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Residual.Global.Assignment.insideResidualTarget input epsilon)
    (epsilonLeReference :
      epsilon ≤ Newton.Restart.Uniform.Budget.uniformAnchoredRadius input.squarefree
        (Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive) 1) :
    (Residual.Global.Assignment.assignInside input sample inside epsilonPositive residualSmall).radius =
      epsilon := by
  let parent := Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive
  have residualQuarter :
      Data.Gaussian.Norm.Basic.normSq (p.eval sample) < parent.clearance.bound / 4 := by
    exact residualSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  change Newton.Restart.Anchored.Budget.anchoredRadius input.squarefree parent sample
      epsilon = epsilon
  exact Newton.Restart.Uniform.Anchored.anchoredRadius_eq_cap_of_le_uniformReference
    input.squarefree parent sample inside epsilonLeReference residualQuarter

end Purelib.RootIsolation.Residual.Global.Assignment
