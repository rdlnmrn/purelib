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

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius

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
    {p : CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 <
      p.natDegree) :
    Clearance.Box.Region.ProtectedAmbient p (Box.largeSquareBox p) where
  box := Box.largeSquareBox p
  refinesAmbient := Box.refines_refl _
  proper := Box.largeSquareBox_proper p
  clearance := Clearance.Box.Boundary.RootRadius.largeSquare_boundaryClearance degreePositive

/-- Compute the uniform residual target within the global isolation square.

The target uses the original squarefree input, protected ambient and requested
radius, without selecting a new isolation or displayed point. -/
@[expose] public def insideResidualTarget
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget input.squarefree
    (largeSquareProtectedAmbient input.degreePositive) epsilon

/-- The uniform inside residual target is positive for a positive request.

The retained squarefree input and protected ambient supply the coefficient
and clearance budgets of the uniform anchored target. -/
public theorem insideResidualTarget_pos
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < insideResidualTarget input epsilon := by
  exact Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget_pos
    input.squarefree (largeSquareProtectedAmbient input.degreePositive)
      epsilonPositive

/-- Select the residual threshold for a sample inside or outside the large square.

Closed-box containment selects the uniform anchored target inside; outside,
the coefficient-derived exclusion threshold uses the same original polynomial. -/
@[expose] public def residualThreshold
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) : Fraction.Rational :=
  if (Box.largeSquareBox p).Contains sample then
    insideResidualTarget input epsilon
  else
    Bounds.outsideResidualThreshold p

/-- The global residual threshold is positive for a positive requested radius.

Each branch retains its original positive target: the uniform protected-square
budget inside and the leading-term exclusion bound outside. -/
public theorem residualThreshold_pos
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    0 < residualThreshold input sample epsilon := by
  by_cases inside : (Box.largeSquareBox p).Contains sample
  · rw [residualThreshold, if_pos inside]
    exact insideResidualTarget_pos input epsilonPositive
  · rw [residualThreshold, if_neg inside]
    exact Bounds.outsideResidualThreshold_pos input.degreePositive

set_option genInjectivity false in
/-- A localized winding-one state and its owner in the computed finite isolation.

The record retains the chosen radius, complete shrinking track, initial-state
identity and distance bounds from the original displayed sample. -/
public structure AssignedResult
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational)
    (output : Exact.Basic.Output p (Box.largeSquareBox p) p.natDegree :=
      input.isolation) where
  /-- The actual positive radius chosen for the localized winding-one band. -/ radius : Fraction.Rational
  /-- The retained localization radius is positive. -/ radiusPositive : 0 < radius
  /-- The retained radius is no larger than the supplied request. -/ radiusLeRequested : radius ≤ epsilon
  /-- The localized winding-one state in the original global isolation square. -/ state :
    State.WindingOne.Basic.WindingOneState p (Box.largeSquareBox p)
  /-- The localized state box lies strictly inside the original global isolation square. -/ stateStrictLargeSquare :
    state.box.StrictInterior (Box.largeSquareBox p)
  /-- The original polynomial's quadrupled winding on the retained state box is four. -/ windingFour :
    Winding.Box.Basic.quadrupledBoxWinding p state.box = 4
  /-- The retained box's squared diagonal is at most thirty-two times the squared request. -/ diagonalBound :
    state.box.diagonalSq ≤ 32 * epsilon ^ 2
  /-- The original total shrinking track constructed from the retained localization seed. -/ track :
    Track.Basic.WindingOneTrack p (Box.largeSquareBox p)
  /-- The track starts at exactly the retained localized state. -/ trackInitial : track.initial = state
  /-- The selected owner in the already computed isolation of the same original polynomial. -/ owner :
    Exact.Ownership.Basic.OwnerSelection output track
  /-- Every point in the localized box is within eighteen squared radii of the supplied sample. -/ bandNearSample : ∀ z,
    state.box.Contains z →
    Gaussian.Norm.Basic.normSq (z - sample) ≤ 18 * radius ^ 2
  /-- Every point in the localized box has squared affine chordal distance at most eighteen squared requests from the
    supplied sample. -/ chordalBound : ∀ z, state.box.Contains z →
    Geometry.Projective.Chordal.Affine.affineChordalSq sample z ≤ 18 * epsilon ^ 2

constructive_injectivity AssignedResult

/-- Construct and assign a localized winding-one state from a small inside residual.

The anchored seed retains the original sample and radius. Its complete track
is assigned through the supplied original box result's ownership function,
reusing its same finite isolation without running another isolation producer.
The result retains quantitative box and chordal-distance bounds. -/
@[expose] public def assignInsideWithElimination
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (boxes : FTA.Squarefree.BoxResult p)
    (support : boxes.isolation.support = Box.largeSquareBox p)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains
      sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) <
      insideResidualTarget input epsilon) :
    AssignedResult input sample epsilon boxes.isolation := by
  let parent := largeSquareProtectedAmbient input.degreePositive
  have localized :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      input.squarefree parent sample inside epsilonPositive residualSmall
  let seed := Newton.Restart.Anchored.Seed.seedOfResidual input.squarefree
    elimination parent sample localized.1 epsilonPositive localized.2
  let state := seed.state input.degreeAtLeastTwo
  let track := seed.track input.degreeAtLeastTwo
  have radiusLe :=
    Newton.Restart.Anchored.Seed.seedOfResidual_radius_le_cap input.squarefree
      elimination parent sample localized.1 epsilonPositive
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
  have supported : track.initial.box.Refines boxes.isolation.support := by
    rewrite [support]
    exact state.refinesAmbient
  let owner := boxes.ownership track supported
  exact
    { radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := radiusLe
      state := state
      stateStrictLargeSquare := by
        simpa only [state, parent, largeSquareProtectedAmbient] using
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
        have distanceFromSample : Gaussian.Norm.Basic.normSq (sample - z) ≤
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

/-- Localize with the original input's canonical axis certificate and the same retained isolation.

This specialization keeps the original certificate, seed, track and dependent
owner. The common constructor consumes that same data without changing the
canonical procedure's numerical requests.
-/
@[expose] public def assignInsideUsing
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (boxes : FTA.Squarefree.BoxResult p)
    (support : boxes.isolation.support = Box.largeSquareBox p)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) < insideResidualTarget input epsilon) :
    AssignedResult input sample epsilon boxes.isolation :=
  assignInsideWithElimination input input.elimination boxes support sample inside epsilonPositive residualSmall

/-- Compute the original anchored residual seed without constructing its band clearances or track.

The source sample, protected isolation square, residual threshold and requested
radius are exactly those of the inside localization constructor. -/
@[expose] public def insideSeed
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) < insideResidualTarget input epsilon) :
    Newton.Restart.Seed input.squarefree elimination (largeSquareProtectedAmbient input.degreePositive) := by
  let parent := largeSquareProtectedAmbient input.degreePositive
  have localized := Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
    input.squarefree parent sample inside epsilonPositive residualSmall
  exact Newton.Restart.Anchored.Seed.seedOfResidual input.squarefree elimination parent
    sample localized.1 epsilonPositive localized.2

section CachedInside

variable {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
  {degreeBound : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (boxes : FTA.Squarefree.BoxResult p)
  (support : boxes.isolation.support = Box.largeSquareBox p)
  (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains sample)
  {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
  (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) < insideResidualTarget input epsilon)
  (seed : Newton.Restart.Seed input.squarefree elimination
    (largeSquareProtectedAmbient input.degreePositive))
  (seedSame : seed = insideSeed input elimination sample inside epsilonPositive residualSmall)
  (state : State.WindingOne.Basic.WindingOneState p (Box.largeSquareBox p))
  (stateSame : state = seed.state input.degreeAtLeastTwo)
  (track : Track.Basic.WindingOneTrack p (Box.largeSquareBox p))
  (trackSame : track = seed.track input.degreeAtLeastTwo)
  (owner : Exact.Ownership.Basic.OwnerSelection boxes.isolation track)
  (ownerSame : owner = boxes.ownership track
    (support.symm ▸ track.initial.refinesAmbient))

/-- Assemble the complete original inside assignment from its authenticated seed, state, track and owner.

Every numerical field is supplied from the actual retained caches. The owner
is the complete original box result's selection, including its retained
assignment-radius refinement, rather than only an equal selected index. -/
public def assignInsideFromCaches : AssignedResult input sample epsilon boxes.isolation := by
  let original := assignInsideWithElimination input elimination boxes support sample inside
    epsilonPositive residualSmall
  have radiusEq : seed.radius = original.radius := by
    cases seedSame
    rfl
  have stateEq : state = original.state := by
    cases stateSame
    cases seedSame
    rfl
  have trackEq : track = original.track := by
    cases trackSame
    cases seedSame
    rfl
  exact
    { radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := by rewrite [radiusEq]; exact original.radiusLeRequested
      state := state
      stateStrictLargeSquare := stateEq.symm ▸ original.stateStrictLargeSquare
      windingFour := state.rawWindingFour
      diagonalBound := stateEq.symm ▸ original.diagonalBound
      track := track
      trackInitial := by rewrite [trackEq, stateEq]; exact original.trackInitial
      owner := owner
      bandNearSample := by
        intro z contains
        have retained := original.bandNearSample z (stateEq ▸ contains)
        rewrite [← radiusEq] at retained
        exact retained
      chordalBound := by
        intro z contains
        exact original.chordalBound z (stateEq ▸ contains) }

/-- Read the retained state and track alongside the complete original assignment equality. -/
private theorem assignInsideFromCaches_readbacks :
    (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame).state = state ∧
    (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame).track = track ∧
    assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame =
      assignInsideWithElimination input elimination boxes support sample inside epsilonPositive residualSmall := by
  constructor
  · rfl
  constructor
  · rfl
  · cases seedSame
    cases stateSame
    cases trackSame
    cases ownerSame
    rfl

/-- The cache-consuming inside assignment retains the exact original initial state. -/
public theorem assignInsideFromCaches_state :
    (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame).state = state :=
  (assignInsideFromCaches_readbacks input elimination boxes support sample inside epsilonPositive
    residualSmall seed seedSame state stateSame track trackSame owner ownerSame).1

/-- The cache-consuming inside assignment retains the exact original once-built track. -/
public theorem assignInsideFromCaches_track :
    (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame).track = track :=
  (assignInsideFromCaches_readbacks input elimination boxes support sample inside epsilonPositive
    residualSmall seed seedSame state stateSame track trackSame owner ownerSame).2.1

/-- All retained inside-assignment fields agree with the complete original elimination procedure. -/
public theorem assignInsideFromCaches_eq :
    assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame =
      assignInsideWithElimination input elimination boxes support sample inside epsilonPositive residualSmall :=
  (assignInsideFromCaches_readbacks input elimination boxes support sample inside epsilonPositive
    residualSmall seed seedSame state stateSame track trackSame owner ownerSame).2.2

/-- Transport the retained complete owner selection along the actual cached-track readback. -/
private theorem assignInsideFromCaches_owner_readback :
    ((assignInsideFromCaches_track input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame) ▸
      (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
        seed seedSame state stateSame track trackSame owner ownerSame).owner) = owner := by
  rfl

/-- The retained track equality identifies the complete cached owner selection unchanged. -/
public theorem assignInsideFromCaches_owner :
    ((assignInsideFromCaches_track input elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame) ▸
      (assignInsideFromCaches input elimination boxes support sample inside epsilonPositive residualSmall
        seed seedSame state stateSame track trackSame owner ownerSame).owner) = owner :=
  assignInsideFromCaches_owner_readback input elimination boxes support sample inside epsilonPositive
    residualSmall seed seedSame state stateSame track trackSame owner ownerSame

end CachedInside

/-- Restoring canonical inside caches gives the complete original canonical-certificate assignment. -/
public theorem assignInsideFromCaches_eq_using
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (boxes : FTA.Squarefree.BoxResult p)
    (support : boxes.isolation.support = Box.largeSquareBox p)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) < insideResidualTarget input epsilon)
    (seed : Newton.Restart.Seed input.squarefree input.elimination
      (largeSquareProtectedAmbient input.degreePositive))
    (seedSame : seed = insideSeed input input.elimination sample inside epsilonPositive residualSmall)
    (state : State.WindingOne.Basic.WindingOneState p (Box.largeSquareBox p))
    (stateSame : state = seed.state input.degreeAtLeastTwo)
    (track : Track.Basic.WindingOneTrack p (Box.largeSquareBox p))
    (trackSame : track = seed.track input.degreeAtLeastTwo)
    (owner : Exact.Ownership.Basic.OwnerSelection boxes.isolation track)
    (ownerSame : owner = boxes.ownership track (support.symm ▸ track.initial.refinesAmbient)) :
    assignInsideFromCaches input input.elimination boxes support sample inside epsilonPositive residualSmall
      seed seedSame state stateSame track trackSame owner ownerSame =
      assignInsideUsing input boxes support sample inside epsilonPositive residualSmall :=
  assignInsideFromCaches_eq input input.elimination boxes support sample inside epsilonPositive residualSmall
    seed seedSame state stateSame track trackSame owner ownerSame

/-- Localize a small inside residual using the coefficient-computed original isolation.

The original box result is computed once and supplied to the cache-consuming
constructor. Its isolation is the original input's canonical isolation;
existing consumers retain their original dependent owner type.
-/
@[expose] public def assignInside
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains
      sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) <
      insideResidualTarget input epsilon) :
    AssignedResult input sample epsilon :=
  let boxes := FTA.Squarefree.Build.BoxFTA.prove input
  assignInsideUsing input boxes rfl sample inside epsilonPositive residualSmall

/-- Assignment retains the requested radius below the uniform reference radius.

The contained sample's residual and the reference-radius bound force the
anchored minimum to choose exactly the original positive request. -/
public theorem assignInside_radius_eq_of_le_uniformReference
    {p : CanonicalCoefficients.CoefficientPolynomial} (input : FTA.Squarefree.Input p)
    (sample : Gaussian.Basic.Canonical) (inside : (Box.largeSquareBox p).Contains
      sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Gaussian.Norm.Basic.normSq (p.eval sample) <
      insideResidualTarget input epsilon)
    (epsilonLeReference :
      epsilon ≤ Newton.Restart.Uniform.Budget.uniformAnchoredRadius input.squarefree
        (largeSquareProtectedAmbient input.degreePositive) 1) :
    (assignInside input sample inside epsilonPositive residualSmall).radius =
      epsilon := by
  let parent := largeSquareProtectedAmbient input.degreePositive
  have residualQuarter :
      Gaussian.Norm.Basic.normSq (p.eval sample) < parent.clearance.bound / 4 := by
    exact residualSmall.trans_le (Fraction.Order.Basic.min_le_left _ _)
  change Newton.Restart.Anchored.Budget.anchoredRadius input.squarefree parent sample
      epsilon = epsilon
  exact Newton.Restart.Uniform.Anchored.anchoredRadius_eq_cap_of_le_uniformReference
    input.squarefree parent sample inside epsilonLeReference residualQuarter

end Purelib.RootIsolation.Residual.Global.Assignment
