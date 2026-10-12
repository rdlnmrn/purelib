module

import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
public import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
import Purelib.RootIsolation.Newton.Restart.Seed.State
public import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.State.WindingOne.Region
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Newton.Restart.Seed.Track
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
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
import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Constructive residual-to-chordal winding boxes

A sufficiently small polynomial residual at a displayed Gaussian rational,
together with a containing winding-one state and finite squarefree and axis
elimination certificates, constructs a nearby winding-one box and its total
shrinking track.  No completed root is selected or asserted.
-/

namespace Purelib.RootIsolation.Residual.Chordal.Basic
/-- The original finite squarefree certificate required by local Newton extraction. -/
abbrev SquarefreeCertificate :=
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate

/-- Minimal protected view used by the generalized residual constructor. -/
abbrev protectedAmbient
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.WindingOne.Basic.WindingOneState p ambient) :
    Clearance.Box.Region.ProtectedAmbient p ambient :=
  Clearance.Box.Region.ProtectedAmbient.ofWindingOne current

set_option genInjectivity false in
/-- Paper-facing output of the local residual converse.  Every field is
finite data or a proof about displayed rational data. -/
structure ResidualChordalResult
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) where
  /-- The retained residual threshold for the original sample and requested radius. -/ residualTarget :
    Fraction.Rational
  /-- The retained threshold is exactly the original anchored residual target. -/ residualTarget_eq : residualTarget =
    Newton.Restart.Anchored.Budget.anchoredResidualTarget
      squarefree (Residual.Chordal.Basic.protectedAmbient current) sample epsilon
  /-- The retained residual target is positive. -/ residualTargetPositive : 0 < residualTarget
  /-- The actual radius selected for the retained Newton band. -/ radius : Fraction.Rational
  /-- The selected band radius is positive. -/ radiusPositive : 0 < radius
  /-- The selected band radius does not exceed the requested tolerance. -/ radiusLeRequested : radius <= epsilon
  /-- The actual winding-one state extracted near the original sample. -/ state : State.WindingOne.Basic.WindingOneState
    p ambient
  /-- The new state box lies strictly inside the original state box. -/ stateStrictCurrent : state.box.StrictInterior
    current.box
  /-- The retained state has raw quadrupled winding equal to four. -/ windingFour :
    Winding.Box.Basic.quadrupledBoxWinding p state.box = 4
  /-- The retained box's squared diagonal is at most thirty-two times the selected radius squared. -/ bandDiagonal :
    state.box.diagonalSq <= 32 * radius ^ 2
  /-- The retained box's squared diagonal is at most thirty-two times the requested tolerance squared. -/ diagonalBound
    : state.box.diagonalSq <= 32 * epsilon ^ 2
  /-- The shrinking track built from the retained new winding-one state. -/ track : Track.Basic.WindingOneTrack p
    ambient
  /-- The track's initial state is exactly the retained new state. -/ trackInitial : track.initial = state
  /-- Every point in the retained box has squared Euclidean distance from the sample at most eighteen times the selected
    radius squared. -/ bandNearSample : forall z, state.box.Contains z ->
    Data.Gaussian.Norm.Basic.normSq (z - sample) <= 18 * radius ^ 2
  /-- Every point in the retained box has squared chordal distance from the sample at most eighteen times the requested
    tolerance squared. -/ chordalBound : forall z, state.box.Contains z ->
    Geometry.Projective.Chordal.Affine.affineChordalSq sample z <= 18 * epsilon ^ 2

constructive_injectivity ResidualChordalResult

set_option genInjectivity false in
/-- The public residual observation distinguishes an exact displayed
Gaussian-rational zero from the genuinely approximate winding-box case. -/
inductive ResidualChordalObservation
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) : Type where
  /-- Retain the exact zero evaluation of the displayed Gaussian sample. -/ | exact (evaluation : p.eval sample = 0)
  /-- Retain the actual nearby winding-one state, track and residual-to-distance bounds. -/ | band
      (result : Residual.Chordal.Basic.ResidualChordalResult squarefree elimination current sample
        epsilon)

constructive_injectivity ResidualChordalObservation

/-- The exact positive residual request used by the constructor. -/
def residualTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (epsilon : Fraction.Rational) : Fraction.Rational :=
  Newton.Restart.Anchored.Budget.anchoredResidualTarget
    squarefree (Residual.Chordal.Basic.protectedAmbient current) sample epsilon

/-- A strict interior sample and positive requested radius give a positive anchored residual target. -/
theorem residualTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (strict : current.box.StrictContains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    0 < Residual.Chordal.Basic.residualTarget squarefree current sample epsilon := by
  exact Newton.Restart.Anchored.Budget.anchoredResidualTarget_pos
    squarefree (Residual.Chordal.Basic.protectedAmbient current) sample strict epsilonPositive

/-- A displayed strict-interior sample below the computed positive residual
target constructs a nearby winding-one box and an ordinary shrinking RAT.
Every displayed point in the new box has squared chordal distance at most
`18 * epsilon^2` from the sample. -/
def ofResidual
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (strict : current.box.StrictContains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Residual.Chordal.Basic.residualTarget squarefree current sample epsilon) :
    Residual.Chordal.Basic.ResidualChordalResult squarefree elimination current sample epsilon := by
  let seed := Newton.Restart.Anchored.Seed.seedOfResidual squarefree
    elimination (Residual.Chordal.Basic.protectedAmbient current) sample strict epsilonPositive
      residualSmall
  let state := seed.state degreeAtLeastTwo
  let track := seed.track degreeAtLeastTwo
  have radiusLe :=
    Newton.Restart.Anchored.Seed.seedOfResidual_radius_le_cap squarefree
      elimination (Residual.Chordal.Basic.protectedAmbient current) sample strict epsilonPositive
        residualSmall
  have radiusSquareLe : seed.radius ^ 2 <= epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct seed.radiusPositive.le
      radiusLe 2
  have scaledRadiusSquare : 18 * seed.radius ^ 2 <= 18 * epsilon ^ 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      radiusSquareLe (by decide)
  exact
    { residualTarget := Residual.Chordal.Basic.residualTarget squarefree current sample epsilon
      residualTarget_eq := rfl
      residualTargetPositive := Residual.Chordal.Basic.residualTarget_pos squarefree current sample
        strict epsilonPositive
      radius := seed.radius
      radiusPositive := seed.radiusPositive
      radiusLeRequested := radiusLe
      state := state
      stateStrictCurrent := seed.state_strict_current degreeAtLeastTwo
      windingFour := (seed.state degreeAtLeastTwo).rawWindingFour
      bandDiagonal := by
        simpa only [state, Newton.Restart.Seed.state,
          Newton.Restart.Seed.band] using
            seed.band.diagonalSq_le seed.radiusPositive
      diagonalBound := by
        have bandDiagonal := seed.band.diagonalSq_le seed.radiusPositive
        have scaled : 32 * seed.radius ^ 2 <= 32 * epsilon ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 32) (by decide)).le
        exact (by
          simpa only [state, Newton.Restart.Seed.state,
            Newton.Restart.Seed.band] using
              bandDiagonal.trans scaled)
      track := track
      trackInitial := rfl
      bandNearSample := by
        intro z inside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall inside
        simpa only [seed, state,
          Newton.Restart.Seed.state,
          Newton.Restart.Seed.band,
          Newton.Restart.Anchored.Seed.seedOfResidual,
          Newton.Restart.Anchored.Basic.AnchoredInput.seed,
          Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
          Box.Square.Anchored.anchoredSquare_anchor] using distance
      chordalBound := by
        intro z inside
        have distance := seed.band.normSq_sub_anchor_le
          seed.displacementSmall inside
        have distanceFromSample : Data.Gaussian.Norm.Basic.normSq (sample - z) <=
            18 * seed.radius ^ 2 := by
          have swapped : sample - z = -(z - sample) := by
            apply Gaussian.Basic.ext <;>
              simp only [Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.neg_re,
                Gaussian.Basic.neg_im] <;>
              ring1
          rw [swapped, Gaussian.Norm.Basic.normSq_neg]
          simpa only [seed, state,
            Newton.Restart.Seed.state,
            Newton.Restart.Seed.band,
            Newton.Restart.Anchored.Seed.seedOfResidual,
            Newton.Restart.Anchored.Basic.AnchoredInput.seed,
            Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
            Box.Square.Anchored.anchoredSquare_anchor] using
              distance
        exact (Geometry.Projective.Chordal.Affine.affineChordalSq_le_normSq sample z).trans
          (distanceFromSample.trans scaledRadiusSquare) }

/-- Point-independent variant for an ordinarily contained sample.  The
boundary-clearance quarter first proves strict containment, then invokes the
same local constructor. -/
def ofUniformResidual
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (contains : current.box.Contains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget
        squarefree (Residual.Chordal.Basic.protectedAmbient current) epsilon) :
    Residual.Chordal.Basic.ResidualChordalResult squarefree elimination current sample epsilon := by
  have localized :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      squarefree (Residual.Chordal.Basic.protectedAmbient current) sample contains epsilonPositive
        residualSmall
  exact Residual.Chordal.Basic.ofResidual degreeAtLeastTwo squarefree elimination current sample
    localized.1 epsilonPositive localized.2

/-- Exact evaluation is returned immediately; only a non-exact displayed
sample is packaged as a nearby winding-one band. -/
def observeOfResidual
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (strict : current.box.StrictContains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Residual.Chordal.Basic.residualTarget squarefree current sample epsilon) :
    Residual.Chordal.Basic.ResidualChordalObservation squarefree elimination current sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (Residual.Chordal.Basic.ofResidual degreeAtLeastTwo squarefree elimination current sample
      strict epsilonPositive residualSmall)

/-- Point-independent public classifier for an ordinarily contained sample. -/
def observeOfUniformResidual
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : Residual.Chordal.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (sample : Gaussian.Basic.Canonical) (contains : current.box.Contains sample)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) <
      Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget
        squarefree (Residual.Chordal.Basic.protectedAmbient current) epsilon) :
    Residual.Chordal.Basic.ResidualChordalObservation squarefree elimination current sample epsilon :=
  if evaluation : p.eval sample = 0 then
    .exact evaluation
  else
    .band (Residual.Chordal.Basic.ofUniformResidual degreeAtLeastTwo squarefree elimination current
      sample contains epsilonPositive residualSmall)
end Purelib.RootIsolation.Residual.Chordal.Basic

end

end
