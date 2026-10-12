module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Interior
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
public import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
public import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
public import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Comparison
public import Purelib.RootIsolation.State.WindingOne.Region
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Protected

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.Newton.Restart (Seed)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.Newton.Restart.Persistence

/-- An auxiliary winding-one box close to a displayed rational sample forces
that sample into every supplied later state once both numerical boxes are
known to belong to the same winding-one container.  The later state is
refined only internally to obtain a protected margin; the returned point is
the original rational `sample`, not a limit of the refinements. -/
theorem sample_inside_later_of_auxiliary_winding
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (container later auxiliary : WindingOneState p ambient)
    (laterRefines : later.box.Refines container.box)
    (auxiliaryInside : auxiliary.box.StrictInterior container.box)
    (sample : Canonical)
    (auxiliaryLeft :
      sample.re -
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance ≤ auxiliary.box.xLower)
    (auxiliaryRight : auxiliary.box.xUpper ≤
      sample.re +
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance)
    (auxiliaryBottom :
      sample.im -
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance ≤ auxiliary.box.yLower)
    (auxiliaryTop : auxiliary.box.yUpper ≤
      sample.im +
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance) :
    later.box.Contains sample := by
  let rho :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius p later.box
      later.clearance
  let rhoPositive :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
      later.clearance later.proper
  let deep := Track.Protected.protectedRefinement track later
  have deepInsideLater : deep.box.StrictInterior later.box := by
    simpa only [deep, Track.Protected.protectedRefinement, rho, rhoPositive] using
      track.strict later rho rhoPositive
  have deepInsideContainer : deep.box.StrictInterior container.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines deepInsideLater) laterRefines
  have notSeparated : ¬auxiliary.box.Separated deep.box :=
    State.WindingOne.Comparison.not_separated_inside_winding_one degreeAtLeastTwo squarefree elimination
      container auxiliary deep auxiliaryInside deepInsideContainer
  have margins := Track.Protected.protectedRefinement_margin
    ((by decide : (0 : Nat) < 2).trans_le degreeAtLeastTwo) track later
  exact Box.Interior.contains_sample_of_not_separated_of_protected_margin
    margins.1 margins.2.1 margins.2.2.1 margins.2.2.2
      (by simpa only [rho] using auxiliaryLeft)
      (by simpa only [rho] using auxiliaryRight)
      (by simpa only [rho] using auxiliaryBottom)
      (by simpa only [rho] using auxiliaryTop)
      (by simpa only [deep] using notSeparated)

/-- Concrete specialization for a winding band built from one displayed
rational residual.  If its finite Newton radius is below the later state's
protected margin, its original rational anchor is inside that later state.
This is the numerical persistence bridge; the anchor is never asserted to
be a polynomial root. -/
theorem residual_seed_anchor_inside_later
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (seed : Seed squarefree elimination
      (State.WindingOne.Region.protectedAmbient current))
    (radiusSmall : 3 * seed.radius ≤
      4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
        later.box later.clearance) :
    later.box.Contains seed.source.anchor := by
  let auxiliary := seed.state degreeAtLeastTwo
  have bandBounds := seed.anchor_band_coordinate_bounds
  have left : seed.source.anchor.re -
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance ≤ auxiliary.box.xLower := by
    calc
      seed.source.anchor.re -
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance ≤
          seed.source.anchor.re - 3 * seed.radius :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusSmall seed.source.anchor.re
      _ ≤ auxiliary.box.xLower := by
        simpa only [auxiliary, Seed.state]
          using bandBounds.1
  have right : auxiliary.box.xUpper ≤ seed.source.anchor.re +
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance := by
    calc
      auxiliary.box.xUpper ≤ seed.source.anchor.re + 3 * seed.radius := by
        simpa only [auxiliary, Seed.state]
          using bandBounds.2.1
      _ = 3 * seed.radius + seed.source.anchor.re := by ring1
      _ ≤ 4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance + seed.source.anchor.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct radiusSmall
          seed.source.anchor.re
      _ = seed.source.anchor.re +
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance := by ring1
  have bottom : seed.source.anchor.im -
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance ≤ auxiliary.box.yLower := by
    calc
      seed.source.anchor.im -
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance ≤
          seed.source.anchor.im - 3 * seed.radius :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusSmall seed.source.anchor.im
      _ ≤ auxiliary.box.yLower := by
        simpa only [auxiliary, Seed.state]
          using bandBounds.2.2.1
  have top : auxiliary.box.yUpper ≤ seed.source.anchor.im +
        4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance := by
    calc
      auxiliary.box.yUpper ≤ seed.source.anchor.im + 3 * seed.radius := by
        simpa only [auxiliary, Seed.state]
          using bandBounds.2.2.2
      _ = 3 * seed.radius + seed.source.anchor.im := by ring1
      _ ≤ 4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance + seed.source.anchor.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct radiusSmall
          seed.source.anchor.im
      _ = seed.source.anchor.im +
          4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance := by ring1
  exact sample_inside_later_of_auxiliary_winding degreeAtLeastTwo squarefree
    elimination track current later auxiliary laterRefines
      (seed.state_strict_current degreeAtLeastTwo) seed.source.anchor left
      right bottom top

/-- End-to-end automatic specialization: a displayed rational point strictly
inside the selected container, with residual below the coefficient-computed
target capped by a later state's protected radius, lies in that later state.
All Newton, Taylor, and source-containment budgets are computed internally. -/
theorem strict_residual_sample_inside_later
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (point : Canonical)
    (strict : current.box.StrictContains point)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Newton.Restart.Anchored.Budget.anchoredResidualTarget squarefree
        (State.WindingOne.Region.protectedAmbient current)
        point
        (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance)) :
    later.box.Contains point := by
  let cap :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius p later.box
      later.clearance
  let capPositive :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
      later.clearance later.proper
  let seed := Newton.Restart.Anchored.Seed.seedOfResidual squarefree
    elimination (State.WindingOne.Region.protectedAmbient current) point strict capPositive residual
  have radiusLeCap : seed.radius ≤ cap := by
    simpa only [seed, cap, capPositive] using
      Newton.Restart.Anchored.Seed.seedOfResidual_radius_le_cap squarefree
        elimination (State.WindingOne.Region.protectedAmbient current) point strict capPositive residual
  have threeLeFour : (3 : Fraction.Rational) ≤ 4 := by decide
  have threeRadiusLeThreeCap : 3 * seed.radius ≤ 3 * cap :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLeCap
      (by decide)
  have threeCapLeFourCap : 3 * cap ≤ 4 * cap :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct threeLeFour
      capPositive.le
  have radiusSmall : 3 * seed.radius ≤ 4 * cap :=
    threeRadiusLeThreeCap.trans threeCapLeFourCap
  have contains := residual_seed_anchor_inside_later degreeAtLeastTwo
    squarefree elimination track current later laterRefines seed (by
      simpa only [cap] using radiusSmall)
  simpa only [seed, Newton.Restart.Anchored.Seed.seedOfResidual,
    Newton.Restart.Anchored.Basic.AnchoredInput.seed,
    Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
    Box.Square.Anchored.anchoredSquare_anchor] using contains

/-- Point-independent automatic specialization.  Boundary clearance supplies
a uniform interior strip, so the residual target can be computed before the
displayed rational event sample is chosen. -/
theorem uniform_residual_sample_inside_later
    {p : CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (point : Canonical)
    (contains : current.box.Contains point)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree
        (State.WindingOne.Region.protectedAmbient current)
        (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
          later.box later.clearance)) :
    later.box.Contains point := by
  let cap :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius p later.box
      later.clearance
  have capPositive : 0 < cap := by
    simpa only [cap] using
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
        later.clearance later.proper
  have ready :=
    Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
      squarefree (State.WindingOne.Region.protectedAmbient current) point contains capPositive (by
        simpa only [cap] using residual)
  exact strict_residual_sample_inside_later degreeAtLeastTwo squarefree
    elimination track current later laterRefines point ready.1 (by
      simpa only [cap] using ready.2)

end Purelib.RootIsolation.Newton.Restart.Persistence

end
