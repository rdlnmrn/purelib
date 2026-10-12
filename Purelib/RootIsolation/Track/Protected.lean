module
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.ProtectedBoundary
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.State.WindingOne.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

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

namespace Purelib.RootIsolation.Track.Protected

/-- Refine one supplied winding state far enough that the finite protected-
boundary theorem gives a uniform four-radius margin inside it. -/
def protectedRefinement
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) : WindingOneState p ambient :=
  track.refine current
    (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box
      current.clearance)
    (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
      current.clearance current.proper)

/-- The protected-boundary refinement stays within its original input box. -/
theorem protectedRefinement_refines
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) :
    (protectedRefinement track current).box.Refines current.box := by
  exact track.nested current
    (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box
      current.clearance)
    (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
      current.clearance current.proper)

/-- The protected refinement is uniformly away from all four sides of its
input box. -/
theorem protectedRefinement_margin
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) :
    let rho :=
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box
        current.clearance
    current.box.xLower + 4 * rho < (protectedRefinement track current).box.xLower ∧
      (protectedRefinement track current).box.xUpper < current.box.xUpper - 4 * rho ∧
      current.box.yLower + 4 * rho < (protectedRefinement track current).box.yLower ∧
      (protectedRefinement track current).box.yUpper < current.box.yUpper - 4 * rho := by
  let rho :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box
      current.clearance
  let positive :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
      current.clearance current.proper
  let refined := protectedRefinement track current
  have diagonal : refined.box.diagonalSq ≤ rho ^ 2 := by
    simpa only [refined, protectedRefinement, rho, positive] using
      track.accurate current rho positive
  exact Winding.Box.ProtectedBoundary.strictly_inside_protectedBoundary
    degreePositive current.clearance current.proper refined.proper
      (protectedRefinement_refines track current) refined.raw.rawWinding_ne
      diagonal

end Purelib.RootIsolation.Track.Protected

end
