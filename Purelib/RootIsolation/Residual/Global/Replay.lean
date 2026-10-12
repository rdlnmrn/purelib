module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.RootIsolation.Exact.Ownership.Replay
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
import Purelib.RootIsolation.Newton.Restart.Anchored.Seed
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
public import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Newton.Restart.Seed.Track
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Ownership.Basic
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring

open Purelib.RootIsolation.Newton.Restart (Seed)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the canonical residual assignment from its retained owner refinement. -/
namespace Purelib.RootIsolation.Residual.Global.Replay

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (input :
  RootIsolation.FTA.Squarefree.Input p)
  (sample : Gaussian.Basic.Canonical) (inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains sample)
  {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon)
  (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval sample) < Residual.Global.Assignment.insideResidualTarget
    input epsilon)

/-- Reconstruct the original anchored localization seed from the supplied sample and strict residual bound. -/
def seed :=
  let parent := Residual.Global.Assignment.largeSquareProtectedAmbient input.degreePositive
  let localized := Newton.Restart.Uniform.Anchored.uniform_residual_strict_and_anchored
    input.squarefree parent sample inside epsilonPositive residualSmall
  Newton.Restart.Anchored.Seed.seedOfResidual input.squarefree input.elimination parent sample
    localized.1 epsilonPositive localized.2

/-- Construct the original shrinking track of the reconstructed anchored seed. -/
def track := (seed input sample inside
  epsilonPositive residualSmall).track input.degreeAtLeastTwo

/-- The retained ownership replay certificate for the exact original isolation and reconstructed track. -/
abbrev Refined := Exact.Ownership.Replay.Refined input.isolation
  (track input sample inside epsilonPositive residualSmall)

/-- Restore the original localized assignment from its retained ownership replay certificate.

Keep the same seed radius, state, track, isolation owner and quantitative bounds while reusing the supplied ownership
evidence. -/
def restore (saved : Refined input sample
  inside epsilonPositive residualSmall) :
    Residual.Global.Assignment.AssignedResult input sample epsilon := open Purelib.Geometry.Rational in by
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
    simpa only [state, Seed.state,
      Seed.band] using bandDiagonal.trans scaled
  have supported : track.initial.box.Refines input.isolation.support := by
    change state.box.Refines (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
    exact state.refinesAmbient
  let owner := Exact.Ownership.Replay.restore input.degreeAtLeastTwo input.squarefree
    input.elimination input.isolation track supported saved
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
          Seed.state,
          Seed.band,
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
            Seed.state,
            Seed.band,
            Newton.Restart.Anchored.Seed.seedOfResidual,
            Newton.Restart.Anchored.Basic.AnchoredInput.seed,
            Newton.Restart.Anchored.Prepare.anchoredInputOfResidual,
            Box.Square.Anchored.anchoredSquare_anchor] using distance
        have scaled : 18 * seed.radius ^ 2 ≤ 18 * epsilon ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusSquareLe (by decide)
        exact (Geometry.Projective.Chordal.Affine.affineChordalSq_le_normSq sample z).trans
          (distanceFromSample.trans scaled) }

/-- Restoring the retained ownership certificate yields exactly the original global residual assignment. -/
theorem restore_eq (saved : Refined input
  sample inside epsilonPositive residualSmall) :
    restore input sample inside epsilonPositive residualSmall saved =
      Residual.Global.Assignment.assignInside input sample inside epsilonPositive residualSmall := by
  rcases saved with ⟨state, same⟩
  cases same
  rfl

end Purelib.RootIsolation.Residual.Global.Replay

end
