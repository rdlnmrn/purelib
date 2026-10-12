module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Enclosure.Sector.Large
import Purelib.Approximation.Gaussian.Enclosure.Sector.Safe
public import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Geometry.Rational.Sector.Eight.Safe
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Geometry.Rational.Sector.Eight

section
@[expose] public section

/-!
# Finite arithmetic output decisions

This module joins progressive finite enclosures to the two overlapping CCL
decisions.  A normalized loop process can always refine once to the uniform
`1/480` squared-error threshold and then emit either a sound unary digit or a
sound redundant sector.  A residual process can always refine once to the
requested padding threshold and then return either a sound small-residual
certificate or positive apartness for affine inversion.

Both constructions are ordinary finite function calls.  In particular, the
residual construction does not ask whether the represented result is exactly
zero.  Repeating it at successively smaller finite padding targets is the
constructive non-return route for an opaque exact rational result.
-/

namespace Purelib.Approximation.Gaussian.Process.Sector

set_option genInjectivity false in
/-- A progressive process already in a loop chart. The centre lower bound is finite state data, normally obtained from
radial scaling or the strict margin of the preceding safe inversion. -/
structure LoopProcess where
  /-- The original stateful finite enclosure process. -/ process : Approximation.Gaussian.Process
  /-- Every retained process state has ball centre squared norm at least one. -/ center_normalized : ∀ (state :
    process.State),
    1 ≤ Data.Gaussian.Norm.Basic.normSq (process.ball state).center

constructive_injectivity LoopProcess

namespace LoopProcess

/-- The one finite refinement used for a redundant output decision. -/
def refinedState (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State) :
    loop.process.State :=
  loop.process.refine state
    Budget.uniformRadiusSq
    Budget.uniformRadiusSq_pos

/-- Every possible reading after the loop refinement was possible at the original state. -/
theorem refined_persists (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State)
    {value : Canonical}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    loop.process.Possible state value :=
  loop.process.refine_persists state _ _ possible

/-- The refined loop state meets the uniform redundant-output squared-radius threshold. -/
theorem refined_accurate (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State) :
    (loop.process.ball (loop.refinedState state)).radiusSq <
      Budget.uniformRadiusSq :=
  loop.process.accurate state _ _

/-- Total bounded unary-or-sector decision at one normalized loop state. -/
def decide (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State) :
    Approximation.Gaussian.Enclosure.Sector.Decision
      (loop.process.ball (loop.refinedState state)) :=
  Decision.decide _
    (loop.center_normalized (loop.refinedState state))
    (loop.refined_accurate state)

/-- The unary outcome is sound for every finite possibility at the refined state. -/
theorem unary_sound (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State)
    (certificate : Large.UnaryBall
      (loop.process.ball (loop.refinedState state)))
    {value : Canonical}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    2 < Data.Gaussian.Norm.Basic.normSq value :=
  Large.normSq_gt_two_of_contains certificate
    (loop.process.possible_inside possible)

/-- The sector outcome is sound for every finite possibility at the refined state. -/
theorem sector_sound (loop :
  Approximation.Gaussian.Process.Sector.LoopProcess) (state : loop.process.State)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector)
    (certificate : Safe.SafeBall sector
      (loop.process.ball (loop.refinedState state)))
    {value : Canonical}
    (possible : loop.process.Possible (loop.refinedState state) value) :
    Geometry.Rational.Sector.Eight.Safe sector value :=
  Safe.safe_of_contains certificate
    (loop.process.possible_inside possible)

end LoopProcess
end Purelib.Approximation.Gaussian.Process.Sector

end
