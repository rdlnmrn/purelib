module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.Run
import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Exact.Step

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.RootIsolation.Exact.Run (RunResult)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.Run.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
section Steps

variable (state : Exact.State.IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
end Steps

section Runs

variable {state : Exact.State.IsolationState p ambient}

/-- Assemble a run from its checked first step and restored tail. -/
def join (first : Exact.Step.StepResult state) (steps : Nat) (tail :
  RunResult first.next steps) :
    RunResult state (steps + 1) where
  final := tail.final
  support_final := tail.support_final.trans first.support_next
  totalRaw_final := tail.totalRaw_final
  tracks_length_final := by
    rw [tail.tracks_length_final, first.tracks_length_next]
    omega

/-- Joining the checked original first step and restored original tail equals the complete canonical run. -/
theorem join_eq (steps : Nat) (total : Winding.Box.Region.Sum.totalRaw
  state.regions = (4 : Int) * (steps + 1))
    (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
    (first : Exact.Step.StepResult state)
    (firstEq : first = Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive)
    (nextTotal : Winding.Box.Region.Sum.totalRaw first.next.regions = (4 : Int) * steps)
    (tail : RunResult first.next steps)
    (tailEq : tail = Exact.Run.run degreeAtLeastTwo squarefree elimination steps first.next nextTotal) :
    join first steps tail = Exact.Run.run degreeAtLeastTwo squarefree elimination (steps + 1) state
      total := by
  cases firstEq
  cases tailEq
  rfl
end Runs
end Purelib.RootIsolation.Exact.Run.Replay

end
