module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Basic
public import Purelib.RootIsolation.Exact.Build
import Purelib.RootIsolation.Exact.Run
import Purelib.RootIsolation.Exact.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Separation.Basic

open Purelib.RootIsolation.Exact.State (IsolationState)

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

namespace Purelib.RootIsolation.Exact.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
  Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
section Steps

variable (state : IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions)
end Steps

section Runs

variable {state : IsolationState p ambient}

/-- Restore the full degree-many output, including the exact ordered tracks
and remainder partition used by ownership, from the checked complete run. -/
def output (initial : Clearance.Box.Region.ClearRegion p ambient) (count :
  Nat)
    (result : Exact.Run.RunResult (IsolationState.initial initial) count) : Exact.Basic.Output p ambient
      count where
  support := initial.box
  support_refinesAmbient := initial.refinesAmbient
  tracks := result.final.tracks
  tracks_length := by
    rw [result.tracks_length_final]
    exact Nat.zero_add count
  tracks_pairwise := result.final.tracksPairwise
  remainder := result.final.regions
  remainder_pairwise := result.final.regionsPairwise
  remainder_rawWinding_zero := by
    intro region member
    apply Winding.Box.Region.Sum.rawWinding_eq_zero_of_mem_totalRaw_eq_zero result.final.regions ?_
      result.totalRaw_final member
    intro region _member
    exact Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative degreeAtLeastTwo
      squarefree elimination
      region.refinesAmbient region.proper region.clearance
  tracks_avoid_remainder := result.final.tracksAvoidRegions
  partition_covers := by
    intro z inside
    apply result.final.covers
    rw [result.support_final]
    exact inside

/-- Assembling the retained original complete run reproduces the canonical isolation output exactly. -/
theorem output_eq (initial : Clearance.Box.Region.ClearRegion p ambient)
  (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (total : Winding.Box.Region.Sum.totalRaw (IsolationState.initial initial).regions = (4 : Int) * count)
    (result : Exact.Run.RunResult (IsolationState.initial initial) count)
    (resultEq : result = Exact.Run.run degreeAtLeastTwo squarefree elimination count
      (IsolationState.initial initial) total) :
    output degreeAtLeastTwo squarefree elimination initial count result =
      Exact.Build.isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw := by
  cases resultEq
  rfl

end Runs
end Purelib.RootIsolation.Exact.Replay

end
