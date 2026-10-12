module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Region.Sum
public import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Separation.Basic

open Purelib.RootIsolation.Exact.State (IsolationState)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Exact isolation steps from checked extraction checkpoints

Rebuild the numerical fields of an isolation state and retain the original
track constructors.  Equality is to the canonical step, not to an arbitrary
equivalent root family.  Proof-only references to that step disappear from
the executable replay.  This imports only existing finite isolation modules.
-/

namespace Purelib.RootIsolation.Exact.State.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}

set_option genInjectivity false in
/-- Cache every executable field; all other isolation-state fields are
proofs and can be transported without running the original constructor. -/
structure StateCache (original : IsolationState p ambient)
  where
  /-- The cached original support box. -/ support : Box
  /-- The cached support equals the original isolation support. -/ support_eq : support = original.support
  /-- The cached original finite region list. -/ regions : List (Clearance.Box.Region.ClearRegion p ambient)
  /-- The cached regions equal the original remaining region list. -/ regions_eq : regions = original.regions
  /-- The cached original finite track list. -/ tracks : List (Track.Basic.WindingOneTrack p
    ambient)
  /-- The cached tracks equal the original extracted track list. -/ tracks_eq : tracks = original.tracks

constructive_injectivity StateCache

/-- Restore the exact original isolation state from its retained executable fields.

Only proof transport is performed; the support, region list and track list come directly from the cache. -/
@[expose] def StateCache.restore {original : IsolationState
  p ambient} (cache : StateCache original) :
    IsolationState p ambient where
  support := cache.support
  supportRefinesAmbient := by rw [cache.support_eq]; exact original.supportRefinesAmbient
  regions := cache.regions
  regionsPairwise := by rw [cache.regions_eq]; exact original.regionsPairwise
  tracks := cache.tracks
  tracksPairwise := by rw [cache.tracks_eq]; exact original.tracksPairwise
  tracksAvoidRegions := by
    rw [cache.tracks_eq, cache.regions_eq]
    exact original.tracksAvoidRegions
  covers := by
    rw [cache.support_eq, cache.tracks_eq, cache.regions_eq]
    exact original.covers

/-- Restoring the checked executable cache returns the original isolation state exactly. -/
theorem StateCache.restore_eq {original : IsolationState p
  ambient} (cache : StateCache original) :
    cache.restore = original := by
  rcases cache with ⟨support, supportEq, regions, regionsEq, tracks, tracksEq⟩
  cases supportEq
  cases regionsEq
  cases tracksEq
  cases original
  rfl

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
end Runs
end Purelib.RootIsolation.Exact.State.Replay

end
