module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay

open Purelib.Polynomial

open Purelib

@[expose] public section

/-! The original checked-first-attempt law follows the stored subdivision,
including the terminal owner passed to the next displayed path segment. -/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay

open QuadraticSampleReplay (Gaussian Box)
open QuadraticTrackReplay (Ready advance)

open Purelib.Riemann.Branches
open Purelib.Riemann
open Purelib.Riemann.Paths

/-- Transport readiness along equality of the owner's exact quadratic parameter. -/
theorem castOwner {source target : Gaussian} (equal : source = target)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner source) (ready : Ready owner) :
    Ready (cast (congrArg Riemann.Topology.SquareRootContinuationChain.Owner equal) owner) := by
  cases equal
  exact ready

/-- The owner at the end of the original prepared subdivision is ready.

Induct over the retained subdivision constructors and preserve the exact terminal owner in each branch. -/
theorem terminal {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {left : Riemann.Branches.PreparedSheetContinuation.Endpoint}
    {owner : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Riemann.Branches.PreparedSheetContinuation.Subdivision segment within left owner) :
    Ready owner → Ready subdivision.terminalOwner := by
  induction subdivision with
  | stop _ _ => exact id
  | next current owner request cached ordered small remaining ih =>
      intro ready
      exact ih (advance segment current owner request ready within small)

/-- The retained owner at a prepared track's start satisfies the checked first-attempt equation. -/
theorem ownerAtStart {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval start)) (ready : Ready owner) :
    Ready (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner) := open Purelib.RootIsolation in by
  have lift {source target : Gaussian} (equal : source = target)
      (retained : Riemann.Topology.SquareRootContinuationChain.Owner source)
      (evidence : Ready retained) :
      Ready (SquareRoot.Owner.Transport.castOwnerParameter equal retained) := by
    cases equal
    exact evidence
  unfold Riemann.Paths.PreparedClearPathModels.ownerAtStart
  exact lift (congrArg polynomial.eval segment.pointAt_zero.symm) owner ready

open Purelib.RootIsolation in
/-- The exact finish owner of the prepared track satisfies the checked first-attempt equation. -/
theorem finishOwner {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval start)}
    (prepared : Riemann.Paths.PreparedClearPathModels.CompleteSegment segment within owner) (ready : Ready owner) :
    Ready prepared.finishOwner := open Purelib.RootIsolation in by
  have result := SquareRoot.Replay.PreparedTrackReplay.terminal prepared.subdivision
    (SquareRoot.Replay.PreparedTrackReplay.ownerAtStart segment owner ready)
  have lift {source target : Gaussian} (equal : source = target)
      (retained : Riemann.Topology.SquareRootContinuationChain.Owner source)
      (evidence : Ready retained) :
      Ready (SquareRoot.Owner.Transport.castOwnerParameter equal retained) := by
    cases equal
    exact evidence
  unfold Riemann.Paths.PreparedClearPathModels.CompleteSegment.finishOwner
    Riemann.Paths.PreparedClearPathModels.CompleteSegment.terminalOwner
  exact lift (congrArg polynomial.eval prepared.finish_eq)
    prepared.subdivision.terminalOwner result

end Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay
