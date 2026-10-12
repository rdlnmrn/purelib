module
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
public import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache

open Purelib.RootIsolation.SquareRoot.Replay

section
@[expose] public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay (Ready)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Paths.PreparedClearPathModels hiding Endpoint

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Riemann.Transport.PreparedDirectRefinementReplay (AllReady)

/-- A replay-ready starting root owner makes every canonical centered subdivision parent replay-ready.

Readiness is propagated along the original dependent spine through its cached root observation and exact advancing
owner. -/
theorem
  subdivision
  (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))}
      (spine : Subdivision segment within left owner), Ready owner →
      AllReady (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet spine).parents
  | _, _, .stop _ _, _ => True.intro
  | _, _, .next current owner request cached ordered small remaining, ready => by
      rw [CenteredPathChain.dataOfCanonicalSubdivision_next]
      exact ⟨QuadraticTrackReplay.cached segment current owner request ready cached,
        Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness.subdivision
          curve source segment within sheet remaining
          (QuadraticTrackReplay.advance segment current owner request ready within small)⟩

/-- A complete prepared segment preserves replay readiness in its canonical centered parent list. -/
theorem
  completeSegment
  (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) (ready : Ready owner) :
    AllReady (CenteredPathChain.dataOfCompleteSegment curve source sheet prepared).parents :=
  Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness.subdivision curve source
    segment within sheet prepared.subdivision (PreparedTrackReplay.ownerAtStart segment owner ready)

/-- Replay readiness propagates through all retained segments of a prepared path. -/
theorem
  preparedPath
  (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} (sheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (prepared : PreparedPath path owner),
        Ready owner →
      AllReady (CenteredPathChain.ofPreparedPath curve source sheet prepared).parents
  | _, _, _, _, .nil _ _, _ => True.intro
  | _, _, _, _, .cons _ _ _ _ head tail, ready =>
      (Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness.completeSegment
        curve source sheet head ready).append

          (preparedPath
          curve source sheet tail (PreparedTrackReplay.finishOwner head ready))

/-- The centered parents extracted from a cached dyadic bank retain replay readiness from its original starting owner.
-/
theorem bank
  (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    (sheet : Fin 2) (bank : PreparedPath.DyadicBank depth diameter positive path owner) (ready : Ready owner) :
    AllReady (CenteredPathChain.ofDyadicBank curve source sheet (.certified (DyadicBank.cache bank))).parents :=
  Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness.preparedPath curve source
    sheet (DyadicBank.cache bank).prepared ready
end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness

end
