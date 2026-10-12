module
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedDirectRefinementReplay.Readiness
public import Purelib.Riemann.Topology.PreparedCycleReplay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Topology.PreparedCycleModels
public import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

section
public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay (Ready)
open Purelib.Riemann.Topology.PreparedCycleReplay

variable {genus : Nat} (curve : HyperellipticCurve genus) (source :
  Differential genus)

/-- Seed laws are obtained from the restored original endpoint families; no per-edge recipe, success witness or new
geometric assumption is supplied. -/
@[expose] def CycleReady :
  PreparedCycleModels.PreparedCycleData curve → Prop
  | .bridge data => Ready data.forwardOwner ∧ Ready data.backwardOwner
  | .finiteCut data => Ready data.forwardOwner ∧ Ready data.rightBoundaryOwner ∧
      Ready data.backwardOwner ∧ Ready data.leftBoundaryOwner
end Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay (Ready)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Paths.PreparedClearPathModels hiding Endpoint

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

open Purelib.Riemann.Transport.PreparedDirectRefinementReplay (AllReady)

/-- Replay-ready original cycle endpoint owners make all canonical cycle parents replay-ready. -/
theorem cycle (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) (ready :
      CycleReady curve data) :
    AllReady (PreparedSwitchedRefinements.cycleState curve source data).parents := by
  rw [← PreparedCycleReplay.CycleParts.canonical_state curve source data]
  cases data with
  | bridge data =>
      change AllReady ((_ ++ ([] ++ (_ ++ []))) : List (CenteredEdge curve source))
      simpa only [List.nil_append, Purelib.Data.List.Append.append_nil] using
        (Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 0 data.forwardChecked
          ready.1).append (Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 1
          data.backwardChecked ready.2)
  | finiteCut data =>
      change AllReady ((_ ++ (_ ++ ([] ++ (_ ++ (_ ++ []))))) : List (CenteredEdge curve source))
      simpa only [List.nil_append, Purelib.Data.List.Append.append_nil] using
        (Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 0 data.forwardChecked
          ready.1).append
          ((Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 0 data.rightBoundaryChecked
            ready.2.1).append
            ((Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 1 data.backwardChecked
              ready.2.2.1).append
              (Preparation.Replay.PreparedDirectRefinementReplay.Readiness.bank curve source 1 data.leftBoundaryChecked
                ready.2.2.2)))

/-- Restoring the exact cached cycle preserves replay readiness of its original parent list. -/
theorem restored (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) (source : Differentials.Basic.Differential genus)
    {data : PreparedCycleModels.PreparedCycleData curve} (ready :
      CycleReady curve data)
    (cached : PreparedCycleReplay.CachedCycle curve source data) : AllReady cached.restore.parents := by
  rw [cached.restore_eq, PreparedSwitchedRefinements.compactCycleState_parents]
  exact cycle curve source data ready

end Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness

end
