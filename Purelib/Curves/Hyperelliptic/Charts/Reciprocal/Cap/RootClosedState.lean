module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements.CenteredState
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample

/-! # Root-closed refinement states of the same retained cap boundary

The actual cap endpoint comparisons recover a root chain of the identical
original parents. Its actual terminal-to-initial return closes that chain.
The centered chain is assembled from the given parent records, without
replaying the original preparation or substituting another owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus}

/-- Recover the original parent-root chain from the same retained cap endpoint handoffs.

Every incoming and outgoing comparison is composed with that actual
ParentData's ownership law. No parent, Point or root query is prepared.
-/
def toParentChain :
    {parents : List (Parent curve differential)} → {bank : Bank cap differential count parents} →
      {first last : Named} → RootLinks bank first last → RootChain parents first last
  | [], .nil, _, _, .nil equivalent => .nil equivalent
  | parent :: _, .cons data _remaining, _, _, .cons _ _ entry tail =>
      .cons parent (entry.trans data.first_owner.symm)
        ((toParentChain tail).changeStart data.last_owner)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}

/-- Assemble the exact retained cap parents into the existing switch-free refinement state.

The source and target are the original labelled anchor. The exposed body
preserves the literal parent list and endpoint indices needed by root-chain
and geometric-path consumers; the original preparation is not replayed.
-/
@[expose] def state (closed : Data cap owner differential) :
    DirectSwitchedState (HyperellipticReciprocalCurve.reciprocalCurve curve)
      (HyperellipticReciprocal.reversedDifferential differential) :=
  DirectSwitchedState.ofCenteredPathChain
    (CenteredPathChain.ofParents closed.covered.cache.parents closed.covered.cache.chain)
    closed.covered.cache.proper

/-- The retained state reads the exact original centered path of the same cap parent cache. -/
theorem state_path (closed : Data cap owner differential) :
    (state closed).path =
      (CenteredPathChain.ofParents closed.covered.cache.parents closed.covered.cache.chain).path :=
  DirectSwitchedState.ofCenteredPathChain_path _ _

/-- Construct the existing root-closed state using the same retained bank and its actual returned root.

Lifted endpoint closure and root return remain separate fields. The root
chain is recovered from the actual retained RootLinks, then closed by the
same returned certificate; neither coordinate nor matrix equality replaces
that evidence. Both original degree parities use this same constructor.
-/
def rootClosedState (closed : Data cap owner differential) :
    RootClosedState (HyperellipticReciprocalCurve.reciprocalCurve curve)
      (HyperellipticReciprocal.reversedDifferential differential) (OwnerTraceReadings.ownerName owner) :=
  ⟨state closed, rfl,
    PreparedBankRootChains.RootChain.changeFinish closed.covered.roots.toParentChain closed.returned⟩

/-- The opaque root-closed constructor retains its exact original-parent state. -/
private theorem packaged_rootClosedState_state (closed : Data cap owner differential) :
    (rootClosedState closed).state = state closed := rfl

/-- Root closure retains the whole original-parent state without changing its path, parents or bounds. -/
theorem rootClosedState_state (closed : Data cap owner differential) :
    (rootClosedState closed).state = state closed :=
  packaged_rootClosedState_state closed

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

end
