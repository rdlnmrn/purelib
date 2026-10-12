module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
public import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements

section

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Rat

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState

open Purelib.Riemann.Transport

section
@[expose] public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Restoration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedDirectMeshes)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CheckedSelection MeshAllowanceChecks)

open Purelib.Riemann.Transport.PreparedDirectRefinementReplay
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)

set_option genInjectivity false in
/-- A completed step retains both its original-source equation and the seed laws needed to resume its children at the
next requested refinement. -/
structure RestoredStep {root : Gaussian.Name.Basic.Named}
    (current : PreparedRefinementRootEndpoints.RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained root-closed refinement step for the exact current state and targets. -/ value : RootClosedState.Step
    current targets target
  /-- The restored step equals the prescribed root-closed acquisition computation. -/ equal : value = Step.acquire
    current targets target positive
  /-- Every parent of the retained next state is replay-ready. -/ ready : AllReady value.next.state.parents
  /-- The deferred recipe histories for the exact retained next-state parent list. -/ histories :
    PreparedDeferredRecipeReplay.Histories value.next.state.parents

constructive_injectivity RestoredStep

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Restoration

end

end
