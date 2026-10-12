module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements
public import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Riemann.Transport

section
public section

/-!
Disk-backed centring of the original prepared bank spines.  Each callback
receives the complete original-source equation, not just matching numbers.
The explicit stored-spine eliminators retain the owners already computed by
preparation instead of rebuilding their canonical indices during execution.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration

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
section Source

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (proposedRootBits familyForecast checkedDirectSelection
  uniformSelection accurateDirectRefinement)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState)

set_option genInjectivity false in
/-- A restored source-refinement step tied to the original refinement computation.

The retained state equals the prescribed accurate refinement and carries replay readiness and deferred histories for its
exact parent list. -/
structure
  RestoredStep
  (current : DirectSwitchedState curve source)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained source-refinement state returned by restoration. -/ value : DirectSwitchedState curve source
  /-- The restored state equals refinement by the prescribed accurate direct refinement. -/ equal : value =
    current.refineSource
    (accurateDirectRefinement current.parents current.proper target positive)
  /-- Every parent in the restored state is ready for replay. -/ ready : AllReady value.parents
  /-- The retained deferred recipe histories indexed by the restored parent list. -/ histories :
    PreparedDeferredRecipeReplay.Histories value.parents

constructive_injectivity RestoredStep

end Source

end Purelib.Curves.Hyperelliptic.Integration.Preparation.Replay.PreparedSourceRefinementReplay.Restoration

end
