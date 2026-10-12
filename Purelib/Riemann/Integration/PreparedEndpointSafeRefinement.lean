module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.PreparedSheetContinuation

public import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# Total selection of query-safe direct refinements

The existing direct child block supplies the actual integration geometry.
A cached coarse root-box budget supports finite operational comparisons along
each child without imposing a further subdivision depth on that geometry.
-/

namespace Purelib.Riemann.Integration.PreparedEndpointSafeRefinement

open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectParentBlock directParentBlockAtDepth)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- An original direct parent refinement block together with its retained root-query comparison budget.

The block and budget share the exact original centered edge, preserving both the child construction and the parent root
owner. -/
structure EndpointSafeBlock (parent : CenteredEdge curve differential) where
  /-- The retained root-query comparison budget of the original parent edge. -/ budget : ParentBudget parent.edge
  /-- The retained direct parent block with its original child list and construction certificates. -/ block :
    DirectParentBlock parent

constructive_injectivity EndpointSafeBlock

namespace EndpointSafeBlock

open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- Construct an endpoint-safe direct parent block at the sufficient dyadic depth for the positive diameter request.

The original edge parameters are strictly ordered. The retained parent budget accompanies the exact ordinary subdivision
depth and original direct block construction. -/
def total (parent : CenteredEdge curve differential)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (diameter : Fraction.Rational) (positive : 0 < diameter) : EndpointSafeBlock parent :=
  let budget := ParentBudget.acquire parent.edge
  let depth := PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
    parent.edge.segment parent.edge.left parent.edge.request.endpoint diameter
  let block := directParentBlockAtDepth parent proper diameter positive depth le_rfl
  ⟨budget, block⟩

end EndpointSafeBlock

end Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
