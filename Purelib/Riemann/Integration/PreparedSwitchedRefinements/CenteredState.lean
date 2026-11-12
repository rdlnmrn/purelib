module

public import Purelib.Riemann.Integration.PreparedSwitchedRefinements.Centered
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-! # Switched refinement states of original centered chains

The existing centered chain and its proper-parent evidence provide the
state. No stationary switches are inserted. Each initial differential
allowance is the exact allowance of those same recast parents.
-/

public section

namespace Purelib.Riemann.Integration.PreparedSwitchedRefinements.DirectSwitchedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Rat.Fraction

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}

/-- Construct a switch-free refinement state from the exact original centered parents and their properness.

The endpoint and parent fields reduce to the supplied owners so root chains
and geometric comparisons retain those literal indices. Initial allowance
bounds are the same finite recast models' exact allowances.
-/
@[expose] def ofCenteredPathChain
    {parents : List (CenteredEdge curve source)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (proper : AllParentsProper parents) : DirectSwitchedState curve source where
  start := start
  finish := finish
  parents := parents
  proper := proper
  chain := SwitchedPathChain.ofCenteredPathChain chain
  initialAllowanceBound := fun differential =>
    (PathModel.mk ((parents.map (recastCenteredEdge differential)).map CenteredEdge.model)).aggregateAllowance
  initialAllowance_le := fun _ => Order.Basic.le_refl _

/-- Reading the state preserves the complete original centered path in its retained order. -/
theorem ofCenteredPathChain_path
    {parents : List (CenteredEdge curve source)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (proper : AllParentsProper parents) : (ofCenteredPathChain chain proper).path = chain.path :=
  (SwitchedPathChain.centered_path (SwitchedPathChain.ofCenteredPathChain chain)
    (SwitchedPathChain.switchCount_ofCenteredPathChain chain)).symm.trans
    (congrArg (fun original : CenteredPathChain parents (start := start) (finish := finish) => original.path)
      (SwitchedPathChain.centered_ofCentered chain))

/-- The state inserts no stationary sheet changes into the original centered parent chain. -/
theorem ofCenteredPathChain_switchCount
    {parents : List (CenteredEdge curve source)} {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    (proper : AllParentsProper parents) : (ofCenteredPathChain chain proper).chain.switchCount = 0 :=
  SwitchedPathChain.switchCount_ofCenteredPathChain chain

end Purelib.Riemann.Integration.PreparedSwitchedRefinements.DirectSwitchedState

end
