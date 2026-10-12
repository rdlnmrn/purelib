module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths

public import Purelib.Riemann.Integration.PreparedScheduledDepthFloor
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-! The original exterior orientation provides the moving-parent witness
needed by the computed spatial-depth threshold. -/
namespace Purelib.Riemann.Integration.PreparedOrientedDepthFloor

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- A strictly positive original endpoint cross-energy forces positive parent movement. -/
theorem movement_positive_of_oriented (parent : CenteredEdge curve source)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) :
    0 < parent.edge.pointMovement := by
  apply Norm.Basic.normSq_pos
  intro zero
  have equal := Purelib.Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero zero
  have vanishes : AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) = 0 := by
    rw [equal]
    change ((parent.edge.point 0).re * (parent.edge.point 0).im +
      (-(parent.edge.point 0).im) * (parent.edge.point 0).re) / 2 = 0
    rw [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  exact (ne_of_gt oriented) vanishes

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Energy in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Positive orientation of a retained initial parent certifies its scheduled dyadic depth floor.

The same original parent supplies the nonzero movement witness, and the previously selected stage threshold controls the
accumulated spatial depth. -/
theorem RootClosedState.depthFloorStage_enough_of_oriented {root : Named}
    (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential genus))
    {parent : CenteredEdge curve source} (member : parent ∈ initial.state.parents)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) (minimum stage : Nat)
    (later : PreparedScheduledDepthFloor.RootClosedState.depthFloorStage initial targets parent minimum ≤ stage + 1) :
    minimum ≤ PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial targets (stage + 1) :=
  PreparedScheduledDepthFloor.RootClosedState.depthFloorStage_enough initial targets member
    (movement_positive_of_oriented parent oriented) minimum stage later

end Purelib.Riemann.Integration.PreparedOrientedDepthFloor
