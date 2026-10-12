module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Readings.UniformPreparedRequests

import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
public import Purelib.Riemann.Paths.PreparedPrimitivePathArea
import Purelib.Tactic.Ring

public section

/-!
# Area comparison across all retained parents of a prepared side

The original-parent count is paid separately from every parent's actual
child count. Both internal areas and the polygon of parent totals remain.
-/

namespace Purelib.Riemann.Readings.PreparedPrimitiveSideArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {target : Coordinate}

open Purelib.Riemann.Paths.PreparedPrimitivePathArea in
/-- Retain paired primitive and model increment blocks for every original requested parent.

Each block follows its own actual child list, while the outer list preserves the original parent grouping. -/
@[expose] def areaBlocks : {parents : List (CenteredEdge curve differential)} → RequestedParents count target parents →
    List (List Gaussian × List Gaussian)
  | _, .nil => []
  | _, .cons head tail => ((LocalRequest.areaPairs head).map Prod.fst, (LocalRequest.areaPairs head).map Prod.snd) ::
    (areaBlocks tail)

/-- There is exactly one paired increment block for every original parent. -/
theorem areaBlocks_length {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents) :
    (areaBlocks requests).length = parents.length := by
  induction requests with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann in
open Purelib.Riemann.Paths.PreparedPrimitivePathArea in
open Purelib.Riemann.Readings.UniformPreparedRequests in
/-- Flattening the model blocks gives the actual retained child-model increments. -/
theorem areaBlocks_right {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents) :
    ((areaBlocks requests).map Prod.snd).flatten = Paths.PathArea.increments (PathModel.mk (requests.blocks.children.map
      CenteredEdge.model)) := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      simp only [areaBlocks, List.map_cons, List.flatten_cons,
        LocalRequest.areaPairs_right, ih,
        RequestedParents.blocks,
        DirectBlockRefinement.children, Purelib.Data.List.Map.map_append, Paths.PathArea.increments, -eq_self,
          -iff_self]
      rfl

open Purelib.Data.Gaussian.Norm.Sum.Basic in
open Purelib.Integration in
open Purelib.Riemann.Paths.PreparedPrimitivePathArea in
open Purelib.Riemann.Readings.UniformPreparedRequests in
/-- Flattening the primitive blocks preserves the total of the retained parent-request increments. -/
theorem areaBlocks_left_total {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count
  target parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((areaBlocks requests).map Prod.fst).flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      simp only [areaBlocks, List.map_cons, List.flatten_cons, Path.IncrementArea.sum_append,
        LocalRequest.areaPairs_left_total,
        ih, RequestedParents.increments, Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
      rfl

open Purelib.Data.Gaussian.Norm.Sum.Basic in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Riemann.Paths.PreparedPrimitivePathArea in
/-- Each retained parent block has certified area, total-error and total-magnitude bounds.

The positive primitive tolerance, nonnegative physical density, parent movement ceiling and actual child-sample bounds
pay these four estimates for the same block. -/
private theorem bounds {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents)
    (positive : 0 < target) {density distance : Coordinate} (densityNonnegative : 0 ≤ density)
    (movements : ∀ parent ∈ parents, movement parent ≤ distance)
    (samples : ∀ child ∈ requests.blocks.children, normSq child.model.integralSample ≤ density *
      child.edge.pointMovement) :
    ∀ pair ∈ (areaBlocks requests),
      normSq (Path.IncrementArea.pathArea pair.1 - Path.IncrementArea.pathArea pair.2) ≤ 32 * target * (density *
        distance + target) ∧
      normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤
        target ∧
      normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 * (density * distance + target) ∧
      normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 * (density * distance + target) := by
  induction requests with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro pair member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have headBounds := (LocalRequest.prepared_area_bounds head) positive densityNonnegative
          (fun child found => samples child (List.mem_append_left _ found))
        have densityLe := add_le_add
          (Arithmetic.mul_le_mul_of_nonneg_left_direct (movements _ (List.mem_cons_self ..)) densityNonnegative)
          (le_rfl (a := target))
        have totalLe := Arithmetic.mul_le_mul_of_nonneg_left_direct densityLe (show (0 : Coordinate) ≤ 2 by decide)
        exact ⟨headBounds.1.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct densityLe
          (Arithmetic.mul_nonneg_direct (by decide +kernel) positive.le)), headBounds.2.1,
          headBounds.2.2.1.trans totalLe, headBounds.2.2.2.trans totalLe⟩
      · exact ih (fun parent found => movements parent (List.mem_cons_of_mem _ found))
          (fun child found => samples child (List.mem_append_right _ found)) pair member

open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann in
/-- Bound the full prepared-side area error with separate internal and parent-polygon contributions.

The original parent count is charged independently of each parent's actual child count. Movement and child-sample bounds
retain the exact primitive and model increment blocks. -/
theorem area_error {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target parents)
    (positive : 0 < target) {density distance : Coordinate} (densityNonnegative : 0 ≤ density) (distanceNonnegative : 0
      ≤ distance)
    (movements : ∀ parent ∈ parents, movement parent ≤ distance)
    (samples : ∀ child ∈ requests.blocks.children, normSq child.model.integralSample ≤ density *
      child.edge.pointMovement) :
    normSq (Path.IncrementArea.pathArea ((areaBlocks requests).map Prod.fst).flatten -
      Path.IncrementArea.pathArea (Paths.PathArea.increments (PathModel.mk (requests.blocks.children.map
        CenteredEdge.model)))) ≤
        64 * ((parents.length : Coordinate) ^ 2 * target) * (density * distance + target) +
          64 * ((parents.length : Coordinate) ^ 4 * target) * (density * distance + target) := by
  rw [← areaBlocks_right requests]
  have bounded := (bounds requests) positive densityNonnegative movements samples
  have estimate := Path.IncrementAreaComparison.blocks_area_difference_bound (areaBlocks requests) positive.le
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 2)
      (add_nonneg (Arithmetic.mul_nonneg_direct densityNonnegative distanceNonnegative) positive.le))
    (fun pair member => by
      have scalar := (bounded pair member).1
      simpa only [Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar)
    (fun pair member => by
      have scalar := (bounded pair member).2.1
      simpa only [Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar)
    (fun pair member => by
      have scalar := (bounded pair member).2.2.1
      simpa only [Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar)
    (fun pair member => by
      have scalar := (bounded pair member).2.2.2
      simpa only [Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar)
  rw [areaBlocks_length requests] at estimate
  simp only [Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
  exact estimate.trans_eq (by ring1)

open Purelib.Approximation.Rational.Geometric in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann in
/-- Pay both levels of prepared-side area subdivision with a uniform accuracy bound.

The parent count is the actual dyadic count, parent movement has matching quarter-radius decay, and the primitive target
pays the squared parent count. Physical density and polynomial accuracy remain independent inputs. -/
theorem dyadic_area_error {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count target
  parents)
    (positive : 0 < target) {accuracy density distance : Coordinate} (accuracyPositive : 0 < accuracy)
    (densityNonnegative : 0 ≤ density) (distanceNonnegative : 0 ≤ distance) (depth : Nat)
    (countEq : parents.length = 2 ^ depth) (targetLe : target ≤ accuracy)
    (countPaid : (parents.length : Coordinate) ^ 2 * target ≤ accuracy)
    (movements : ∀ parent ∈ parents, movement parent ≤ Basic.quarterRadius distance depth)
    (samples : ∀ child ∈ requests.blocks.children, normSq child.model.integralSample ≤ density *
      child.edge.pointMovement) :
    normSq (Path.IncrementArea.pathArea ((areaBlocks requests).map Prod.fst).flatten -
      Path.IncrementArea.pathArea (Paths.PathArea.increments (PathModel.mk (requests.blocks.children.map
        CenteredEdge.model)))) ≤
        128 * accuracy * (density * distance + accuracy) := by
  have firstBound : density * Basic.quarterRadius distance depth + target ≤ density * distance + accuracy :=
    add_le_add (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Basic.quarterRadius_le_scale distanceNonnegative depth) densityNonnegative) targetLe
  have firstNonnegative : 0 ≤ density * Basic.quarterRadius distance depth + target :=
    add_nonneg (Arithmetic.mul_nonneg_direct densityNonnegative (Basic.quarterRadius_nonneg distanceNonnegative depth))
      positive.le
  have countDensity : (parents.length : Coordinate) ^ 2 * (density * Basic.quarterRadius distance depth + target) ≤
      density * distance + accuracy := by
    calc
      _ = density * (((parents.length : Coordinate) * ((parents.length : Coordinate) * Basic.quarterRadius distance
        depth))) +
        (parents.length : Coordinate) ^ 2 * target := by ring1
      _ = density * distance + (parents.length : Coordinate) ^ 2 * target := by
        rw [countEq, DyadicCount.dyadic_count_cancel]
      _ ≤ _ := add_le_add le_rfl countPaid
  have internal := Arithmetic.mul_le_mul_direct countPaid firstBound firstNonnegative accuracyPositive.le
  have polygon := Arithmetic.mul_le_mul_direct countPaid countDensity
    (Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct _) firstNonnegative) accuracyPositive.le
  have bounded := (area_error requests) positive densityNonnegative (Basic.quarterRadius_nonneg distanceNonnegative
    depth) movements samples
  apply bounded.trans
  calc
    _ = 64 * (((parents.length : Coordinate) ^ 2 * target) * (density * Basic.quarterRadius distance depth + target)) +
      64 * (((parents.length : Coordinate) ^ 2 * target) *
        ((parents.length : Coordinate) ^ 2 * (density * Basic.quarterRadius distance depth + target))) := by ring1
    _ ≤ 64 * (accuracy * (density * distance + accuracy)) + 64 * (accuracy * (density * distance + accuracy)) :=
      add_le_add (Arithmetic.mul_le_mul_of_nonneg_left_direct internal (by decide +kernel))
        (Arithmetic.mul_le_mul_of_nonneg_left_direct polygon (by decide +kernel))
    _ = _ := by ring1

end Purelib.Riemann.Readings.PreparedPrimitiveSideArea
