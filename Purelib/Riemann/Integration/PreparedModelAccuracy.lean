module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Requested coefficient accuracy for existing prepared parents

Only the parent geometry and finite quotient-error coefficients are needed
here. No primitive polynomial is constructed. The actual direct subdivision
and its child-error guarantees are retained for later integration consumers.
-/

namespace Purelib.Riemann.Integration.PreparedModelAccuracy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectParentBlock directParentBlockAtDepth)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement preparedScale preparationDepth)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
abbrev Coordinate := Fraction.Rational

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

set_option genInjectivity false in
open Purelib.Riemann.Readings in
/-- Cached movement and preparation-error scale for the original centered parent.

Both stored scalar equations identify the exact original parent geometry and point/root error coefficients. -/
structure Profile (parent : CenteredEdge curve differential) where
  /-- The cached exact original parent movement. -/ movement : Coordinate
  /-- The cache equals the original centered parent's geometric movement. -/ movement_eq : movement =
    PreparedPrimitiveRequests.movement parent
  /-- The cached original point/root preparation-error scale. -/ scale : Coordinate
  /-- The scale equals the original parent's exact error-coefficient sum. -/ scale_eq : scale = preparedScale parent

constructive_injectivity Profile

namespace Profile

variable {parent : CenteredEdge curve differential}

open Purelib.Riemann.Readings
/-- Cache the original centered parent's exact movement and preparation-error scale. -/
@[expose] def build (parent : CenteredEdge curve differential) : Profile parent :=
  ⟨PreparedPrimitiveRequests.movement parent, rfl, preparedScale parent, rfl⟩

/-- The retained original parent movement cache is nonnegative. -/
theorem movement_nonnegative (profile : Profile parent) : 0 ≤ profile.movement := by
  rw [profile.movement_eq]
  exact PreparedPrimitiveRequests.movement_nonnegative parent

/-- The retained original preparation-error scale is nonnegative. -/
theorem scale_nonnegative (profile : Profile parent) : 0 ≤ profile.scale := by
  rw [profile.scale_eq]
  exact PreparedPrimitiveRequests.preparedScale_nonnegative parent

end Profile

set_option genInjectivity false in
open Purelib.Approximation.Rational in
/-- A positive root diameter and sufficient dyadic depth paying the original model-error target.

The original movement and scale remain separate, and the depth retains the required preparation floor for that exact
diameter. -/
structure Budget (movement scale : Coordinate) (preparationDepth : Coordinate → Nat) (target : Coordinate) where
  /-- The retained positive root-diameter request. -/ diameter : Coordinate
  /-- The original requested root diameter is strictly positive. -/ diameterPositive : 0 < diameter
  /-- The retained original dyadic subdivision depth. -/ depth : Nat
  /-- The selected depth meets the exact preparation floor for the retained diameter. -/ prepared : preparationDepth
    diameter ≤ depth
  /-- The original scaled spatial-plus-root error is at most the retained target. -/ paid : scale *
    (Geometric.Basic.quarterRadius movement depth + diameter) ≤ target

constructive_injectivity Budget

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Choose a retained root diameter and dyadic depth paying the original model-error target.

A weighted half-target allowance determines the diameter, and the geometric search begins at its exact preparation
floor. The spatial and root terms each consume at most half the original target. -/
@[expose] def Budget.build (movement scale : Coordinate) (preparationDepth : Coordinate → Nat)
    (movementNonnegative : 0 ≤ movement) (scaleNonnegative : 0 ≤ scale)
    {target : Coordinate} (positive : 0 < target) : Budget movement scale preparationDepth target := by
  let diameter := Budget.Weighted.allowance (target / 2) scale
  have halfPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Coordinate) < 2)
  have diameterPositive : 0 < diameter := Budget.Weighted.allowance_positive halfPositive scaleNonnegative
  let floor := preparationDepth diameter
  let depth := Geometric.Search.firstQuarterBelow movement floor diameter
  have spatial : Geometric.Basic.quarterRadius movement depth ≤ diameter :=
    (Geometric.Search.firstQuarterBelow_accurate movement movementNonnegative floor diameter diameterPositive).le
  have halfPaid : scale * diameter ≤ target / 2 :=
    Budget.Weighted.mul_allowance_le halfPositive.le scaleNonnegative
  exact
    { diameter := diameter
      diameterPositive := diameterPositive
      depth := depth
      prepared := Geometric.Search.firstQuarterBelow_ge movement floor diameter
      paid := by
        calc
          _ ≤ scale * (diameter + diameter) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add spatial le_rfl) scaleNonnegative
          _ = scale * diameter + scale * diameter := _root_.mul_add _ _ _
          _ ≤ target / 2 + target / 2 := add_le_add halfPaid halfPaid
          _ = (target / 2) * 2 := by ring1
          _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide) }

set_option genInjectivity false in
open Purelib.Approximation.Rational in
/-- A direct-refinement request retaining the original parent profile, positive root diameter and exact child block.

The stored block has exactly the retained depth and diameter, with their original combined error bound paid against the
target. -/
structure Request {parent : CenteredEdge curve differential} (profile : Profile parent) (target : Coordinate) where
  /-- The retained positive root-diameter request. -/ diameter : Coordinate
  /-- The original requested root diameter is strictly positive. -/ diameterPositive : 0 < diameter
  /-- The retained original dyadic subdivision depth. -/ depth : Nat
  /-- The original direct child block built at the retained depth and root diameter. -/ block : DirectParentBlock parent
  /-- The stored original child-block depth equals the retained request depth. -/ block_depth : block.depth = depth
  /-- The stored original child-block root diameter equals the retained request diameter. -/ block_diameter :
    block.rootDiameter = diameter
  /-- The original scaled spatial-plus-root error is at most the retained target. -/ paid : profile.scale *
    (Geometric.Basic.quarterRadius profile.movement depth + diameter) ≤ target

constructive_injectivity Request

/-- Acquire an original parent refinement using the retained profile and a positive error target.

The exact budget's positive diameter and sufficient depth drive the original direct-block builder; those values and
their payment are retained unchanged. -/
@[expose] def Profile.request {parent : CenteredEdge curve differential} (profile : Profile parent)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {target : Coordinate} (positive : 0 < target) : Request profile target := by
  let budget := Budget.build profile.movement profile.scale (preparationDepth parent)
    profile.movement_nonnegative profile.scale_nonnegative positive
  let block := directParentBlockAtDepth parent proper budget.diameter budget.diameterPositive budget.depth
    budget.prepared
  exact
    { diameter := budget.diameter
      diameterPositive := budget.diameterPositive
      depth := budget.depth
      block := block
      block_depth := rfl
      block_diameter := rfl
      paid := budget.paid }

open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- Every original child of the retained refinement block satisfies the exact requested model-error target. -/
theorem Request.child_error {parent : CenteredEdge curve differential} {profile : Profile parent}
    {target : Coordinate} (request : Request profile target) {child : CenteredEdge curve differential}
    (member : child ∈ request.block.children) : child.edge.modelErrorAllowance ≤ target := by
  have localBound := PreparedPrimitivePaths.block_modelError_le request.block member
  rw [request.block_depth, request.block_diameter] at localBound
  have paid := request.paid
  rw [profile.movement_eq, profile.scale_eq] at paid
  exact localBound.trans ((PreparedPrimitiveRequests.localModelErrorBound_le_preparedScale parent
    request.diameterPositive.le request.depth).trans paid)

end Purelib.Riemann.Integration.PreparedModelAccuracy
