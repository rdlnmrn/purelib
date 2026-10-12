module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.CheckedDirectGeometry
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Tactic.Ring

public section

/-! Exact primitive paths of the retained checked midpoint tree. A child
count or a telescoping total alone is not used to identify vertex geometry. -/
namespace Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths

open Purelib.Riemann.Integration.CheckedDirectGeometry (Mesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Integration.Path.BoundaryRibbon (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- The continuation midpoint equals the dyadic partition midpoint. -/
private theorem midpoint_eq (first last : Path.BoundaryRibbon.Coordinate) :
    Branches.ClearSheetContinuation.midpoint first last = Rectangle.Partition.PreparedBoxPartitions.midpoint first last
      := by
  unfold Branches.ClearSheetContinuation.midpoint Rectangle.Partition.PreparedBoxPartitions.midpoint
  apply Rat.Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  calc
    _ = first + last := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    _ = first * 2 + ((last - first) / 2) * 2 := by
      rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
    _ = _ := by ring1

namespace CheckedDirectGeometry.Mesh

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : PreparedEdge curve differential} {diameter : Coordinate} {depth :
    Nat} {left right : Endpoint}

open Purelib.Riemann in
open Purelib.Integration in
/-- Read the checked midpoint tree as the exact ordered dyadic primitive increments.

The original segment parameterization and retained endpoint parameters determine every child increment. -/
theorem primitive_increments (mesh : Mesh parent diameter depth left right) (value : Path.BoundaryRibbon.Gaussian →
  Path.BoundaryRibbon.Gaussian) :
    mesh.children.map (fun child => value (child.edge.point 1) - value (child.edge.point 0)) =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.segment.pointAt parameter))
        depth left.parameter right.parameter := by
  induction mesh with
  | leaf leaf _ =>
      change [value (leaf.edge.point 1) - value (leaf.edge.point 0)] = _
      rw [PreparedEdge.point_one, PreparedEdge.point_zero]
      rfl
  | split first second firstEq secondEq =>
      rw [Mesh.children, Purelib.Data.List.Map.map_append, firstEq, secondEq,
        Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements]
      dsimp only [Integration.CheckedDirectGeometry.midpoint]
      rw [midpoint_eq]

end CheckedDirectGeometry.Mesh

section
open Purelib.Integration
/-- Pointwise equality of sampled functions preserves every finite dyadic increment. -/
private theorem increments_congr {firstValue lastValue : Path.BoundaryRibbon.Coordinate → Path.BoundaryRibbon.Gaussian}
    (equal : ∀ parameter, firstValue parameter = lastValue parameter) (depth : Nat) (first last :
      Path.BoundaryRibbon.Coordinate) :
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements firstValue depth first last =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements lastValue depth first last := by
  induction depth generalizing first last with
  | zero => change [firstValue last - firstValue first] = [lastValue last - lastValue first]; rw [equal, equal]
  | succ depth ih =>
    rw [Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements, Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements, ih, ih]

/-- An affine parameter change commutes with the complete dyadic increment list. -/
private theorem increments_affine (value : Path.BoundaryRibbon.Coordinate → Path.BoundaryRibbon.Gaussian) (origin slope
  : Path.BoundaryRibbon.Coordinate)
    (depth : Nat) (first last : Path.BoundaryRibbon.Coordinate) :
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (origin + slope * parameter)) depth first
      last =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements value depth (origin + slope * first) (origin + slope * last) :=
        by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
    rw [Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements, Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements, ih, ih,
      Path.Dyadic.DyadicBoundaryRibbon.midpoint_affine]

end

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- Convert dyadic primitive increments from a prepared edge's local parameter to its retained segment parameter.

The equality uses the exact left and requested right endpoint parameters without identifying functions by
extensionality. -/
theorem PreparedConstantModels.PreparedEdge.primitive_dyadic_increments
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
      Hyperelliptic.Differentials.Basic.Differential genus}
    (parent : PreparedEdge curve differential) (value : Path.BoundaryRibbon.Gaussian → Path.BoundaryRibbon.Gaussian)
      (depth : Nat) :
    Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.point parameter)) depth 0 1 =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.segment.pointAt parameter))
        depth
        parent.left.parameter parent.request.endpoint.parameter := by
  have parameter (fraction : Path.BoundaryRibbon.Coordinate) : value (parent.point fraction) =
      value (parent.segment.pointAt (parent.left.parameter +
        (parent.request.endpoint.parameter - parent.left.parameter) * fraction)) := by
    have equal := Branches.PreparedSheetContinuation.pointAt_parameterAt parent.segment parent.within
      parent.left parent.request fraction
    rw [Branches.PreparedSheetContinuation.parameterAt_eq_affine] at equal
    have reorder : parent.left.parameter + fraction * (parent.request.endpoint.parameter - parent.left.parameter) =
        parent.left.parameter + (parent.request.endpoint.parameter - parent.left.parameter) * fraction := by ring1
    rw [reorder] at equal
    exact congrArg value equal.symm
  rw [increments_congr parameter]
  have affine := increments_affine (fun parameter => value (parent.segment.pointAt parameter)) parent.left.parameter
    (parent.request.endpoint.parameter - parent.left.parameter) depth 0 1
  rw [Rat.Fraction.Field.mul_zero_direct, _root_.add_zero,
    Rat.Fraction.Field.mul_one_direct,
    show parent.left.parameter + (parent.request.endpoint.parameter - parent.left.parameter) =
      parent.request.endpoint.parameter by ring1] at affine
  exact affine

namespace CheckedDirectGeometry.Mesh

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
/-- Further subdivision of every checked child yields the original segment path at the summed depth.

The equality preserves the entire ordered increment list and all intermediate points. -/
theorem primitive_refined_increments
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
      Hyperelliptic.Differentials.Basic.Differential genus}
    {parent : PreparedEdge curve differential} {diameter : Path.BoundaryRibbon.Coordinate} {depth : Nat} {left right :
      Endpoint}
    (mesh : Mesh parent diameter depth left right) (value : Path.BoundaryRibbon.Gaussian → Path.BoundaryRibbon.Gaussian)
      (fine : Nat) :
    (mesh.children.map (fun child =>
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0
        1)).flatten =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.segment.pointAt parameter))
        (depth + fine) left.parameter right.parameter := by
  induction mesh with
  | leaf leaf _ =>
      change (Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (leaf.edge.point parameter))
        fine 0 1) ++ [] = _
      rw [Purelib.Data.List.Append.append_nil,
        Paths.PreparedCheckedPrimitivePaths.PreparedConstantModels.PreparedEdge.primitive_dyadic_increments leaf.edge,
        Nat.zero_add]
      rfl
  | split first second firstEq secondEq =>
      rw [Mesh.children, Purelib.Data.List.Map.map_append, Purelib.Data.List.Flatten.flatten_append, firstEq, secondEq,
        Nat.succ_add, Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements]
      dsimp only [Integration.CheckedDirectGeometry.midpoint]
      rw [midpoint_eq]

end CheckedDirectGeometry.Mesh

namespace PreparedDirectDyadicRefinements

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

section
open Purelib.Riemann
open Purelib.Integration
/-- Read a checked parent block as its exact primitive path on the parent's unit interval. -/
theorem checkedParentBlock_primitive_increments (parent : CenteredEdge curve differential)
    {diameter : Path.BoundaryRibbon.Coordinate} {depth : Nat}
    (mesh : Integration.CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left
      parent.edge.request.endpoint)
    (value : Path.BoundaryRibbon.Gaussian → Path.BoundaryRibbon.Gaussian) :
    (Integration.PreparedDirectDyadicRefinements.checkedParentBlock parent mesh).children.map (fun child => value
      (child.edge.point 1) - value (child.edge.point 0)) =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter)) depth 0 1
        := by
  rw [Integration.PreparedDirectDyadicRefinements.checkedParentBlock_children,
    Paths.PreparedCheckedPrimitivePaths.CheckedDirectGeometry.Mesh.primitive_increments mesh,
    Paths.PreparedCheckedPrimitivePaths.PreparedConstantModels.PreparedEdge.primitive_dyadic_increments parent.edge]

/-- Nested child refinement preserves the parent's complete primitive path at the combined depth. -/
theorem checkedParentBlock_primitive_refined_increments (parent : CenteredEdge curve differential)
    {diameter : Path.BoundaryRibbon.Coordinate} {depth : Nat}
    (mesh : Integration.CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left
      parent.edge.request.endpoint)
    (value : Path.BoundaryRibbon.Gaussian → Path.BoundaryRibbon.Gaussian) (fine : Nat) :
    ((Integration.PreparedDirectDyadicRefinements.checkedParentBlock parent mesh).children.map (fun child =>
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0
        1)).flatten =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter)) (depth +
        fine) 0 1 := by
  rw [Integration.PreparedDirectDyadicRefinements.checkedParentBlock_children,
    Paths.PreparedCheckedPrimitivePaths.CheckedDirectGeometry.Mesh.primitive_refined_increments mesh,
    Paths.PreparedCheckedPrimitivePaths.PreparedConstantModels.PreparedEdge.primitive_dyadic_increments parent.edge]

end

open Purelib.Riemann in
open Purelib.Integration in
/-- Grouped checked refinements preserve complete primitive paths in the original parent order.

Refining each retained child again equals refining each original parent at the summed depth and concatenating those
paths. -/
theorem CheckedDirectMeshes.primitive_refined_increments
    {depth : Nat} {diameter : Path.BoundaryRibbon.Coordinate} {parents : List (CenteredEdge curve differential)}
    (meshes : Integration.PreparedDirectDyadicRefinements.CheckedDirectMeshes depth diameter parents) (value :
      Path.BoundaryRibbon.Gaussian → Path.BoundaryRibbon.Gaussian) (fine : Nat) :
    (meshes.toBlocks.children.map (fun child =>
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0
        1)).flatten =
      (parents.map (fun parent =>
        Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter)) (depth
          + fine) 0 1)).flatten := by
  induction meshes with
  | nil => rfl
  | @cons parent remaining mesh tail ih =>
      rw [Integration.PreparedDirectDyadicRefinements.CheckedDirectMeshes.toBlocks_cons_children,
        Purelib.Data.List.Map.map_append, Purelib.Data.List.Flatten.flatten_append]
      have head := checkedParentBlock_primitive_refined_increments parent mesh value fine
      rw [Integration.PreparedDirectDyadicRefinements.checkedParentBlock_children] at head
      exact congrArg₂ List.append head ih

end PreparedDirectDyadicRefinements

end Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths
