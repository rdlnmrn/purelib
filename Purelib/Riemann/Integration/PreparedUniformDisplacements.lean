module
import Purelib.Algebra.NatCast
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.LinearAlgebra.Norm.GaussianRigidity
import Purelib.Tactic.Ring

public section

/-!
# Uniform geometry forced by the retained direct refinement certificates

The exact child count, displacement sum and per-child squared movement
bounds force each child displacement to be the parent's dyadic displacement.
This reconstructs order information from the existing cached block; no
subdivision or root preparation is repeated.
-/

namespace Purelib.Riemann.Integration.PreparedUniformDisplacements

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain DirectParentBlock)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}

open Purelib.Data in
open Purelib.Geometry in
/-- The ordered child displacements telescope to the retained chain's endpoint displacement. -/
private theorem chain_displacements {children : List (CenteredEdge curve source)}
    {first last : Path.Gaussian.Lifted.Basic.LiftedPoint 2} (chain : DirectPathChain children (start := first) (finish
      := last)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (children.map (fun child => child.edge.point 1 - child.edge.point 0)) =
      last.coordinate - first.coordinate := by
  induction chain with
  | nil => change (0 : Gaussian.Basic.Canonical) = _ - _; ring1
  | cons child tail ih =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih, child.edge.point_one,
        child.edge.point_zero]
      ring1

section
open Purelib.Data
/-- The squared Gaussian norm of the natural dyadic count is four to the same depth. -/
private theorem dyadic_norm (depth : Nat) : Data.Gaussian.Norm.Basic.normSq ((2 ^ depth : Nat) :
  Gaussian.Basic.Canonical) = (4 : Rat.Fraction.Rational) ^ depth := by
  rw [Data.Gaussian.Norm.Basic.normSq, Gaussian.Cast.natCast_re,
    Gaussian.Cast.natCast_im]
  simp only [Algebra.NatCast.pow, Nat.cast_ofNat, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  congr 1

/-- A natural dyadic count embedded in the Gaussian rationals is nonzero. -/
private theorem dyadic_nonzero (depth : Nat) : ((2 ^ depth : Nat) : Gaussian.Basic.Canonical) ≠ 0 := by
  have positive : 0 < Data.Gaussian.Norm.Basic.normSq ((2 ^ depth : Nat) : Gaussian.Basic.Canonical) := by
    rw [dyadic_norm]
    exact Rat.Fraction.Order.Arithmetic.pow_pos_direct (by decide) _
  intro equal
  exact positive.ne' ((congrArg Data.Gaussian.Norm.Basic.normSq equal).trans Gaussian.Norm.Basic.normSq_zero)

end

namespace DirectParentBlock

open Purelib.Data in
/-- The parent displacement divided by its retained dyadic child count. -/
@[expose] def step {parent : CenteredEdge curve source} (block : DirectParentBlock parent) : Gaussian :=
  (parent.edge.point 1 - parent.edge.point 0) / ((2 ^ block.depth : Nat) : Gaussian.Basic.Canonical)

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- The common step's squared norm equals the parent geometric movement scaled by the dyadic quarter-radius. -/
private theorem step_norm {parent : CenteredEdge curve source} (block : DirectParentBlock parent) :
    Data.Gaussian.Norm.Basic.normSq (Integration.PreparedUniformDisplacements.DirectParentBlock.step block) =
      Rational.Geometric.Basic.quarterRadius
      (Integration.PreparedDirectDyadicRefinements.geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter) block.depth := by
  rw [step, Gaussian.Field.normSq_div _ _ (dyadic_nonzero _), dyadic_norm]
  rw [parent.edge.point_one, parent.edge.point_zero]
  exact (Rat.Fraction.Field.div_eq_mul_inv_direct _ _).symm

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Data in
/-- The common step is a strictly positive rational multiple of the parent displacement. -/
theorem step_eq_positive_scale {parent : CenteredEdge curve source} (block : DirectParentBlock parent) :
    ∃ factor : Rat.Fraction.Rational, 0 < factor ∧ (Integration.PreparedUniformDisplacements.DirectParentBlock.step
      block) =
      (⟨factor, 0⟩ : Gaussian.Basic.Canonical) * (parent.edge.point 1 - parent.edge.point 0) := by
  have positive : (0 : Rat.Fraction.Rational) < ((2 ^ block.depth : Nat) : Rat.Fraction.Rational) :=
    Rat.Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide))
  let factor : Rat.Fraction.Rational := 1 / ((2 ^ block.depth : Nat) : Rat.Fraction.Rational)
  have product : factor * ((2 ^ block.depth : Nat) : Rat.Fraction.Rational) = 1 :=
    Rat.Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
  have scalar : (⟨factor, 0⟩ : Gaussian.Basic.Canonical) * ((2 ^ block.depth : Nat) : Gaussian.Basic.Canonical) = 1 :=
    by
    apply Gaussian.Basic.ext
    · rw [Gaussian.Basic.mul_re, Gaussian.Cast.natCast_re,
        Gaussian.Cast.natCast_im, Gaussian.Basic.one_re]
      change factor * ((2 ^ block.depth : Nat) : Rat.Fraction.Rational) - 0 * 0 = 1
      rw [product]
      ring1
    · rw [Gaussian.Basic.mul_im, Gaussian.Cast.natCast_re,
        Gaussian.Cast.natCast_im, Gaussian.Basic.one_im]
      change factor * 0 + 0 * ((2 ^ block.depth : Nat) : Rat.Fraction.Rational) = 0
      ring1
  refine ⟨factor, Rat.Fraction.Order.Field.div_pos_direct (by decide) positive, ?_⟩
  apply Gaussian.Field.mul_right_cancel_of_ne (dyadic_nonzero block.depth)
  rw [step, Field.ExplicitField.div_mul_cancel _ (dyadic_nonzero _)]
  calc
    _ = (parent.edge.point 1 - parent.edge.point 0) * 1 := by ring1
    _ = (parent.edge.point 1 - parent.edge.point 0) * ((⟨factor, 0⟩ : Gaussian.Basic.Canonical) * ((2 ^ block.depth :
      Nat) : Gaussian.Basic.Canonical)) :=
      congrArg ((parent.edge.point 1 - parent.edge.point 0) * ·) scalar.symm
    _ = _ := by ring1

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Every retained child has exactly the common dyadic displacement.

The certified count, telescoping sum and per-child norm bounds force equality by finite Gaussian rigidity, including
when the parent is stationary. -/
theorem child_displacement {parent : CenteredEdge curve source} (block : DirectParentBlock parent)
    {child : CenteredEdge curve source} (member : child ∈ block.children) :
    child.edge.point 1 - child.edge.point 0 = (Integration.PreparedUniformDisplacements.DirectParentBlock.step block) :=
      by
  have total : Data.Gaussian.Norm.Sum.Basic.gaussianSum (block.children.map (fun child => child.edge.point 1 -
    child.edge.point 0)) =
      ((block.children.map (fun child => child.edge.point 1 - child.edge.point 0)).length : Gaussian.Basic.Canonical) *
        (Integration.PreparedUniformDisplacements.DirectParentBlock.step block) := by
    rw [chain_displacements block.chain, List.Map.length_map, block.childCount, step,
      Gaussian.Basic.mul_comm, Field.ExplicitField.div_mul_cancel _ (dyadic_nonzero _),
      parent.edge.point_one, parent.edge.point_zero]
  have bounded : ∀ value ∈ block.children.map (fun child => child.edge.point 1 - child.edge.point 0),
    Data.Gaussian.Norm.Basic.normSq value ≤ Data.Gaussian.Norm.Basic.normSq
    (Integration.PreparedUniformDisplacements.DirectParentBlock.step block) := by
    intro value present
    obtain ⟨child, member, rfl⟩ := List.Map.mem_map.mp present
    rw [Integration.PreparedUniformDisplacements.DirectParentBlock.step_norm block]
    exact Paths.PreparedPrimitivePaths.block_movement_le block member
  exact Norm.all_eq_of_sum_and_norm_bound _ (Integration.PreparedUniformDisplacements.DirectParentBlock.step block)
    total bounded _
    (List.Map.mem_map.mpr ⟨child, member, rfl⟩)

end DirectParentBlock
end Purelib.Riemann.Integration.PreparedUniformDisplacements
