module
import Lean.Elab.Tactic.Basic

import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Ring.Basic
public import Purelib.Tactic.AC.Soundness
public import Purelib.Tactic.NormNum.Integer
public import Purelib.Tactic.NormNum.Natural
-- Generated client proofs retain this semiring's structural law fields.
import Purelib.Algebra.Semiring.Nat
public import Purelib.Algebra.Semiring.Normalization
public import Purelib.Algebra.Ring.Normalization
-- Generated client certificates retain these instances and their proof fields.
import Purelib.Algebra.Ring.Int
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order

section
/-!
# Constructive ring proof reconstruction

Mathlib's ring normalizer computes finite polynomial normal forms. Some of its
proof lemmas and standard arithmetic instances retain forbidden axioms. This
frontend replaces the traced roots with direct scalar certificates and a
natural semiring with the same executable operations, before kernel checking.

The normalizer and replacement pass run during elaboration. The stored proof
uses the replacement declarations; independently dirty carrier instances and
other unrepaired roots still require their own authoritative closure checks.
-/

public section

section
open Lean Elab Tactic Meta Mathlib.Tactic Qq
open Purelib.Algebra
open Purelib.Algebra.Semiring

namespace Purelib.Tactic.QuotientFreeRing

/-- Retain the constant replacements used to reconstruct a ring certificate.

Each exact source constant is paired with a universe-sensitive replacement
expression. The finite map retains the original scalar operations and selects the
direct certificate for the corresponding proof law. -/
private meta def proofRootReplacements : Std.HashMap Name (List Level → Expr) :=
  Std.HashMap.ofList [
    (``Mathlib.Meta.NormNum.isNat_intCast, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isNat_intCast
      levels)),
    (``Mathlib.Meta.NormNum.isintCast, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isintCast levels)),
    (``Mathlib.Meta.NormNum.isInt_add, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isInt_add levels)),
    (``Mathlib.Meta.NormNum.isInt_mul, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isInt_mul levels)),
    (``Mathlib.Meta.NormNum.isInt_pow, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isInt_pow levels)),
    (``Mathlib.Meta.NormNum.isInt_neg, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isInt_neg levels)),
    (``Mathlib.Meta.NormNum.IsNat.to_isInt, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isNat_to_isInt
      levels)),
    (``Mathlib.Meta.NormNum.IsInt.to_isNat, fun levels => (.const ``Purelib.Tactic.NormNum.Integer.isInt_to_isNat
      levels)),
    (``Mathlib.Meta.NormNum.IsNat.raw_refl, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.isNat_self levels)),
    (``Mathlib.Meta.NormNum.isNat_natCast, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.isNat_natCast
      levels)),
    (``Mathlib.Meta.NormNum.natPow_one, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.natPow_one levels)),
    (``Mathlib.Meta.NormNum.IsNatPowT.run, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.natPow_run levels)),
    (``Mathlib.Meta.NormNum.IsNatPowT.bit0, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.natPow_bit0 levels)),
    (``Mathlib.Meta.NormNum.IsNatPowT.bit1, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.natPow_bit1 levels)),
    (``Mathlib.Meta.NormNum.intPow_negOfNat_bit0, fun levels => (.const
      ``Purelib.Tactic.NormNum.Integer.intPow_negOfNat_bit0 levels)),
    (``Mathlib.Meta.NormNum.intPow_negOfNat_bit1, fun levels => (.const
      ``Purelib.Tactic.NormNum.Integer.intPow_negOfNat_bit1 levels)),
    (``Mathlib.Meta.NormNum.instAtLeastTwo, fun levels => (.const ``Purelib.Data.Nat.Order.atLeastTwo_add_two levels)),
    (``Nat.instNeZeroSucc, fun levels => (.const ``Purelib.Data.Nat.successorNeZero levels)),
    (``Lean.Data.AC.Context.eq_of_norm, fun levels => (.const ``Purelib.Tactic.AC.Soundness.ac_eq_of_norm levels)),
    (``Nat.instCommSemiring, fun _ => q(Semiring.Nat.commSemiring)),
    (``Nat.instSemiring, fun _ => q(Semiring.Nat.commSemiring.toSemiring)),
    (``Nat.instCommMonoid, fun _ => q(Semiring.Nat.commSemiring.toCommMonoid)),
    (``Nat.instMonoid, fun _ => q(Semiring.Nat.commSemiring.toCommMonoid.toMonoid)),
    (``Nat.instAddMonoidWithOne, fun _ => q(Semiring.Nat.commSemiring.toSemiring.toAddMonoidWithOne)),
    (``Int.instCommRing, fun _ => q(Ring.Int.commRing)),
    (``Int.instRing, fun _ => q(Ring.Int.commRing.toRing)),
    (``Int.instCommSemiring, fun _ => q(Ring.Int.commRing.toCommSemiring)),
    (``Int.instSemiring, fun _ => q(Ring.Int.commRing.toRing.toSemiring)),
    (``Int.instDistrib, fun _ => q(Ring.Int.commRing.toRing.toSemiring.toDistrib)),
    (``Int.instCommMonoid, fun _ => q(Monoid.Int.commMonoid)),
    (``Int.instMonoid, fun _ => q(Monoid.Int.monoid)),
    (``Int.instCommSemigroup, fun _ => q(Semigroup.Int.commSemigroup)),
    (``Int.instSemigroup, fun _ => q(Semigroup.Int.semigroup)),
    (``Int.instAddCommGroup, fun _ => q(Group.Int.addCommGroup)),
    (``Int.instAddGroup, fun _ => q(Group.Int.addCommGroup.toAddGroup)),
    (``Int.instAddCommMonoid, fun _ => q(Group.Int.addCommGroup.toAddCommMonoid)),
    (``Int.instAddMonoid, fun _ => q(Group.Int.addCommGroup.toAddCommMonoid.toAddMonoid)),
    (``Int.instAddCommSemigroup, fun _ => q(Group.Int.addCommGroup.toAddCommMonoid.toAddCommSemigroup)),
    (``Int.instAddSemigroup, fun _ => q(Group.Int.addCommGroup.toAddCommMonoid.toAddCommSemigroup.toAddSemigroup)),
    (``SubtractionMonoid.toSubNegZeroMonoid, fun levels => (.const ``Group.Negation.subNegZeroMonoid levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_zero_add, fun levels => (.const ``Normalization.add_pf_zero_add levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_add_zero, fun levels => (.const ``Normalization.add_pf_add_zero levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_add_lt, fun levels => (.const ``Normalization.add_pf_add_lt levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_add_gt, fun levels => (.const ``Normalization.add_pf_add_gt levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_add_overlap, fun levels => (.const ``Normalization.add_pf_add_overlap levels)),
    (``Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero, fun levels => (.const ``Normalization.add_pf_add_overlap_zero
      levels)),
    (``Mathlib.Tactic.Ring.Common.mul_zero, fun levels => (.const ``Normalization.mul_zero levels)),
    (``Mathlib.Tactic.Ring.Common.zero_mul, fun levels => (.const ``Normalization.zero_mul levels)),
    (``Mathlib.Tactic.Ring.Common.mul_add, fun levels => (.const ``Normalization.mul_add levels)),
    (``Mathlib.Tactic.Ring.Common.add_mul, fun levels => (.const ``Normalization.add_mul levels)),
    (``Mathlib.Tactic.Ring.Common.add_overlap_pf, fun levels => (.const ``Normalization.add_overlap_pf levels)),
    (``Mathlib.Tactic.Ring.Common.add_overlap_pf_zero, fun levels => (.const ``Normalization.add_overlap_pf_zero
      levels)),
    (``Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap, fun levels => (.const ``Normalization.mul_pp_pf_overlap levels)),
    (``Mathlib.Tactic.Ring.Common.single_pow, fun levels => (.const ``Normalization.single_pow levels)),
    (``Mathlib.Tactic.Ring.Common.pow_prod_atom, fun levels => (.const ``Normalization.pow_prod_atom levels)),
    (``Mathlib.Tactic.Ring.Common.atom_pf, fun levels => (.const ``Normalization.atom_pf levels)),
    (``Mathlib.Tactic.Ring.Common.const_pos, fun levels => (.const ``Purelib.Data.Nat.Order.positive_of_ble_one
      levels)),
    (``Mathlib.Tactic.Ring.Common.zero_pow, fun levels => (.const ``Normalization.zero_pow levels)),
    (``Mathlib.Tactic.Ring.Common.pow_one, fun levels => (.const ``Normalization.pow_one levels)),
    (``Mathlib.Tactic.Ring.Common.pow_bit0, fun levels => (.const ``Normalization.pow_bit0 levels)),
    (``Mathlib.Tactic.Ring.Common.pow_bit1, fun levels => (.const ``Normalization.pow_bit1 levels)),
    (``Mathlib.Tactic.Ring.Common.one_pow, fun levels => (.const ``Normalization.one_pow levels)),
    (``Mathlib.Tactic.Ring.Common.coeff_one, fun levels => (.const ``Normalization.coeff_one levels)),
    (``Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat, fun levels => (.const ``Normalization.pow_one_cast_of_isNat
      levels)),
    (``Mathlib.Tactic.Ring.Common.pow_nat, fun levels => (.const ``Normalization.pow_nat levels)),
    (``Mathlib.Tactic.Ring.Common.pow_zero, fun levels => (.const ``Normalization.pow_zero levels)),
    (``Mathlib.Tactic.Ring.Common.pow_add, fun levels => (.const ``Normalization.pow_add levels)),
    (``Mathlib.Tactic.Ring.Common.mul_pow_mul, fun levels => (.const ``Normalization.mul_pow_mul levels)),
    (``Mathlib.Tactic.Ring.cast_pos, fun levels => (.const ``Normalization.cast_pos levels)),
    (``Mathlib.Tactic.Ring.cast_neg, fun levels => (.const ``Ring.Normalization.cast_neg levels)),
    (``Mathlib.Tactic.Ring.cast_zero, fun levels => (.const ``Normalization.cast_zero levels)),
    (``Mathlib.Tactic.Ring.Common.neg_zero, fun levels => (.const ``Ring.Normalization.neg_zero levels)),
    (``Mathlib.Tactic.Ring.Common.neg_mul, fun levels => (.const ``Ring.Normalization.neg_mul levels)),
    (``Mathlib.Tactic.Ring.Common.neg_add, fun levels => (.const ``Ring.Normalization.neg_add levels)),
    (``Mathlib.Tactic.Ring.Common.sub_pf, fun levels => (.const ``Ring.Normalization.sub_pf levels)),
    (``Mathlib.Tactic.Ring.Common.neg_congr, fun levels => (.const ``Ring.Normalization.neg_congr levels)),
    (``Mathlib.Meta.NormNum.isNat_add, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.isNat_add levels)),
    (``Mathlib.Meta.NormNum.isNat_mul, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.isNat_mul levels)),
    (``Mathlib.Meta.NormNum.isNat_pow, fun levels => (.const ``Purelib.Tactic.NormNum.Natural.isNat_pow levels))]

end Purelib.Tactic.QuotientFreeRing

namespace Purelib.Tactic.Ring

set_option backward.match.sparseCases false in
/-- Replace dirty proof roots while retaining the normalizer's arithmetic operations.

The finite replacement map supplies direct certificates for the original scalar
operations. Ordinary expression cases preserve the complete proof tree without
retaining sparse bitmask discriminator certificates. -/
private meta def replaceProofRoots (proof : Expr) : Expr :=
  let replacements := Purelib.Tactic.QuotientFreeRing.proofRootReplacements
  proof.replace fun expression =>
    if !expression.isConst then none else
    match replacements.get? expression.constName! with
    | none => none
    | some replacement => some (replacement expression.constLevels!)

/-- Reconstruct the computed ring equality with the direct replacement proof roots. -/
private meta def proveEq (goal : MVarId) (transparency : TransparencyMode) : MetaM Unit := do
  let proofGoal ← mkFreshExprMVar (← goal.getType)
  AtomM.run transparency
    (Mathlib.Tactic.Ring.proveEq proofGoal.mvarId!)
  let proof ← instantiateMVars proofGoal
  goal.assign (replaceProofRoots proof)

/-- Quotient-free frontend for Mathlib's computational ring normalizer. -/
elab (name := quotientFreeRing) "ring0" bang:"!"? : tactic =>
  liftMetaMAtMain fun goal => do
    Purelib.Tactic.Ring.proveEq goal (if bang.isSome then .default else .reducible)

/-! Importing this module also upgrades existing `ring1` source without a
cosmetic tactic rename.  The later elaboration rule takes precedence over
Mathlib's frontend while retaining exactly the same syntax. -/

end Purelib.Tactic.Ring

namespace Purelib.Tactic.QuotientFreeRing

elab_rules : tactic
  | `(tactic| ring1 $[!%$bang]?) =>
      liftMetaMAtMain fun goal => do
        Purelib.Tactic.Ring.proveEq goal (if bang.isSome then .default else .reducible)
end Purelib.Tactic.QuotientFreeRing

end

end

end
