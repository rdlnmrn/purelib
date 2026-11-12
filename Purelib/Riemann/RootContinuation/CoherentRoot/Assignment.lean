module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Identification
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
import Purelib.Riemann.RootContinuation.CoherentRoot.Family
public import Purelib.RootIsolation.Residual.Global.Assignment
public import Purelib.Approximation.Gaussian.Sequence.Selection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Nearby readings of original assigned root caches

A retained localized track and its original isolation owner determine a nearby
reading of that owner's actual cached program. The comparison uses the original
assignment state and computes its own paid refinement request.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Assignment

open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.RootIsolation.Residual
open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Eighteen times the retained small radius square fits one quarter of its positive target. -/
private theorem band_payment {target radius : Fraction.Rational} (positive : 0 < target)
    (small : radius ^ 2 < target / 128) : 18 * radius ^ 2 < target / 4 := by
  have paid := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (show (0 : Fraction.Rational) < 18 by decide)
    small
  have coefficientBound := Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (show (18 / 128 : Fraction.Rational) < 1 / 4 by
      change ((18 : Nat) : Fraction.Rational) / ((128 : Nat) : Fraction.Rational) <
        ((1 : Nat) : Fraction.Rational) / ((4 : Nat) : Fraction.Rational)
      rewrite [Fraction.Cast.natCast_eq_fromInt 18, Fraction.Cast.natCast_eq_fromInt 128,
        Fraction.Cast.natCast_eq_fromInt 1, Fraction.Cast.natCast_eq_fromInt 4]
      decide) positive
  rewrite [← Fraction.Compatibility.mul_div_reassociate, ← Fraction.Compatibility.mul_div_reassociate,
    one_mul] at coefficientBound
  exact paid.trans coefficientBound

/-- Transfer a retained original localization band to the same actual cached owner program at a positive request. -/
def nearby {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output) :
    Sequence.Selection.Nearby (fun index => (roots.get index).approximation) sample target := by
  let root := certifiedName localized.track input.degreePositive
  let assignment := Assignment.ofSelection input output roots root localized.owner
  let owner := roots.get localized.owner.owner
  let sourceIntermediate := root.compare_nested_prepared input assignment.intermediate
    assignment.selection.refined_strict_source
  let ownerIntermediate := owner.compare_nested_prepared input assignment.intermediate
    assignment.selection.refined_strict
  let equivalent := ownerIntermediate.trans sourceIntermediate.symm
  let comparison := equivalent.compare 0 0 (target / 4)
    (Fraction.Order.Field.div_pos_direct targetPositive (by decide))
  have contained : localized.state.box.Contains (root.approximation.sample comparison.rightIndex) := by
    have inside := root.sample_initial_inside comparison.rightIndex
    rewrite [localized.trackInitial] at inside
    exact inside
  have band := localized.bandNearSample _ contained
  have radiusLe := Order.Arithmetic.pow_le_pow_direct localized.radiusPositive.le localized.radiusLeRequested 2
  have nearPoint : normSq (root.approximation.sample comparison.rightIndex - sample) < target / 4 :=
    (band.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLe (by decide))).trans_lt
      (band_payment targetPositive radiusSmall)
  refine ⟨localized.owner.owner, comparison.leftIndex, ?_⟩
  intro later order
  have close := comparison.close order (Nat.le_refl comparison.rightIndex)
  have bound := (Norm.Bounds.normSq_sub_le_via (owner.approximation.sample later)
    (root.approximation.sample comparison.rightIndex) sample).trans_lt
      (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Order.Arithmetic.add_lt_add_direct close nearPoint))
  have identity : 2 * (target / 4 + target / 4) = target := by
    calc
      2 * (target / 4 + target / 4) = target / 4 * 4 := by ring0
      _ = target := Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
  exact bound.trans_eq identity

/-- Read the original nearby owner and first nested payment without evaluating its other proof data. -/
private theorem nearby_readback {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output) :
    (nearby input output roots sample targetPositive radiusSmall localized).owner = localized.owner.owner ∧
    (nearby input output roots sample targetPositive radiusSmall localized).index =
      (CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner) (max 0 1)
        (((target / 4) / 4) / 4)
        (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))).index := by
  constructor
  · rfl
  · let root := certifiedName localized.track input.degreePositive
    let assignment := Assignment.ofSelection input output roots root localized.owner
    dsimp only [nearby, Equivalence.Equivalent.trans]
    exact (CertifiedName.compare_nested_prepared_indices input
      (roots.get localized.owner.owner) assignment.intermediate assignment.selection.refined_strict
      0 0 ((target / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide))).1

/-- Reuse the original owner-side payment of a nearby-root comparison.

The supplied localized result retains its exact original track and full owner
selection. Only the first original nested comparison's owner index contributes
to the nearby record; the remaining comparison data occurs in its proof. This
constructor reads the authenticated owner payment without rebuilding the
localized root, intermediate assignment or their discarded numerical payments.
-/
def nearbyFromOwnerPaid {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output)
    (ownerPaid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
    (ownerSame : ownerPaid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))) :
    Sequence.Selection.Nearby (fun index => (roots.get index).approximation) sample target where
  owner := localized.owner.owner
  index := ownerPaid.index
  close := by
    intro later order
    let original := nearby input output roots sample targetPositive radiusSmall localized
    have fields := nearby_readback input output roots sample targetPositive radiusSmall localized
    have index : ownerPaid.index = original.index :=
      (congrArg CoherentRoot.Refinement.index ownerSame).trans fields.2.symm
    have owner : original.owner = localized.owner.owner := fields.1
    have bound := original.close later (index ▸ order)
    rewrite [owner] at bound
    exact bound

/-- The retained owner payment preserves the complete original nearby-root result. -/
private theorem nearbyFromOwnerPaid_readback {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output)
    (ownerPaid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
    (ownerSame : ownerPaid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))) :
    nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame =
      nearby input output roots sample targetPositive radiusSmall localized ∧
      (nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).owner =
        localized.owner.owner ∧
      (nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).index =
        ownerPaid.index := by
  constructor
  · have fields := nearby_readback input output roots sample targetPositive radiusSmall localized
    cases originalEq : nearby input output roots sample targetPositive radiusSmall localized with
    | mk originalOwner originalIndex originalClose =>
      have owner : originalOwner = localized.owner.owner :=
        (congrArg Sequence.Selection.Nearby.owner originalEq).symm.trans fields.1
      have index : originalIndex = ownerPaid.index :=
        (congrArg Sequence.Selection.Nearby.index originalEq).symm.trans
          (fields.2.trans (congrArg CoherentRoot.Refinement.index ownerSame).symm)
      cases owner
      cases index
      rfl
  · exact ⟨rfl, rfl⟩

/-- The retained owner payment preserves the complete original nearby-root result. -/
theorem nearbyFromOwnerPaid_eq {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output)
    (ownerPaid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
    (ownerSame : ownerPaid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))) :
    nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame =
      nearby input output roots sample targetPositive radiusSmall localized :=
  (nearbyFromOwnerPaid_readback input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).1

/-- The nearby original owner is read from the retained complete localization selection. -/
theorem nearbyFromOwnerPaid_owner {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output)
    (ownerPaid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
    (ownerSame : ownerPaid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))) :
    (nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).owner =
      localized.owner.owner :=
  (nearbyFromOwnerPaid_readback input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).2.1

/-- The nearby stage reads the authenticated original owner payment's actual index. -/
theorem nearbyFromOwnerPaid_index {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (output : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
      polynomial.natDegree) (roots : Family output.tracks)
    (sample : Basic.Canonical) {epsilon target : Fraction.Rational} (targetPositive : 0 < target)
    (radiusSmall : epsilon ^ 2 < target / 128)
    (localized : Global.Assignment.AssignedResult input sample epsilon output)
    (ownerPaid : CoherentRoot.Refinement (roots.get localized.owner.owner) (max 0 1))
    (ownerSame : ownerPaid = CoherentRoot.Refinement.ofTarget (roots.get localized.owner.owner)
      (max 0 1) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct targetPositive (by decide)) (by decide)) (by decide))) :
    (nearbyFromOwnerPaid input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).index =
      ownerPaid.index :=
  (nearbyFromOwnerPaid_readback input output roots sample targetPositive radiusSmall localized ownerPaid ownerSame).2.2

end Purelib.Riemann.RootContinuation.CoherentRoot.Assignment

end
