module

public import Init.Data.Nat.Linear
import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Nat.Multiplication
import Lean.Elab.Tactic.Omega
meta import Lean.Elab.Tactic.Omega.Frontend
meta import Lean.Elab.Tactic.Omega.OmegaM

section

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

public section

section

open Lean.Omega

namespace Purelib.Tactic.QuotientFreeOmega

/-- Reduce a finite coordinate evaluation by its explicit list and integer equations.

This local tactic unfolds only the displayed coefficient constructors, dot product and scalar zero/one identities. -/
local macro "coordinate_rfl" : tactic =>
  `(tactic|
    simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith, Int.one_mul, Int.zero_mul, Int.add_zero,
      Int.zero_add])

end Purelib.Tactic.QuotientFreeOmega

namespace Purelib.Tactic.Omega.NatLinear

open Nat.Linear in
open Purelib.Data.Nat in
/-- Natural expression conversion retains denotation with its displayed coefficient and polynomial tail.

The recursive conversion retains the original context, coefficient and tail.
Kernel reduction certifies the fixed numeral variable, and direct natural
arithmetic laws transport each original scalar expression. -/
theorem natExpr_denote_toPoly_go (context : Context) (expression : Expr) :
    (Expr.toPoly.go coefficient expression polynomial).denote context =
      coefficient * expression.denote context + polynomial.denote context := open Purelib in by
  induction expression generalizing coefficient polynomial with
  | num constant =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            coefficient * constant * Var.denote context fixedVar +
                polynomial.denote context =
              coefficient * constant + polynomial.denote context
          have fixedDenotation : Var.denote context fixedVar = 1 := by
            change Bool.rec (context.get fixedVar) 1
                (Nat.beq fixedVar fixedVar) = 1
            rfl
          rw [fixedDenotation, Nat.mul_one]
      | true =>
          have constantEquality : constant = 0 := of_decide_eq_true equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * 0 + polynomial.denote context
          rw [Nat.mul_zero, Nat.zero_add]
  | var index => rfl
  | add left right leftHypothesis rightHypothesis =>
      change
        (Expr.toPoly.go coefficient left
            (Expr.toPoly.go coefficient right polynomial)).denote context =
          coefficient * (left.denote context + right.denote context) +
            polynomial.denote context
      calc
        (Expr.toPoly.go coefficient left
              (Expr.toPoly.go coefficient right polynomial)).denote context =
            coefficient * left.denote context +
              (Expr.toPoly.go coefficient right polynomial).denote context :=
          leftHypothesis
        _ = coefficient * left.denote context +
              (coefficient * right.denote context +
                polynomial.denote context) := by
          rw [rightHypothesis]
        _ = coefficient * (left.denote context + right.denote context) +
              polynomial.denote context := by
          rw [Nat.mul_add, Nat.add_assoc]
  | mulL constant expression inductionHypothesis =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            (Expr.toPoly.go (coefficient * constant) expression polynomial).denote
                context =
              coefficient * (constant * expression.denote context) +
                polynomial.denote context
          rw [inductionHypothesis, Multiplication.mul_assoc]
      | true =>
          have constantEquality : constant = 0 := of_decide_eq_true equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * (0 * expression.denote context) +
              polynomial.denote context
          rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
  | mulR expression constant inductionHypothesis =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            (Expr.toPoly.go (coefficient * constant) expression polynomial).denote
                context =
              coefficient * (expression.denote context * constant) +
                polynomial.denote context
          rw [inductionHypothesis, Multiplication.mul_assoc,
            Nat.mul_comm constant (expression.denote context)]
      | true =>
          have constantEquality : constant = 0 := of_decide_eq_true equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * (expression.denote context * 0) +
              polynomial.denote context
          rw [Nat.mul_zero, Nat.mul_zero, Nat.zero_add]

open Nat.Linear in
open Purelib.Tactic in
/-- Converting a natural linear expression to its finite polynomial preserves its denotation in every displayed context.
-/
theorem natExpr_denote_toPoly (context : Context) (expression : Expr) :
    expression.toPoly.denote context = expression.denote context := by
  change (Expr.toPoly.go 1 expression []).denote context =
    expression.denote context
  rw [natExpr_denote_toPoly_go]
  change 1 * expression.denote context + 0 = expression.denote context
  rw [Nat.one_mul, Nat.add_zero]

end Purelib.Tactic.Omega.NatLinear

open Nat.Linear
open Purelib.Data.Nat
open Purelib.Tactic

namespace Purelib.Tactic.QuotientFreeOmega

/-- Inserting one retained monomial preserves its scalar contribution.

The original Boolean ordering selects an insertion point. Equal variables
merge their supplied coefficients; every other entry remains in its original tail. -/
private theorem poly_insert_denote (context : Context) (coefficient varIndex : Nat) :
    ∀ polynomial : Poly,
      (polynomial.insert coefficient varIndex).denote context =
        polynomial.denote context + coefficient * Var.denote context varIndex
  | [] => by
      change coefficient * Var.denote context varIndex + 0 =
        0 + coefficient * Var.denote context varIndex
      exact (Nat.add_zero _).trans (Nat.zero_add _).symm
  | (nextCoefficient, nextVariable) :: tail => by
      cases ordered : Nat.blt varIndex nextVariable with
      | true =>
          rw [Poly.insert, ordered]
          exact Nat.add_comm _ _
      | false =>
          cases equal : Nat.beq varIndex nextVariable with
          | true =>
              have same := Nat.eq_of_beq_eq_true equal
              subst nextVariable
              rw [Poly.insert, ordered, equal]
              change (coefficient + nextCoefficient) * Var.denote context varIndex + Poly.denote context tail =
                (nextCoefficient * Var.denote context varIndex + Poly.denote context tail) +
                  coefficient * Var.denote context varIndex
              rw [Multiplication.right_distrib]
              exact (Nat.add_assoc _ _ _).trans (Nat.add_comm _ _)
          | false =>
              rw [Poly.insert, ordered, equal]
              change nextCoefficient * Var.denote context nextVariable +
                  Poly.denote context (Poly.insert coefficient varIndex tail) =
                (nextCoefficient * Var.denote context nextVariable + Poly.denote context tail) +
                  coefficient * Var.denote context varIndex
              rw [poly_insert_denote context coefficient varIndex tail]
              exact (Nat.add_assoc _ _ _).symm

/-- The original normalization fold retains both polynomial and accumulator denotations.

Each displayed monomial is inserted into the supplied accumulator. The
insertion certificate and structural tail recursion preserve their scalar sum. -/
private theorem poly_norm_go_denote (context : Context) : ∀ polynomial accumulator : Poly,
    (Poly.norm.go polynomial accumulator).denote context =
      polynomial.denote context + accumulator.denote context
  | [], accumulator => (Nat.zero_add _).symm
  | (coefficient, varIndex) :: tail, accumulator => by
      change (Poly.norm.go tail (accumulator.insert coefficient varIndex)).denote context =
        (coefficient * Var.denote context varIndex + Poly.denote context tail) + accumulator.denote context
      rw [poly_norm_go_denote context tail, poly_insert_denote context]
      calc
        Poly.denote context tail + (accumulator.denote context + coefficient * Var.denote context varIndex) =
            (Poly.denote context tail + accumulator.denote context) + coefficient * Var.denote context varIndex :=
          (Nat.add_assoc _ _ _).symm
        _ = coefficient * Var.denote context varIndex +
              (Poly.denote context tail + accumulator.denote context) := Nat.add_comm _ _
        _ = (coefficient * Var.denote context varIndex + Poly.denote context tail) + accumulator.denote context :=
          (Nat.add_assoc _ _ _).symm

/-- Original coefficient normalization preserves scalar denotation.

The fold begins with the original empty accumulator, whose scalar contribution
is zero. Insertion preserves every monomial's supplied context value. -/
private theorem poly_norm_denote (context : Context) (polynomial : Poly) :
    polynomial.norm.denote context = polynomial.denote context := by
  change (Poly.norm.go polynomial []).denote context = polynomial.denote context
  rw [poly_norm_go_denote]
  exact Nat.add_zero _

/-- Concatenating retained monomial lists adds their scalar denotations.

Structural recursion retains the left head contribution and transports only
the corresponding tail sum, leaving the original right list unchanged. -/
private theorem poly_append_denote (context : Context) : ∀ left right : Poly,
    Poly.denote context (left ++ right) = left.denote context + right.denote context
  | [], right => (Nat.zero_add _).symm
  | (coefficient, varIndex) :: tail, right => by
      change coefficient * Var.denote context varIndex + Poly.denote context (tail ++ right) =
        (coefficient * Var.denote context varIndex + Poly.denote context tail) + right.denote context
      exact (congrArg (fun subtotal : Nat => coefficient * Var.denote context varIndex + subtotal)
        (poly_append_denote context tail right)).trans (Nat.add_assoc _ _ _).symm

/-- Reversing into a retained accumulator preserves the original scalar sum.

Each original head moves to the displayed accumulator without changing its
context value. The recursion consumes the exact original polynomial tail. -/
private theorem poly_reverseAux_denote (context : Context) : ∀ polynomial accumulator : Poly,
    Poly.denote context (List.reverseAux polynomial accumulator) =
      polynomial.denote context + accumulator.denote context
  | [], accumulator => (Nat.zero_add _).symm
  | (coefficient, varIndex) :: tail, accumulator => by
      change Poly.denote context (List.reverseAux tail ((coefficient, varIndex) :: accumulator)) =
        (coefficient * Var.denote context varIndex + Poly.denote context tail) + accumulator.denote context
      rw [poly_reverseAux_denote context tail]
      change Poly.denote context tail + (coefficient * Var.denote context varIndex + accumulator.denote context) =
        (coefficient * Var.denote context varIndex + Poly.denote context tail) + accumulator.denote context
      exact (Nat.add_left_comm _ _ _).trans (Nat.add_assoc _ _ _).symm

/-- Reversing the original monomial list preserves its scalar denotation.

The reverse traversal begins with the empty accumulator. Its displayed
monomial values therefore contribute exactly the original scalar sum. -/
private theorem poly_reverse_denote (context : Context) (polynomial : Poly) :
    Poly.denote context polynomial.reverse = polynomial.denote context := by
  change Poly.denote context (List.reverseAux polynomial []) = polynomial.denote context
  rw [poly_reverseAux_denote]
  exact Nat.add_zero _

/-- Restoring the reversed accumulator adds its unchanged contribution to the retained tail.

The original cancellation output concatenates this accumulator with the exact
remaining polynomial. Append and reverse certificates identify that scalar sum. -/
private theorem poly_restore_denote (context : Context) (accumulator tail : Poly) :
    Poly.denote context (accumulator.reverse ++ tail) = Poly.denote context tail + accumulator.denote context :=
  (poly_append_denote context _ _).trans
    ((congrArg (fun subtotal : Nat => subtotal + Poly.denote context tail)
      (poly_reverse_denote context accumulator)).trans (Nat.add_comm _ _))

/-- A false original strict comparison retains the reverse natural bound.

A strict forward bound would make that same primitive Boolean comparison
true. Constructor disjointness excludes that bound without identifying propositions. -/
private theorem reverse_bound_of_blt_false {left right : Nat}
    (comparison : Nat.blt left right = false) : right ≤ left := by
  apply Nat.le_of_not_gt
  intro ordered
  have selected : Nat.blt left right = true := Nat.ble_eq_true_of_le ordered
  exact Bool.noConfusion (comparison.symm.trans selected)

/-- Matching false strict comparisons identify the original natural arguments.

Each retained Boolean equation gives the reverse weak bound. Antisymmetry
therefore identifies the actual original values. -/
private theorem equal_of_blt_false {left right : Nat}
    (forward : Nat.blt left right = false) (backward : Nat.blt right left = false) : left = right :=
  Nat.le_antisymm (reverse_bound_of_blt_false backward) (reverse_bound_of_blt_false forward)

/-- Reconstructing a larger coefficient reconstructs its original scaled value.

The supplied coefficient bound permits adding back its truncated difference.
The original natural multiplication distributes over that same retained sum. -/
private theorem scaled_reconstruction (smaller larger value : Nat) (bound : smaller ≤ larger) :
    larger * value = smaller * value + (larger - smaller) * value :=
  (congrArg (fun coefficient : Nat => coefficient * value)
    (Subtraction.add_sub_of_le bound).symm).trans (Multiplication.right_distrib _ _ _)

/-- Moving the common leading contribution past a retained tail preserves the scalar sum.

The head and accumulator still contribute their original values. Only the
parenthesization and order of those three displayed natural summands change. -/
private theorem move_head (head tail accumulator : Nat) :
    (head + tail) + accumulator = tail + (head + accumulator) :=
  (Nat.add_assoc _ _ _).trans (Nat.add_left_comm _ _ _)

/-- Splitting a retained head exposes a common contribution before its exact residual tail.

The first displayed summand is separated from its residual. Reassociation
keeps the original residual, tail and accumulator values in their finite sum. -/
private theorem split_head (common residual tail accumulator : Nat) :
    ((common + residual) + tail) + accumulator = common + (tail + (residual + accumulator)) :=
  (Nat.add_assoc _ _ _).trans
    ((Nat.add_assoc _ _ _).trans
      (congrArg (fun subtotal : Nat => common + subtotal) (Nat.add_left_comm _ _ _)))

/-- Adding a displayed head extends the same retained common contribution.

The original output is unchanged. Scalar reassociation puts the added head
beside the common value already shared by both polynomial denotations. -/
private theorem extend_common (head : Nat) {total output common : Nat}
    (retained : total = output + common) :
    head + total = output + (head + common) :=
  (congrArg (fun value : Nat => head + value) retained).trans (Nat.add_left_comm _ _ _)

/-- Finite cancellation retains the same removed scalar on both original sides.

Every original comparison and residual coefficient is preserved. The fuel
bounds traversal only; even an early stop restores both exact retained tails. -/
private theorem poly_cancelAux_common (context : Context) (fuel : Nat)
    (left right leftAccumulator rightAccumulator : Poly) :
    ∃ common : Nat,
      left.denote context + leftAccumulator.denote context =
        (Poly.cancelAux fuel left right leftAccumulator rightAccumulator).1.denote context + common ∧
      right.denote context + rightAccumulator.denote context =
        (Poly.cancelAux fuel left right leftAccumulator rightAccumulator).2.denote context + common := by
  induction fuel generalizing left right leftAccumulator rightAccumulator with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · exact (poly_restore_denote context leftAccumulator left).symm.trans (Nat.add_zero _).symm
      · exact (poly_restore_denote context rightAccumulator right).symm.trans (Nat.add_zero _).symm
  | succ fuel recurse =>
      cases right with
      | nil =>
          refine ⟨0, ?_, ?_⟩
          · exact (poly_restore_denote context leftAccumulator left).symm.trans (Nat.add_zero _).symm
          · exact (Nat.zero_add _).trans
              ((poly_reverse_denote context rightAccumulator).symm.trans (Nat.add_zero _).symm)
      | cons rightHead rightTail =>
          cases left with
          | nil =>
              refine ⟨0, ?_, ?_⟩
              · exact (Nat.zero_add _).trans
                  ((poly_reverse_denote context leftAccumulator).symm.trans (Nat.add_zero _).symm)
              · exact (poly_restore_denote context rightAccumulator (rightHead :: rightTail)).symm.trans
                  (Nat.add_zero _).symm
          | cons leftHead leftTail =>
              obtain ⟨leftCoefficient, leftVariable⟩ := leftHead
              obtain ⟨rightCoefficient, rightVariable⟩ := rightHead
              cases forward : Nat.blt leftVariable rightVariable with
              | true =>
                  obtain ⟨common, leftRetained, rightRetained⟩ :=
                    recurse leftTail ((rightCoefficient, rightVariable) :: rightTail)
                      ((leftCoefficient, leftVariable) :: leftAccumulator) rightAccumulator
                  refine ⟨common, ?_, ?_⟩
                  · rw [Poly.cancelAux, forward]
                    exact (move_head _ _ _).trans leftRetained
                  · rw [Poly.cancelAux, forward]
                    exact rightRetained
              | false =>
                  cases backward : Nat.blt rightVariable leftVariable with
                  | true =>
                      obtain ⟨common, leftRetained, rightRetained⟩ :=
                        recurse ((leftCoefficient, leftVariable) :: leftTail) rightTail
                          leftAccumulator ((rightCoefficient, rightVariable) :: rightAccumulator)
                      refine ⟨common, ?_, ?_⟩
                      · rw [Poly.cancelAux, forward, backward]
                        exact leftRetained
                      · rw [Poly.cancelAux, forward, backward]
                        exact (move_head _ _ _).trans rightRetained
                  | false =>
                      have sameVariable := equal_of_blt_false forward backward
                      subst rightVariable
                      cases smallerLeft : Nat.blt leftCoefficient rightCoefficient with
                      | true =>
                          obtain ⟨common, leftRetained, rightRetained⟩ :=
                            recurse leftTail rightTail leftAccumulator
                              ((rightCoefficient - leftCoefficient, leftVariable) :: rightAccumulator)
                          refine ⟨leftCoefficient * Var.denote context leftVariable + common, ?_, ?_⟩
                          · rw [Poly.cancelAux, forward, smallerLeft]
                            exact (Nat.add_assoc _ _ _).trans (extend_common _ leftRetained)
                          · rw [Poly.cancelAux, forward, smallerLeft]
                            have coefficientBound : leftCoefficient ≤ rightCoefficient :=
                              Nat.le_of_lt (Nat.le_of_ble_eq_true smallerLeft)
                            calc
                              (rightCoefficient * Var.denote context leftVariable + Poly.denote context rightTail) +
                                  rightAccumulator.denote context =
                                ((leftCoefficient * Var.denote context leftVariable +
                                  (rightCoefficient - leftCoefficient) * Var.denote context leftVariable) +
                                  Poly.denote context rightTail) + rightAccumulator.denote context :=
                                congrArg (fun value : Nat => (value + Poly.denote context rightTail) +
                                  rightAccumulator.denote context)
                                  (scaled_reconstruction _ _ _ coefficientBound)
                              _ = leftCoefficient * Var.denote context leftVariable +
                                (Poly.denote context rightTail +
                                  ((rightCoefficient - leftCoefficient) * Var.denote context leftVariable +
                                    rightAccumulator.denote context)) := split_head _ _ _ _
                              _ = _ := extend_common _ rightRetained
                      | false =>
                          cases smallerRight : Nat.blt rightCoefficient leftCoefficient with
                          | true =>
                              obtain ⟨common, leftRetained, rightRetained⟩ :=
                                recurse leftTail rightTail
                                  ((leftCoefficient - rightCoefficient, leftVariable) :: leftAccumulator)
                                  rightAccumulator
                              refine ⟨rightCoefficient * Var.denote context leftVariable + common, ?_, ?_⟩
                              · rw [Poly.cancelAux, forward, smallerLeft, smallerRight]
                                have coefficientBound : rightCoefficient ≤ leftCoefficient :=
                                  Nat.le_of_lt (Nat.le_of_ble_eq_true smallerRight)
                                calc
                                  (leftCoefficient * Var.denote context leftVariable + Poly.denote context leftTail) +
                                      leftAccumulator.denote context =
                                    ((rightCoefficient * Var.denote context leftVariable +
                                      (leftCoefficient - rightCoefficient) * Var.denote context leftVariable) +
                                      Poly.denote context leftTail) + leftAccumulator.denote context :=
                                    congrArg (fun value : Nat => (value + Poly.denote context leftTail) +
                                      leftAccumulator.denote context)
                                      (scaled_reconstruction _ _ _ coefficientBound)
                                  _ = rightCoefficient * Var.denote context leftVariable +
                                    (Poly.denote context leftTail +
                                      ((leftCoefficient - rightCoefficient) * Var.denote context leftVariable +
                                        leftAccumulator.denote context)) := split_head _ _ _ _
                                  _ = _ := extend_common _ leftRetained
                              · rw [Poly.cancelAux, forward, smallerLeft, smallerRight]
                                exact (Nat.add_assoc _ _ _).trans (extend_common _ rightRetained)
                          | false =>
                              have sameCoefficient := equal_of_blt_false smallerLeft smallerRight
                              subst rightCoefficient
                              obtain ⟨common, leftRetained, rightRetained⟩ :=
                                recurse leftTail rightTail leftAccumulator rightAccumulator
                              refine ⟨leftCoefficient * Var.denote context leftVariable + common, ?_, ?_⟩
                              · rw [Poly.cancelAux, forward, smallerLeft]
                                exact (Nat.add_assoc _ _ _).trans (extend_common _ leftRetained)
                              · rw [Poly.cancelAux, forward, smallerLeft]
                                exact (Nat.add_assoc _ _ _).trans (extend_common _ rightRetained)

/-- Original polynomial cancellation removes one common natural scalar.

Its finite traversal starts with the exact empty accumulators and retains
both original input polynomials and both original output polynomials. -/
private theorem poly_cancel_common (context : Context) (left right : Poly) :
    ∃ common : Nat,
      left.denote context = (Poly.cancel left right).1.denote context + common ∧
      right.denote context = (Poly.cancel left right).2.denote context + common := by
  obtain ⟨common, leftRetained, rightRetained⟩ :=
    poly_cancelAux_common context hugeFuel left right [] []
  exact ⟨common, (Nat.add_zero _).symm.trans leftRetained,
    (Nat.add_zero _).symm.trans rightRetained⟩

/-- Original cancellation preserves and reflects equality of scalar denotations.

The same natural contribution is removed on both sides. Direct addition
cancellation recovers the output equality without identifying propositions. -/
private theorem poly_cancel_eq_iff (context : Context) (left right : Poly) :
    Poly.denote_eq context (Poly.cancel left right) ↔ Poly.denote_eq context (left, right) := by
  obtain ⟨common, leftRetained, rightRetained⟩ := poly_cancel_common context left right
  constructor
  · intro equal
    exact leftRetained.trans
      ((congrArg (fun value : Nat => value + common) equal).trans rightRetained.symm)
  · intro equal
    exact Addition.add_right_cancel (leftRetained.symm.trans (equal.trans rightRetained))

/-- Original cancellation preserves and reflects ordering of scalar denotations.

Both sides retain the same removed natural contribution. Monotonicity and
direct natural addition cancellation transport precisely that common sum. -/
private theorem poly_cancel_le_iff (context : Context) (left right : Poly) :
    Poly.denote_le context (Poly.cancel left right) ↔ Poly.denote_le context (left, right) := by
  obtain ⟨common, leftRetained, rightRetained⟩ := poly_cancel_common context left right
  constructor
  · intro ordered
    change left.denote context ≤ right.denote context
    rw [leftRetained, rightRetained]
    exact Nat.add_le_add_right ordered common
  · intro ordered
    have retainedBound : (Poly.cancel left right).1.denote context + common ≤
        (Poly.cancel left right).2.denote context + common := by
      rw [← leftRetained, ← rightRetained]
      exact ordered
    obtain ⟨difference, reconstructed⟩ := Nat.le.dest retainedBound
    have orderedDifference : (Poly.cancel left right).1.denote context + difference =
        (Poly.cancel left right).2.denote context := by
      apply Addition.add_right_cancel (common := common)
      exact (Nat.add_right_comm _ _ _).trans reconstructed
    exact Nat.le.intro orderedDifference

/-- Original natural-expression normalization preserves its scalar value.

The original expression conversion and coefficient-insertion fold retain the
same context values. Their scalar certificates compose without proposition transport. -/
private theorem natExpr_denote_toNormPoly (context : Context) (expression : Expr) :
    expression.toNormPoly.denote context = expression.denote context :=
  (poly_norm_denote context expression.toPoly).trans
    (Purelib.Tactic.Omega.NatLinear.natExpr_denote_toPoly context expression)

end Purelib.Tactic.QuotientFreeOmega

open Purelib.Tactic.QuotientFreeOmega
  (natExpr_denote_toNormPoly poly_cancel_le_iff poly_cancel_eq_iff)

namespace Purelib.Tactic.Omega.NatLinear

/-- Normalized natural-linear constraints preserve and reflect their denotation.

The original normalization and cancellation retain the same scalar expression
values. Equality and ordering are transported in both directions as logical implications. -/
theorem natExprCnstr_denote_toNormPoly (context : Context)
    (constraint : ExprCnstr) :
    constraint.toNormPoly.denote context ↔ constraint.denote context := by
  cases constraint with
  | mk equality left right =>
      cases equality with
      | false =>
          change Poly.denote_le context (Poly.cancel left.toNormPoly right.toNormPoly) ↔
            left.denote context ≤ right.denote context
          have leftRetained := natExpr_denote_toNormPoly context left
          have rightRetained := natExpr_denote_toNormPoly context right
          constructor
          · intro normalized
            have ordered := (poly_cancel_le_iff context left.toNormPoly right.toNormPoly).mp normalized
            change left.toNormPoly.denote context ≤ right.toNormPoly.denote context at ordered
            rw [leftRetained, rightRetained] at ordered
            exact ordered
          · intro ordered
            apply (poly_cancel_le_iff context left.toNormPoly right.toNormPoly).mpr
            change left.toNormPoly.denote context ≤ right.toNormPoly.denote context
            rw [leftRetained, rightRetained]
            exact ordered
      | true =>
          change Poly.denote_eq context (Poly.cancel left.toNormPoly right.toNormPoly) ↔
            left.denote context = right.denote context
          have leftRetained := natExpr_denote_toNormPoly context left
          have rightRetained := natExpr_denote_toNormPoly context right
          constructor
          · intro normalized
            have equal := (poly_cancel_eq_iff context left.toNormPoly right.toNormPoly).mp normalized
            exact leftRetained.symm.trans (equal.trans rightRetained)
          · intro equal
            apply (poly_cancel_eq_iff context left.toNormPoly right.toNormPoly).mpr
            exact leftRetained.trans (equal.trans rightRetained.symm)

/-- Check whether a natural polynomial constraint is syntactically valid.

An equality requires both original coefficient lists to be empty. An ordering
requires only its original left list to be empty; no coefficient data is reconstructed. -/
@[expose] public def isValid (constraint : PolyCnstr) : Bool :=
  match constraint.eq with
  | false =>
      match constraint.lhs with
      | [] => true
      | _ :: _ => false
  | true =>
      match constraint.lhs with
      | [] =>
          match constraint.rhs with
          | [] => true
          | _ :: _ => false
      | _ :: _ => false

end Purelib.Tactic.Omega.NatLinear

namespace Purelib.Tactic.QuotientFreeOmega

/-- A successful syntactic polynomial check supplies its actual denotation.

Empty equality sides have equal zero values. An empty ordering left side is
bounded by every natural right value; impossible Boolean branches are discharged directly. -/
private theorem poly_denote_of_isValid (context : Context) (constraint : PolyCnstr)
    (valid : Purelib.Tactic.Omega.NatLinear.isValid constraint = true) :
    constraint.denote context := by
  cases constraint with
  | mk equality left right =>
      cases equality with
      | false =>
          cases left with
          | nil => exact Nat.zero_le _
          | cons head tail =>
              change false = true at valid
              nomatch valid
      | true =>
          cases left with
          | cons head tail =>
              change false = true at valid
              nomatch valid
          | nil =>
              cases right with
              | nil => rfl
              | cons head tail =>
                  change false = true at valid
                  nomatch valid

end Purelib.Tactic.QuotientFreeOmega

namespace Purelib.Tactic.Omega.NatLinear

/-- A successful normalized natural-linear check supplies the original constraint proof.

The checker examines the retained normalized polynomial lists. Its direct
validity witness is transported back by the normalization equivalence. -/
theorem natExprCnstr_denote_of_isValid (context : Context)
    (constraint : ExprCnstr)
    (valid : isValid constraint.toNormPoly = true) :
    constraint.denote context :=
  (natExprCnstr_denote_toNormPoly context constraint).mp
    (Purelib.Tactic.QuotientFreeOmega.poly_denote_of_isValid context constraint.toNormPoly valid)

end Purelib.Tactic.Omega.NatLinear

end

end

end
