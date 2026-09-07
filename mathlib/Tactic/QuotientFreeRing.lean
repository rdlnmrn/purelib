import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.NormNum.Pow

/-!
# Quotient-free ring normalization

Mathlib's ring normalizer is computational, but three proof lemmas emitted by
the tactic currently reach `Quot.sound`: integer-cast multiplication and
power in `norm_num`, and the generic AC normalizer's conversion of Boolean
list equality to propositional equality.  This module supplies direct
constructive replacements and a `ring0` frontend that substitutes them in the
generated proof term before the kernel checks it.

The normalizer and the replacement pass run only during elaboration.  The
stored theorem proof contains the explicit lemmas below, never the three
upstream quotient-bearing declarations.
-/

namespace QuotientFreeRing

/-- Integer casts preserve multiplication, proved by integer induction from
the additive cast laws rather than through upstream extensional simp
machinery. -/
theorem intCast_mul {R : Type*} [Ring R] (left right : Int) :
    ((left * right : Int) : R) = (left : R) * (right : R) := by
  induction left using Int.induction_on with
  | zero =>
      rw [Int.zero_mul, Int.cast_zero, zero_mul]
  | succ left ih =>
      calc
        (((((left : Nat) : Int) + 1) * right : Int) : R) =
            (((left : Int) * right : Int) : R) + ((1 * right : Int) : R) := by
          rw [Int.add_mul, Int.cast_add]
        _ = ((left : Nat) : R) * (right : R) + (right : R) := by
          rw [ih, Int.one_mul, Int.cast_natCast]
        _ = ((((left : Nat) : Int) + 1 : Int) : R) * (right : R) := by
          rw [Int.cast_add, Int.cast_one, Int.cast_natCast, add_mul, one_mul]
  | pred left ih =>
      calc
        (((-((left : Nat) : Int) - 1) * right : Int) : R) =
            ((-((left : Nat) : Int) * right : Int) : R) -
              ((1 * right : Int) : R) := by
          rw [Int.sub_mul, Int.cast_sub]
        _ = (-((left : Nat) : Int) : R) * (right : R) - (right : R) := by
          rw [ih, Int.one_mul, Int.cast_neg]
        _ = ((-((left : Nat) : Int) - 1 : Int) : R) * (right : R) := by
          rw [Int.cast_sub, Int.cast_one, Int.cast_neg, sub_mul, one_mul]

/-- Integer casts preserve natural powers, derived from the direct
multiplication proof above. -/
theorem intCast_pow {R : Type*} [Ring R] (value : Int) :
    ∀ exponent : Nat, ((value ^ exponent : Int) : R) = (value : R) ^ exponent
  | 0 => by rw [pow_zero, pow_zero, Int.cast_one]
  | exponent + 1 => by
      rw [pow_succ, pow_succ, intCast_mul, intCast_pow]

-- See Mathlib's note [norm_num lemma function equality].
theorem isInt_mul {R : Type*} [Ring R] :
    ∀ {f : R → R → R} {a b : R} {a' b' c : Int},
      f = HMul.hMul →
      Mathlib.Meta.NormNum.IsInt a a' →
      Mathlib.Meta.NormNum.IsInt b b' →
      Int.mul a' b' = c →
      Mathlib.Meta.NormNum.IsInt (a * b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl =>
      ⟨(intCast_mul _ _).symm⟩

-- See Mathlib's note [norm_num lemma function equality].
theorem isInt_pow {R : Type*} [Ring R] :
    ∀ {f : R → Nat → R} {a : R} {b : Nat} {a' : Int} {b' : Nat} {c : Int},
      f = HPow.hPow →
      Mathlib.Meta.NormNum.IsInt a a' →
      Mathlib.Meta.NormNum.IsNat b b' →
      Int.pow a' b' = c →
      Mathlib.Meta.NormNum.IsInt (f a b) c
  | _, _, _, _, _, _, rfl, ⟨rfl⟩, ⟨rfl⟩, rfl =>
      ⟨(intCast_pow _ _).symm⟩

/-- Boolean equality of natural-number lists reflects structural equality,
without requesting the generic `LawfulBEq (List Nat)` instance. -/
theorem listNat_eq_of_beq : ∀ left right : List Nat,
    List.beq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, equality => Bool.noConfusion equality
  | _ :: _, [], equality => Bool.noConfusion equality
  | left :: leftTail, right :: rightTail, equality => by
      change ((left == right) && List.beq leftTail rightTail) = true at equality
      have parts : (left == right) = true ∧
          List.beq leftTail rightTail = true :=
        Eq.mp (Bool.and_eq_true _ _) equality
      have headEquality : (left == right) = true := parts.1
      have tailEquality : List.beq leftTail rightTail = true := parts.2
      rw [of_decide_eq_true headEquality,
        listNat_eq_of_beq leftTail rightTail tailEquality]

/-- The AC normalizer's soundness step with its finite Boolean equality
certificate decoded directly. -/
theorem ac_eq_of_norm {R : Sort u} (context : Lean.Data.AC.Context R)
    (left right : Lean.Data.AC.Expr)
    (equalNormalForms :
      Lean.Data.AC.norm context left == Lean.Data.AC.norm context right) :
    Lean.Data.AC.eval R context left = Lean.Data.AC.eval R context right := by
  have normalFormsEqual :
      Lean.Data.AC.norm context left = Lean.Data.AC.norm context right :=
    listNat_eq_of_beq _ _ equalNormalForms
  calc
    Lean.Data.AC.eval R context left =
        Lean.Data.AC.evalList R context (Lean.Data.AC.norm context left) :=
      (Lean.Data.AC.Context.eval_norm context left).symm
    _ = Lean.Data.AC.evalList R context (Lean.Data.AC.norm context right) :=
      congrArg (Lean.Data.AC.evalList R context) normalFormsEqual
    _ = Lean.Data.AC.eval R context right :=
      Lean.Data.AC.Context.eval_norm context right

open Lean Elab Tactic Meta Mathlib.Tactic

/-- Replace the three quotient-bearing proof roots emitted by Mathlib's ring
normalizer with the direct constructive lemmas above. -/
private meta def replaceProofRoots (proof : Expr) : Expr :=
  proof.replace fun
    | .const ``Mathlib.Meta.NormNum.isInt_mul levels =>
        some (.const ``QuotientFreeRing.isInt_mul levels)
    | .const ``Mathlib.Meta.NormNum.isInt_pow levels =>
        some (.const ``QuotientFreeRing.isInt_pow levels)
    | .const ``Lean.Data.AC.Context.eq_of_norm levels =>
        some (.const ``QuotientFreeRing.ac_eq_of_norm levels)
    | _ => none

/-- Run the upstream normalizer and replace its quotient-bearing proof roots
before assigning the resulting proof. -/
private meta def proveEq (goal : MVarId) (transparency : TransparencyMode) : MetaM Unit := do
  let proofGoal ← mkFreshExprMVar (← goal.getType)
  Mathlib.Tactic.AtomM.run transparency
    (Mathlib.Tactic.Ring.proveEq proofGoal.mvarId!)
  let proof ← instantiateMVars proofGoal
  goal.assign (replaceProofRoots proof)

/-- Quotient-free frontend for Mathlib's computational ring normalizer. -/
elab (name := quotientFreeRing) "ring0" bang:"!"? : tactic =>
  liftMetaMAtMain fun goal => do
    proveEq goal (if bang.isSome then .default else .reducible)

/-! Importing this module also upgrades existing `ring1` source without a
cosmetic tactic rename.  The later elaboration rule takes precedence over
Mathlib's frontend while retaining exactly the same syntax. -/
elab_rules : tactic
  | `(tactic| ring1 $[!%$bang]?) =>
      liftMetaMAtMain fun goal => do
        proveEq goal (if bang.isSome then .default else .reducible)

/-- Kernel-checked regression covering AC normalization, negative integer
coefficients, multiplication, and powers through the overridden spelling. -/
theorem ring1_regression {R : Type*} [CommRing R] (value : R) :
    (-2 : R) * (value + 1) ^ 2 =
      -2 * value ^ 2 - 4 * value - 2 := by
  ring1

end QuotientFreeRing
