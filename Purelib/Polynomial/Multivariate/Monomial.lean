module

import Init.Data.Nat.Compare
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite monomial exponent vectors

An arity-indexed structural vector retains one natural exponent per original
variable. Lexicographic comparison and componentwise addition recurse on that
vector, without function equality or a choice of a variable enumeration.
-/

public section

namespace Purelib.Polynomial.Multivariate

set_option genInjectivity false in
/-- A monomial with one natural exponent for each of its finitely indexed variables. -/
inductive Monomial : Nat → Type where
  /-- The unique exponent vector in zero variables. -/
  | nil : Monomial 0
  /-- Retain the first variable's exponent and the remaining exponent vector. -/
  | cons {arity : Nat} (exponent : Nat) (tail : Monomial arity) : Monomial (arity + 1)
  deriving @[expose] DecidableEq

constructive_injectivity Monomial

namespace Monomial

/-- Every variable with a nonzero original exponent satisfies the supplied availability condition. -/
@[expose] def Supported : {arity : Nat} → Monomial arity → (Fin arity → Prop) → Prop
  | 0, .nil, _ => True
  | _ + 1, .cons exponent remaining, available =>
      (exponent = 0 ∨ available 0) ∧ Supported remaining (fun index => available index.succ)

/-- Decide required-variable availability by the original structural exponent vector. -/
instance supportedDecidable : {arity : Nat} → (monomial : Monomial arity) →
    (available : Fin arity → Prop) → [∀ index, Decidable (available index)] → Decidable (Supported monomial available)
  | 0, .nil, _, _ => isTrue True.intro
  | arity + 1, .cons exponent remaining, available, decisions =>
      letI : ∀ index : Fin arity, Decidable (available index.succ) := fun index => decisions index.succ
      letI := supportedDecidable remaining (fun index => available index.succ)
      inferInstanceAs (Decidable ((exponent = 0 ∨ available 0) ∧ Supported remaining _))

/-- Availability of every original variable supplies the monomial's required support. -/
theorem supported_all : {arity : Nat} → (monomial : Monomial arity) →
    (available : Fin arity → Prop) → (∀ index, available index) → Supported monomial available
  | 0, .nil, _, _ => True.intro
  | _ + 1, .cons _ remaining, available, ready =>
      ⟨Or.inr (ready 0), supported_all remaining (fun index => available index.succ) (fun index => ready index.succ)⟩

/-- The exponent vector of the constant monomial. -/
@[expose] def zero : (arity : Nat) → Monomial arity
  | 0 => .nil
  | arity + 1 => .cons 0 (zero arity)

/-- The degree-one monomial belonging to the displayed original variable index. -/
@[expose] def atom : (arity : Nat) → Fin arity → Monomial arity
  | 0, index => nomatch index
  | arity + 1, index =>
      Fin.cases (.cons 1 (zero arity)) (fun tail => .cons 0 (atom arity tail)) index

/-- Add the exponents of two monomials of the same arity. -/
@[expose] def add : {arity : Nat} → Monomial arity → Monomial arity → Monomial arity
  | 0, .nil, .nil => .nil
  | _ + 1, .cons first tail, .cons second remaining => .cons (first + second) (add tail remaining)

/-- Strict lexicographic order on the displayed finite exponent vectors. -/
@[expose] def Less : {arity : Nat} → Monomial arity → Monomial arity → Prop
  | 0, .nil, .nil => False
  | _ + 1, .cons first tail, .cons second remaining =>
      first < second ∨ (first = second ∧ Less tail remaining)

/-- Decide lexicographic monomial order by structural comparison of its coordinates. -/
instance lessDecidable : {arity : Nat} → (left right : Monomial arity) → Decidable (Less left right)
  | 0, .nil, .nil => isFalse (fun impossible => impossible)
  | _ + 1, .cons first tail, .cons second remaining =>
      letI := lessDecidable tail remaining
      inferInstanceAs (Decidable (first < second ∨ (first = second ∧ Less tail remaining)))

/-- No finite exponent vector is lexicographically smaller than itself. -/
theorem less_irrefl {arity : Nat} (monomial : Monomial arity) : ¬ Less monomial monomial := by
  induction monomial with
  | nil => exact fun impossible => impossible
  | cons exponent tail ih =>
      intro smaller
      cases smaller with
      | inl smaller => omega0
      | inr same => exact ih same.2

/-- Lexicographic order on finite exponent vectors is transitive. -/
theorem less_trans {arity : Nat} {first second third : Monomial arity}
    (left : Less first second) (right : Less second third) : Less first third := by
  induction first with
  | nil => cases second; exact False.elim left
  | cons a firstTail ih =>
      cases second with
      | cons b secondTail =>
          cases third with
          | cons c thirdTail =>
              cases left with
              | inl ab =>
                  cases right with
                  | inl bc => exact Or.inl (by omega0)
                  | inr bc => exact Or.inl (by omega0)
              | inr ab =>
                  cases right with
                  | inl bc => exact Or.inl (by omega0)
                  | inr bc => exact Or.inr ⟨ab.1.trans bc.1, ih ab.2 bc.2⟩

/-- Distinct finite exponent vectors have one of the two strict lexicographic orders. -/
theorem less_total {arity : Nat} (left right : Monomial arity) :
    Less left right ∨ left = right ∨ Less right left := by
  induction left with
  | nil => cases right; exact Or.inr (Or.inl rfl)
  | cons first tail ih =>
      cases right with
      | cons second remaining =>
          if smaller : first < second then exact Or.inl (Or.inl smaller)
          else if greater : second < first then exact Or.inr (Or.inr (Or.inl greater))
          else
            have same : first = second := by omega0
            subst second
            cases ih remaining with
            | inl smaller => exact Or.inl (Or.inr ⟨rfl, smaller⟩)
            | inr rest =>
                cases rest with
                | inl sameTail => exact Or.inr (Or.inl (congrArg (Monomial.cons first) sameTail))
                | inr greater => exact Or.inr (Or.inr (Or.inr ⟨rfl, greater⟩))

/-- If neither equality nor increasing order holds, the reverse strict order holds. -/
theorem less_of_not_less_of_ne {arity : Nat} {left right : Monomial arity}
    (notLess : ¬ Less left right) (different : left ≠ right) : Less right left := by
  cases less_total left right with
  | inl smaller => exact False.elim (notLess smaller)
  | inr rest =>
      cases rest with
      | inl same => exact False.elim (different same)
      | inr greater => exact greater

/-- Lexicographic order excludes the opposite strict order. -/
theorem not_less_reverse {arity : Nat} {left right : Monomial arity} (smaller : Less left right) :
    ¬ Less right left := fun greater => less_irrefl left (less_trans smaller greater)

/-- Componentwise exponent addition preserves the original vector when its right input is zero. -/
theorem add_zero {arity : Nat} (monomial : Monomial arity) : add monomial (zero arity) = monomial := by
  induction monomial with
  | nil => rfl
  | cons exponent tail ih => exact congrArg (Monomial.cons exponent) ih

/-- Componentwise exponent addition preserves the original vector when its left input is zero. -/
theorem zero_add {arity : Nat} (monomial : Monomial arity) : add (zero arity) monomial = monomial := by
  induction monomial with
  | nil => rfl
  | cons exponent tail ih =>
      change Monomial.cons (0 + exponent) _ = _
      rewrite [Nat.zero_add]
      exact congrArg (Monomial.cons exponent) ih

/-- Componentwise addition of finite exponent vectors is commutative. -/
theorem add_comm {arity : Nat} (left right : Monomial arity) : add left right = add right left := by
  induction left with
  | nil => cases right; rfl
  | cons first tail ih =>
      cases right with
      | cons second remaining =>
          change Monomial.cons (first + second) _ = _
          rewrite [Nat.add_comm first second, ih remaining]
          rfl

/-- Componentwise addition of finite exponent vectors is associative. -/
theorem add_assoc {arity : Nat} (first second third : Monomial arity) :
    add (add first second) third = add first (add second third) := by
  induction first with
  | nil => cases second; cases third; rfl
  | cons a firstTail ih =>
      cases second with
      | cons b secondTail =>
          cases third with
          | cons c thirdTail =>
              change Monomial.cons ((a + b) + c) _ = _
              rewrite [Nat.add_assoc, ih secondTail thirdTail]
              rfl

end Monomial

end Purelib.Polynomial.Multivariate

end
