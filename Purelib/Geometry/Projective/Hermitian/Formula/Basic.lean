module
import Purelib.Data.Bool.Decide
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Hermitian.Atom
import Init.Prelude

public section

open Purelib

open Purelib.Geometry.Projective

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib.Geometry.Projective.Hermitian.Formula

set_option genInjectivity false in
/-- Finite Boolean formulas over rational Hermitian sign atoms. -/
inductive BoundaryFormula where
  /-- A formula true at every Gaussian rational. -/ | truth
  /-- A formula false at every Gaussian rational. -/ | falsity
  /-- One Hermitian form sign test. -/ | atom (value : Hermitian.Atom)
  /-- Conjunction of two finite boundary formulas. -/ | and (left right :
    BoundaryFormula)
  /-- Disjunction of two finite boundary formulas. -/ | or (left right :
    BoundaryFormula)
deriving DecidableEq

constructive_injectivity BoundaryFormula

namespace BoundaryFormula

/-- Interpret a finite Hermitian formula as a proposition at a Gaussian rational.

Truth and falsity have their logical meanings, atoms evaluate their sign tests, and the binary constructors use
conjunction and disjunction. -/
@[expose] def Holds :
  BoundaryFormula → Data.Gaussian.Basic.Canonical → Prop
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.truth, _ => True
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.falsity, _ => False
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.atom testAtom, value => testAtom.Holds value
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.and left right, value => left.Holds value ∧ right.Holds value
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.or left right, value => left.Holds value ∨ right.Holds value

/-- Conjoin a finite list of boundary formulas, with truth for the empty list. -/
@[expose] def all : List
  BoundaryFormula →
  BoundaryFormula
  | [] => Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula.truth
  | formula :: formulas => Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula.and formula
    (all formulas)

/-- Disjoin a finite list of boundary formulas, with falsity for the empty list. -/
@[expose] def any : List
  BoundaryFormula →
  BoundaryFormula
  | [] => Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula.falsity
  | formula :: formulas => Purelib.Geometry.Projective.Hermitian.Formula.BoundaryFormula.or formula
    (any formulas)

/-- The finite conjunction holds exactly when every member formula holds. -/
theorem holds_all (formulas : List
  BoundaryFormula) (value : Data.Gaussian.Basic.Canonical) :
    (all formulas).Holds value ↔
      ∀ formula ∈ formulas, formula.Holds value := by
  induction formulas with
  | nil =>
      constructor
      · intro _ formula member
        exact (List.not_mem_nil member).elim
      · intro _
        exact True.intro
  | cons formula formulas inductionHypothesis =>
      change (formula.Holds value ∧ (all formulas).Holds value) ↔
        ∀ item ∈ formula :: formulas, item.Holds value
      constructor
      · rintro ⟨headHolds, tailHolds⟩ item member
        rcases Purelib.Data.List.Membership.mem_cons.mp member with identity | tailMember
        · subst item
          exact headHolds
        · exact (inductionHypothesis.mp tailHolds) item tailMember
      · intro everyHolds
        exact
          ⟨everyHolds formula List.mem_cons_self,
            inductionHypothesis.mpr (fun item tailMember =>
              everyHolds item (List.mem_cons_of_mem formula tailMember))⟩

/-- The finite disjunction holds exactly when some member formula holds. -/
theorem holds_any (formulas : List
  BoundaryFormula) (value : Data.Gaussian.Basic.Canonical) :
    (any formulas).Holds value ↔
      ∃ formula ∈ formulas, formula.Holds value := by
  induction formulas with
  | nil =>
      constructor
      · intro falsehood
        exact falsehood.elim
      · rintro ⟨formula, member, _⟩
        exact (List.not_mem_nil member).elim
  | cons formula formulas inductionHypothesis =>
      change (formula.Holds value ∨ (any formulas).Holds value) ↔
        ∃ item ∈ formula :: formulas, item.Holds value
      constructor
      · intro holds
        rcases holds with headHolds | tailHolds
        · exact ⟨formula, List.mem_cons_self, headHolds⟩
        · rcases inductionHypothesis.mp tailHolds with
            ⟨item, member, itemHolds⟩
          exact
            ⟨item, List.mem_cons_of_mem formula member, itemHolds⟩
      · rintro ⟨item, member, itemHolds⟩
        rcases Purelib.Data.List.Membership.mem_cons.mp member with head | tail
        · subst item
          exact Or.inl itemHolds
        · exact
            Or.inr (inductionHypothesis.mpr ⟨item, tail, itemHolds⟩)

/-- Evaluate a finite Hermitian formula by exact rational sign decisions.

The Boolean recursion follows the formula constructors and combines their results with conjunction or disjunction. -/
@[expose] def evalBool :
  BoundaryFormula → Data.Gaussian.Basic.Canonical → Bool
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.truth, _ => true
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.falsity, _ => false
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.atom testAtom, value => decide (testAtom.Holds value)
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.and left right, value => left.evalBool value && right.evalBool
    value
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.or left right, value => left.evalBool value || right.evalBool
    value

/-- Boolean evaluation returns true exactly when the formula proposition holds. -/
theorem evalBool_eq_true (formula :
  BoundaryFormula) (value : Data.Gaussian.Basic.Canonical) :
    formula.evalBool value = true ↔ formula.Holds value := by
  induction formula with
  | truth => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | falsity => exact ⟨fun impossible => Bool.noConfusion impossible, fun impossible => impossible.elim⟩
  | atom atom =>
      change decide (atom.Holds value) = true ↔ atom.Holds value
      exact ⟨of_decide_eq_true, fun holds => decide_eq_true holds⟩
  | and left right leftHypothesis rightHypothesis =>
      exact (Purelib.Data.Bool.Decide.and_true_iff _ _).trans
        (and_congr leftHypothesis rightHypothesis)
  | or left right leftHypothesis rightHypothesis =>
      change (left.evalBool value || right.evalBool value) = true ↔ _
      constructor
      · intro accepted
        cases leftValue : left.evalBool value with
        | false =>
            cases rightValue : right.evalBool value with
            | false =>
                rewrite [leftValue, rightValue] at accepted
                exact Bool.noConfusion accepted
            | true => exact Or.inr (rightHypothesis.mp rightValue)
        | true => exact Or.inl (leftHypothesis.mp leftValue)
      · intro holds
        rcases holds with leftHolds | rightHolds
        · rewrite [leftHypothesis.mpr leftHolds]
          rfl
        · rewrite [rightHypothesis.mpr rightHolds]
          cases left.evalBool value <;> rfl

end BoundaryFormula

/-- Explicit finite list of all sign atoms occurring in a formula. -/
@[expose] def BoundaryFormula.atoms :
  BoundaryFormula → List Hermitian.Atom
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.truth |
    Geometry.Projective.Hermitian.Formula.BoundaryFormula.falsity => []
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.atom testAtom => [testAtom]
  | Geometry.Projective.Hermitian.Formula.BoundaryFormula.and left right |
    Geometry.Projective.Hermitian.Formula.BoundaryFormula.or left right =>
      left.atoms ++ right.atoms

end Purelib.Geometry.Projective.Hermitian.Formula

end
