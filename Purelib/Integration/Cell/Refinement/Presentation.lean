module

public import Purelib.Integration.Cell.Refinement
import Purelib.Data.List.Search
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Purelib.Integration.IntegrationSplit.Presentation

open Purelib.Data

/-- A proposed split has the original parent's weight and refines its range at every retained child. -/
@[expose] public def Valid {α : Type} (parent : IntegrationCell α)
    (children : List (IntegrationCell α)) : Prop :=
  integrationWeight children = parent.weight ∧
    (∀ child ∈ children, parent.lower ≤ child.lower) ∧
    (∀ child ∈ children, child.upper ≤ parent.upper)

set_option genInjectivity false in
/-- A split check returns the original certified split or a proved failure at the original data. -/
public inductive Check {α : Type} (parent : IntegrationCell α) (children : List (IntegrationCell α)) where
  /-- The original child list satisfies the split contract. -/
  | accepted (split : IntegrationSplit parent) (children_eq : split.children = children)
  /-- The proposed children do not conserve the original parent's weight. -/
  | wrongWeight (failed : integrationWeight children ≠ parent.weight)
  /-- An original bounded child occurrence violates the parent's lower bound. -/
  | lowerOutOfRange (index : Fin children.length) (failed : ¬ parent.lower ≤ (children.get index).lower)
  /-- An original bounded child occurrence violates the parent's upper bound. -/
  | upperOutOfRange (index : Fin children.length) (failed : ¬ (children.get index).upper ≤ parent.upper)

/-- Check the finite split conditions against the exact original parent and ordered children. -/
public def check {α : Type} (parent : IntegrationCell α) (children : List (IntegrationCell α)) :
    Check parent children :=
  if weight : integrationWeight children = parent.weight then
    match lowerResult : List.Search.firstOccurrence (fun child => ¬ parent.lower ≤ child.lower)
        (fun _ => inferInstance) children with
    | some occurrence =>
        .lowerOutOfRange occurrence.index (by
          rw [List.get_eq_getElem, ← occurrence.entry_eq]
          exact occurrence.accepted)
    | none =>
        have lower : ∀ child ∈ children, parent.lower ≤ child.lower := by
          intro child member
          by_cases valid : parent.lower ≤ child.lower
          · exact valid
          · have found := List.Search.firstAccepted (fun child => ¬ parent.lower ≤ child.lower)
              (fun _ => inferInstance) children ⟨child, member, valid⟩
            have impossible : none = some found.val := lowerResult.symm.trans found.property
            cases impossible
        match upperResult : List.Search.firstOccurrence (fun child => ¬ child.upper ≤ parent.upper)
            (fun _ => inferInstance) children with
        | some occurrence =>
            .upperOutOfRange occurrence.index (by
              rw [List.get_eq_getElem, ← occurrence.entry_eq]
              exact occurrence.accepted)
        | none =>
            have upper : ∀ child ∈ children, child.upper ≤ parent.upper := by
              intro child member
              by_cases valid : child.upper ≤ parent.upper
              · exact valid
              · have found := List.Search.firstAccepted (fun child => ¬ child.upper ≤ parent.upper)
                  (fun _ => inferInstance) children ⟨child, member, valid⟩
                have impossible : none = some found.val := upperResult.symm.trans found.property
                cases impossible
            .accepted ⟨children, weight, lower, upper⟩ rfl
  else .wrongWeight weight

/-- The typed result decides the three finite split conditions. -/
public def recognize {α : Type} (parent : IntegrationCell α) (children : List (IntegrationCell α)) :
    Decidable (Valid parent children) :=
  match check parent children with
  | .accepted split childrenEq => .isTrue (by
      subst children
      exact ⟨split.weight_conserved, split.lower_refines, split.upper_refines⟩)
  | .wrongWeight failed => .isFalse (fun valid => failed valid.1)
  | .lowerOutOfRange index failed => .isFalse (fun valid =>
      failed (valid.2.1 (children.get index) (List.getElem_mem index.isLt)))
  | .upperOutOfRange index failed => .isFalse (fun valid =>
      failed (valid.2.2 (children.get index) (List.getElem_mem index.isLt)))

/-- Quote the original split by projecting its retained ordered children and certificates. -/
@[expose] public def quote {α : Type} {parent : IntegrationCell α} (split : IntegrationSplit parent) :
    {children : List (IntegrationCell α) // Valid parent children} :=
  ⟨split.children, split.weight_conserved, split.lower_refines, split.upper_refines⟩

/-- Read validated ordered children as the original split owner. -/
@[expose] public def read {α : Type} {parent : IntegrationCell α}
    (display : {children : List (IntegrationCell α) // Valid parent children}) : IntegrationSplit parent :=
  ⟨display.val, display.property.1, display.property.2.1, display.property.2.2⟩

/-- Reading a split's quotation recovers the original owner, independent of proof witnesses. -/
public theorem read_quote {α : Type} {parent : IntegrationCell α} (split : IntegrationSplit parent) :
    read (quote split) = split := by
  cases split
  rfl

/-- Quotation after readback recovers the retained ordered children. -/
public theorem quote_read {α : Type} {parent : IntegrationCell α}
    (display : {children : List (IntegrationCell α) // Valid parent children}) :
    quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Original splits read equal exactly when their retained ordered children agree. -/
public theorem read_eq_iff {α : Type} {parent : IntegrationCell α}
    (left right : {children : List (IntegrationCell α) // Valid parent children}) :
    read left = read right ↔ left.val = right.val := by
  constructor
  · intro equal
    exact congrArg IntegrationSplit.children equal
  · intro equal
    cases Subtype.ext equal
    rfl

/-- A split is recognized with its original ordered children. -/
public theorem check_quote {α : Type} {parent : IntegrationCell α} (split : IntegrationSplit parent) :
    ∃ (found : IntegrationSplit parent) (equal : found.children = split.children),
      check parent split.children = .accepted found equal := by
  cases result : check parent split.children with
  | accepted found equal =>
      exact ⟨found, equal, rfl⟩
  | wrongWeight failed => exact False.elim (failed split.weight_conserved)
  | lowerOutOfRange index failed =>
      exact False.elim (failed (split.lower_refines _ (List.getElem_mem index.isLt)))
  | upperOutOfRange index failed =>
      exact False.elim (failed (split.upper_refines _ (List.getElem_mem index.isLt)))

end Purelib.Integration.IntegrationSplit.Presentation
