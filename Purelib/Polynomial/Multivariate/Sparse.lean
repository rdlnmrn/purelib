module

import Purelib.Data.List.Membership
public import Purelib.Polynomial.Multivariate.Monomial
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Canonical finite sparse polynomials

Each term retains a coefficient and an exponent vector in the original finite
variable order. Insertion combines equal monomials and removes zero coefficients;
every public polynomial carries the strict-order and nonzero-coefficient proof.
The executable operations do not require a completed polynomial ring or quotient.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.List.Membership (mem_cons)

set_option genInjectivity false in
/-- One coefficient attached to a finite monomial in the original variable order. -/
structure Term (R : Type) (arity : Nat) where
  /-- The exponent vector of this occurrence. -/
  monomial : Monomial arity
  /-- The exact coefficient of this occurrence. -/
  coefficient : R
  deriving @[expose] DecidableEq

constructive_injectivity Term

namespace Terms

variable {R : Type} {arity : Nat}

/-- Every term is strictly above a displayed monomial in lexicographic order. -/
@[expose] def Above (lower : Monomial arity) : List (Term R arity) → Prop
  | [] => True
  | first :: remaining => Monomial.Less lower first.monomial ∧ Above lower remaining

/-- A finite term list has nonzero coefficients and strictly increasing monomials. -/
@[expose] def Canonical [Zero R] : List (Term R arity) → Prop
  | [] => True
  | first :: remaining => first.coefficient ≠ 0 ∧ Above first.monomial remaining ∧ Canonical remaining

/-- Insert one term, combining its coefficient with an existing equal monomial.

Zero input and combined coefficients are removed. The original suffix is
retained as soon as insertion or cancellation finishes. -/
@[expose] def insert [Zero R] [Add R] [DecidableEq R] (term : Term R arity) :
    List (Term R arity) → List (Term R arity)
  | [] => if term.coefficient = 0 then [] else [term]
  | first :: remaining =>
      if term.coefficient = 0 then first :: remaining
      else if Monomial.Less term.monomial first.monomial then term :: first :: remaining
      else if term.monomial = first.monomial then
        if term.coefficient + first.coefficient = 0 then remaining
        else ⟨first.monomial, term.coefficient + first.coefficient⟩ :: remaining
      else first :: insert term remaining

/-- Transitivity moves a lower bound past a smaller intermediate monomial. -/
theorem above_trans {lower middle : Monomial arity} {terms : List (Term R arity)}
    (smaller : Monomial.Less lower middle) (above : Above middle terms) : Above lower terms := by
  induction terms with
  | nil => exact True.intro
  | cons first remaining ih => exact ⟨Monomial.less_trans smaller above.1, ih above.2⟩

/-- Inserting a term above the bound preserves every retained term's lower bound. -/
theorem insert_above [Zero R] [Add R] [DecidableEq R] (lower : Monomial arity)
    (term : Term R arity) (terms : List (Term R arity))
    (termAbove : Monomial.Less lower term.monomial) (above : Above lower terms) :
    Above lower (insert term terms) := by
  induction terms with
  | nil =>
      unfold insert
      split
      · exact True.intro
      · exact ⟨termAbove, True.intro⟩
  | cons first remaining ih =>
      unfold insert
      split
      · exact above
      · split
        · exact ⟨termAbove, above⟩
        · split
          · split
            · exact above.2
            · exact ⟨above.1, above.2⟩
          · exact ⟨above.1, ih above.2⟩

/-- Canonical insertion preserves strict monomial order and nonzero coefficients. -/
theorem insert_canonical [Zero R] [Add R] [DecidableEq R] (term : Term R arity)
    (terms : List (Term R arity)) (canonical : Canonical terms) : Canonical (insert term terms) := by
  induction terms with
  | nil =>
      unfold insert
      split
      · exact True.intro
      · rename_i nonzero
        exact ⟨nonzero, True.intro, True.intro⟩
  | cons first remaining ih =>
      unfold insert
      split
      · exact canonical
      · rename_i nonzero
        split
        · rename_i smaller
          exact ⟨nonzero, ⟨smaller, above_trans smaller canonical.2.1⟩, canonical⟩
        · rename_i notSmaller
          split
          · split
            · exact canonical.2.2
            · rename_i combinedNonzero
              exact ⟨combinedNonzero, canonical.2.1, canonical.2.2⟩
          · rename_i different
            have greater := Monomial.less_of_not_less_of_ne notSmaller different
            exact ⟨canonical.1, insert_above first.monomial term remaining greater canonical.2.1,
              ih canonical.2.2⟩

/-- Accumulate a finite list into an existing term list using canonical insertion. -/
@[expose] def accumulate [Zero R] [Add R] [DecidableEq R] :
    List (Term R arity) → List (Term R arity) → List (Term R arity)
  | [], result => result
  | first :: remaining, result => accumulate remaining (insert first result)

/-- Accumulation preserves a canonical accumulator even when its inputs are unordered. -/
theorem accumulate_canonical [Zero R] [Add R] [DecidableEq R]
    (input result : List (Term R arity)) (canonical : Canonical result) :
    Canonical (accumulate input result) := by
  induction input generalizing result with
  | nil => exact canonical
  | cons first remaining ih => exact ih _ (insert_canonical first result canonical)

/-- Multiply one term by every retained term and canonically insert the products. -/
@[expose] def multiplyTerm [Zero R] [Add R] [Mul R] [DecidableEq R] (term : Term R arity) :
    List (Term R arity) → List (Term R arity) → List (Term R arity)
  | [], result => result
  | first :: remaining, result =>
      multiplyTerm term remaining
        (insert ⟨Monomial.add term.monomial first.monomial, term.coefficient * first.coefficient⟩ result)

/-- Term multiplication preserves a canonical accumulator. -/
theorem multiplyTerm_canonical [Zero R] [Add R] [Mul R] [DecidableEq R]
    (term : Term R arity) (input result : List (Term R arity)) (canonical : Canonical result) :
    Canonical (multiplyTerm term input result) := by
  induction input generalizing result with
  | nil => exact canonical
  | cons first remaining ih => exact ih _ (insert_canonical _ result canonical)

/-- Accumulate the complete finite convolution of two term lists. -/
@[expose] def multiply [Zero R] [Add R] [Mul R] [DecidableEq R] :
    List (Term R arity) → List (Term R arity) → List (Term R arity) → List (Term R arity)
  | [], _, result => result
  | first :: remaining, right, result => multiply remaining right (multiplyTerm first right result)

/-- Finite convolution preserves a canonical accumulator. -/
theorem multiply_canonical [Zero R] [Add R] [Mul R] [DecidableEq R]
    (left right result : List (Term R arity)) (canonical : Canonical result) :
    Canonical (multiply left right result) := by
  induction left generalizing result with
  | nil => exact canonical
  | cons first remaining ih => exact ih _ (multiplyTerm_canonical first right result canonical)

/-- Every retained monomial satisfies the supplied scalar exponent-vector property. -/
@[expose] def MonomialsSatisfy (property : Monomial arity → Prop) : List (Term R arity) → Prop
  | [] => True
  | first :: remaining => property first.monomial ∧ MonomialsSatisfy property remaining

/-- Transport a finite monomial property through a pointwise implication. -/
theorem monomialsSatisfy_mono {first last : Monomial arity → Prop}
    (implies : ∀ monomial, first monomial → last monomial) :
    (terms : List (Term R arity)) → MonomialsSatisfy first terms → MonomialsSatisfy last terms
  | [], _ => True.intro
  | head :: tail, holds => ⟨implies head.monomial holds.1, monomialsSatisfy_mono implies tail holds.2⟩

/-- Read a monomial property at an actual occurrence in the retained finite list. -/
theorem monomialsSatisfy_of_mem (property : Monomial arity → Prop) :
    (terms : List (Term R arity)) → MonomialsSatisfy property terms →
    (term : Term R arity) → term ∈ terms → property term.monomial
  | [], _, _, present => by cases present
  | first :: remaining, holds, term, present => by
      cases mem_cons.mp present with
      | inl same => cases same; exact holds.1
      | inr later => exact monomialsSatisfy_of_mem property remaining holds.2 term later

/-- Properties at every actual retained occurrence supply the corresponding finite monomial predicate. -/
theorem monomialsSatisfy_of_forall_mem (property : Monomial arity → Prop) :
    (terms : List (Term R arity)) → (∀ term, term ∈ terms → property term.monomial) →
    MonomialsSatisfy property terms
  | [], _ => True.intro
  | first :: remaining, holds =>
      ⟨holds first (mem_cons.mpr (Or.inl rfl)),
        monomialsSatisfy_of_forall_mem property remaining
          (fun term present => holds term (mem_cons.mpr (Or.inr present)))⟩

/-- Canonical insertion preserves properties of the input and every original output monomial.

Combining equal monomials changes only their coefficient. Cancellation removes
an occurrence; no branch introduces a new exponent vector.
-/
theorem insert_monomialsSatisfy [Zero R] [Add R] [DecidableEq R]
    (property : Monomial arity → Prop) (term : Term R arity) (terms : List (Term R arity))
    (head : property term.monomial) (tail : MonomialsSatisfy property terms) :
    MonomialsSatisfy property (insert term terms) := by
  induction terms with
  | nil =>
      unfold insert
      split
      · exact True.intro
      · exact ⟨head, True.intro⟩
  | cons first remaining ih =>
      unfold insert
      split
      · exact tail
      · split
        · exact ⟨head, tail⟩
        · split
          · split
            · exact tail.2
            · exact tail
          · exact ⟨tail.1, ih tail.2⟩

/-- Canonical accumulation preserves a common property of both actual finite input lists. -/
theorem accumulate_monomialsSatisfy [Zero R] [Add R] [DecidableEq R]
    (property : Monomial arity → Prop) (input result : List (Term R arity))
    (head : MonomialsSatisfy property input) (tail : MonomialsSatisfy property result) :
    MonomialsSatisfy property (accumulate input result) := by
  induction input generalizing result with
  | nil => exact tail
  | cons first remaining ih =>
      exact ih _ head.2 (insert_monomialsSatisfy property first result head.1 tail)

/-- A retained monomial property survives multiplication by one term and canonical insertion. -/
theorem multiplyTerm_monomialsSatisfy [Zero R] [Add R] [Mul R] [DecidableEq R]
    (property : Monomial arity → Prop) (term : Term R arity) (input result : List (Term R arity))
    (products : MonomialsSatisfy (fun monomial => property (Monomial.add term.monomial monomial)) input)
    (retained : MonomialsSatisfy property result) :
    MonomialsSatisfy property (multiplyTerm term input result) := by
  induction input generalizing result with
  | nil => exact retained
  | cons first remaining ih =>
      exact ih _ products.2 (insert_monomialsSatisfy property _ result products.1 retained)

/-- Every surviving canonical convolution monomial satisfies the supplied property of each actual product. -/
theorem multiply_monomialsSatisfy [Zero R] [Add R] [Mul R] [DecidableEq R]
    (property : Monomial arity → Prop) (left right result : List (Term R arity))
    (products : MonomialsSatisfy
      (fun first => MonomialsSatisfy (fun second => property (Monomial.add first second)) right) left)
    (retained : MonomialsSatisfy property result) :
    MonomialsSatisfy property (multiply left right result) := by
  induction left generalizing result with
  | nil => exact retained
  | cons first remaining ih =>
      exact ih _ products.2 (multiplyTerm_monomialsSatisfy property first right result products.1 retained)

end Terms

set_option genInjectivity false in
/-- A finite sparse polynomial carrying its canonical monomial and coefficient invariants. -/
structure Sparse (R : Type) [Zero R] (arity : Nat) where
  /-- The original finite, strictly ordered coefficient list. -/
  terms : List (Term R arity)
  /-- Every coefficient is nonzero and every monomial occurs in strict increasing order. -/
  canonical : Terms.Canonical terms

constructive_injectivity Sparse

namespace Sparse

variable {R : Type} [Zero R] [Add R] [DecidableEq R] {arity : Nat}

/-- Canonical zero retains an empty term list at the original arity. -/
@[expose] def zero : Sparse R arity := ⟨[], True.intro⟩

/-- Canonicalize an arbitrary finite coefficient list by insertion into zero. -/
@[expose] def ofTerms (terms : List (Term R arity)) : Sparse R arity :=
  ⟨Terms.accumulate terms [], Terms.accumulate_canonical terms [] True.intro⟩

/-- A scalar polynomial at the displayed original arity. -/
@[expose] def constant (value : R) : Sparse R arity := ofTerms [⟨Monomial.zero arity, value⟩]

/-- A degree-one polynomial at its original finite variable index. -/
@[expose] def atom [One R] (index : Fin arity) : Sparse R arity :=
  ofTerms [⟨Monomial.atom arity index, 1⟩]

/-- Add two canonical polynomials using their retained term lists. -/
@[expose] def add (left right : Sparse R arity) : Sparse R arity :=
  ⟨Terms.accumulate left.terms right.terms, Terms.accumulate_canonical left.terms right.terms right.canonical⟩

/-- Negate the coefficients and canonically retain the resulting finite terms. -/
@[expose] def neg [Neg R] (input : Sparse R arity) : Sparse R arity :=
  ofTerms (input.terms.map (fun term => ⟨term.monomial, -term.coefficient⟩))

/-- Subtract two finite sparse polynomials by coefficient negation and addition. -/
@[expose] def sub [Neg R] (left right : Sparse R arity) : Sparse R arity := add left (neg right)

/-- Multiply two canonical polynomials with a complete finite convolution. -/
@[expose] def mul [Mul R] (left right : Sparse R arity) : Sparse R arity :=
  ⟨Terms.multiply left.terms right.terms [], Terms.multiply_canonical left.terms right.terms [] True.intro⟩

/-- Compute a natural power using retained repeated finite multiplication. -/
@[expose] def pow [Mul R] [One R] (input : Sparse R arity) : Nat → Sparse R arity
  | 0 => constant 1
  | exponent + 1 => mul input (pow input exponent)

/-- Canonical construction preserves a property of every actual input monomial. -/
theorem ofTerms_monomialsSatisfy (property : Monomial arity → Prop) (terms : List (Term R arity))
    (holds : Terms.MonomialsSatisfy property terms) : Terms.MonomialsSatisfy property (ofTerms terms).terms :=
  Terms.accumulate_monomialsSatisfy property terms [] holds True.intro

/-- Canonical addition preserves a property of each original input monomial. -/
theorem add_monomialsSatisfy (property : Monomial arity → Prop) (left right : Sparse R arity)
    (first : Terms.MonomialsSatisfy property left.terms) (second : Terms.MonomialsSatisfy property right.terms) :
    Terms.MonomialsSatisfy property (left.add right).terms :=
  Terms.accumulate_monomialsSatisfy property left.terms right.terms first second

/-- Canonical multiplication preserves a property of every actual pair of input monomials. -/
theorem mul_monomialsSatisfy [Mul R] (property : Monomial arity → Prop) (left right : Sparse R arity)
    (products : Terms.MonomialsSatisfy
      (fun first => Terms.MonomialsSatisfy (fun second => property (Monomial.add first second)) right.terms)
      left.terms) :
    Terms.MonomialsSatisfy property (left.mul right).terms :=
  Terms.multiply_monomialsSatisfy property left.terms right.terms [] products True.intro

end Sparse

end Purelib.Polynomial.Multivariate

end
