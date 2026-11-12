module

import Purelib.Data.List.Membership
import Purelib.Polynomial.Multivariate.Sparse
public import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.Ring

/-!
# Reduction at a retained finite-power relation

One bounded original variable satisfies a supplied equation `x^degree = q`.
Each monomial retains its other exponents, moves whole powers of `q` into its
coefficient, and keeps the selected exponent's natural remainder.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.List.Membership (mem_cons)

namespace Monomial

/-- Read an actual original bounded coordinate of the retained exponent vector. -/
@[expose] def exponentAt : {arity : Nat} → Monomial arity → Fin arity → Nat
  | 0, .nil, index => nomatch index
  | _ + 1, .cons exponent tail, index => Fin.cases exponent (fun next => exponentAt tail next) index

/-- The first coordinate of a nonempty exponent vector is its actual stored head. -/
theorem exponentAt_cons_zero {arity : Nat} (exponent : Nat) (remaining : Monomial arity) :
    (.cons exponent remaining : Monomial (arity + 1)).exponentAt 0 = exponent := rfl

/-- A successor coordinate reads the same actual suffix entry at its original bounded position. -/
theorem exponentAt_cons_succ {arity : Nat} (exponent : Nat) (remaining : Monomial arity) (index : Fin arity) :
    (.cons exponent remaining : Monomial (arity + 1)).exponentAt index.succ = remaining.exponentAt index := rfl

/-- A bound on every coordinate bounds the actual first exponent. -/
theorem exponentAt_head_lt {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
    (bounds : Fin (arity + 1) → Nat)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index) :
    exponent < bounds 0 :=
  Eq.mp (congrArg (fun value => value < bounds 0)
    (exponentAt_cons_zero exponent remaining)) (below 0)

/-- A bound on every coordinate bounds each actual suffix exponent at its original successor position. -/
theorem exponentAt_tail_lt {arity : Nat} (exponent : Nat) (remaining : Monomial arity)
    (bounds : Fin (arity + 1) → Nat)
    (below : ∀ index, (.cons exponent remaining : Monomial (arity + 1)).exponentAt index < bounds index)
    (index : Fin arity) : remaining.exponentAt index < bounds index.succ :=
  Eq.mp (congrArg (fun value => value < bounds index.succ)
    (exponentAt_cons_succ exponent remaining index)) (below index.succ)

/-- Replace one original bounded exponent while preserving every other coordinate. -/
@[expose] def withExponentAt : {arity : Nat} → Monomial arity → Fin arity → Nat → Monomial arity
  | 0, .nil, index, _ => Fin.elim0 index
  | _ + 1, .cons exponent remaining, index, replacement =>
      Fin.cases (.cons replacement remaining)
        (fun tail => .cons exponent (withExponentAt remaining tail replacement)) index

/-- Replacement stores the supplied exponent at that same original variable. -/
theorem exponentAt_withExponentAt : {arity : Nat} → (monomial : Monomial arity) →
    (index : Fin arity) → (replacement : Nat) →
    (monomial.withExponentAt index replacement).exponentAt index = replacement
  | 0, .nil, index, _ => Fin.elim0 index
  | _ + 1, .cons _ remaining, index, replacement =>
      Fin.cases (Eq.refl _) (fun tail => exponentAt_withExponentAt remaining tail replacement) index

/-- Replacing a coordinate by its original exponent retains the complete original vector. -/
theorem withExponentAt_self : {arity : Nat} → (monomial : Monomial arity) → (index : Fin arity) →
    monomial.withExponentAt index (monomial.exponentAt index) = monomial
  | 0, .nil, index => Fin.elim0 index
  | _ + 1, .cons exponent remaining, index =>
      Fin.cases (Eq.refl _)
        (fun tail => congrArg (Monomial.cons exponent) (withExponentAt_self remaining tail)) index

/-- A later replacement at the same bounded coordinate retains only its supplied final exponent. -/
theorem withExponentAt_twice : {arity : Nat} → (monomial : Monomial arity) → (index : Fin arity) →
    (first last : Nat) → (monomial.withExponentAt index first).withExponentAt index last =
      monomial.withExponentAt index last
  | 0, .nil, index, _, _ => Fin.elim0 index
  | _ + 1, .cons exponent remaining, index, first, last =>
      Fin.cases (Eq.refl _)
        (fun tail => congrArg (Monomial.cons exponent) (withExponentAt_twice remaining tail first last)) index

/-- The original constant vector has zero at every bounded coordinate. -/
theorem exponentAt_zero : (arity : Nat) → (index : Fin arity) → (zero arity).exponentAt index = 0
  | 0, index => Fin.elim0 index
  | arity + 1, index => Fin.cases (Eq.refl _) (fun tail => exponentAt_zero arity tail) index

/-- The original variable monomial has exponent one at its same bounded coordinate. -/
theorem exponentAt_atom : (arity : Nat) → (index : Fin arity) → (atom arity index).exponentAt index = 1
  | 0, index => Fin.elim0 index
  | arity + 1, index => Fin.cases (Eq.refl _) (fun tail => exponentAt_atom arity tail) index

/-- The selected exponent of an actual monomial product is the sum of its two original selected exponents. -/
theorem exponentAt_add : {arity : Nat} → (first second : Monomial arity) → (index : Fin arity) →
    (add first second).exponentAt index = first.exponentAt index + second.exponentAt index
  | 0, .nil, .nil, index => Fin.elim0 index
  | _ + 1, .cons _ first, .cons _ second, index =>
      Fin.cases (Eq.refl _) (fun tail => exponentAt_add first second tail) index

/-- Coordinate replacement distributes through an actual monomial product with the supplied exponent sum. -/
theorem withExponentAt_add : {arity : Nat} → (first second : Monomial arity) → (index : Fin arity) →
    (left right : Nat) → (add first second).withExponentAt index (left + right) =
      add (first.withExponentAt index left) (second.withExponentAt index right)
  | 0, .nil, .nil, index, _, _ => Fin.elim0 index
  | _ + 1, .cons a first, .cons b second, index, left, right =>
      Fin.cases (Eq.refl _)
        (fun tail => congrArg (Monomial.cons (a + b)) (withExponentAt_add first second tail left right)) index

/-- Multiplication by a selected-variable power changes only that same original exponent. -/
theorem add_selected : {arity : Nat} → (original : Monomial arity) → (index : Fin arity) →
    (exponent : Nat) → add (original.withExponentAt index 0) ((zero arity).withExponentAt index exponent) =
      original.withExponentAt index exponent
  | 0, .nil, index, _ => Fin.elim0 index
  | arity + 1, .cons head remaining, index, exponent => by
      refine Fin.cases ?_ ?_ index
      · change Monomial.cons (0 + exponent) (add remaining (zero arity)) = _
        rewrite [Nat.zero_add, add_zero]
        rfl
      · intro tail
        exact congrArg (Monomial.cons head) (add_selected remaining tail exponent)

/-- A monomial contains no powers outside the same original bounded variable. -/
@[expose] def SelectedAt {arity : Nat} (index : Fin arity) (monomial : Monomial arity) : Prop :=
  monomial.withExponentAt index 0 = zero arity

/-- A selected-only monomial is the original constant vector with its one actual exponent replaced. -/
theorem selectedAt_shape {arity : Nat} (index : Fin arity) (monomial : Monomial arity)
    (selected : SelectedAt index monomial) : monomial = (zero arity).withExponentAt index (monomial.exponentAt index) :=
  ((withExponentAt_twice monomial index 0 (monomial.exponentAt index)).trans
    (withExponentAt_self monomial index)).symm.trans
      (congrArg (fun vector => vector.withExponentAt index (monomial.exponentAt index)) selected)

/-- The original constant monomial contains no variable power outside any selected coordinate. -/
theorem selectedAt_zero {arity : Nat} (index : Fin arity) : SelectedAt index (zero arity) := by
  unfold SelectedAt
  have same := withExponentAt_self (zero arity) index
  rewrite [exponentAt_zero] at same
  exact same

/-- The original selected variable monomial has no other variable support. -/
theorem selectedAt_atom : (arity : Nat) → (index : Fin arity) → SelectedAt index (atom arity index)
  | 0, index => Fin.elim0 index
  | arity + 1, index =>
      Fin.cases (Eq.refl _) (fun tail => congrArg (Monomial.cons 0) (selectedAt_atom arity tail)) index

/-- Multiplication of two selected-only monomials preserves their common original variable support. -/
theorem selectedAt_add {arity : Nat} (index : Fin arity) (first second : Monomial arity)
    (left : SelectedAt index first) (right : SelectedAt index second) : SelectedAt index (add first second) := by
  unfold SelectedAt
  rewrite [withExponentAt_add first second index 0 0, left, right, add_zero]
  rfl

/-- A selected-only multiplier replaces precisely the selected exponent of an unchanged other-variable factor. -/
theorem add_selectedAt {arity : Nat} (original : Monomial arity) (index : Fin arity)
    (selected : Monomial arity) (only : SelectedAt index selected) :
    add (original.withExponentAt index 0) selected = original.withExponentAt index (selected.exponentAt index) := by
  exact (congrArg (add (original.withExponentAt index 0)) (selectedAt_shape index selected only)).trans
    (add_selected original index (selected.exponentAt index))

/-- Reduce one original bounded exponent, retaining its coefficient factor and the other original exponents. -/
@[expose] def reduceAt {R : Type} [Pow R Nat] (degree : Nat) (parameter : R) :
    {arity : Nat} → Monomial arity → Fin arity → R × Monomial arity
  | 0, .nil, index => nomatch index
  | _ + 1, .cons exponent tail, index =>
      Fin.cases (parameter ^ (exponent / degree), .cons (exponent % degree) tail)
        (fun tailIndex =>
          let reduced := reduceAt degree parameter tail tailIndex
          (reduced.1, .cons exponent reduced.2)) index

/-- Reduction stores the original selected exponent's natural remainder. -/
theorem exponentAt_reduceAt {R : Type} [Pow R Nat] {arity : Nat} (monomial : Monomial arity)
    (index : Fin arity) (degree : Nat) (parameter : R) :
    (reduceAt degree parameter monomial index).2.exponentAt index = monomial.exponentAt index % degree := by
  induction monomial with
  | nil => exact Fin.elim0 index
  | cons exponent tail ih =>
      refine Fin.cases (Eq.refl _) (fun next => ih next) index

/-- A positive-degree reduction bounds its selected exponent by the retained degree. -/
theorem exponentAt_reduceAt_lt {R : Type} [Pow R Nat] {arity : Nat} (monomial : Monomial arity)
    (index : Fin arity) (degree : Nat) (parameter : R) (positive : 0 < degree) :
    (reduceAt degree parameter monomial index).2.exponentAt index < degree := by
  rewrite [exponentAt_reduceAt]
  exact Nat.mod_lt _ positive

/-- Pure-power reduction changes only the selected original exponent. -/
theorem reduceAt_withExponentAt {R : Type} [Pow R Nat] : {arity : Nat} → (monomial : Monomial arity) →
    (index : Fin arity) → (degree : Nat) → (parameter : R) →
    (reduceAt degree parameter monomial index).2 =
      monomial.withExponentAt index (monomial.exponentAt index % degree)
  | 0, .nil, index, _, _ => Fin.elim0 index
  | _ + 1, .cons exponent remaining, index, degree, parameter =>
      Fin.cases (Eq.refl _)
        (fun tail => congrArg (Monomial.cons exponent) (reduceAt_withExponentAt remaining tail degree parameter)) index

/-- A retained scalar power equation reduces any exponent by its natural quotient and remainder. -/
theorem power_reduction {R : Type} [CommRing R] (value parameter : R) (degree exponent : Nat)
    (relation : value ^ degree = parameter) :
    parameter ^ (exponent / degree) * value ^ (exponent % degree) = value ^ exponent := by
  rewrite [← relation, ← pow_mul, ← pow_add]
  exact congrArg (fun power => value ^ power)
    ((Nat.add_comm _ _).trans (Purelib.Data.Nat.Division.mod_add_div exponent degree))

/-- Reduced monomial data preserve scalar evaluation under the selected original variable's power equation. -/
theorem eval_reduceAt {R : Type} [CommRing R] {arity : Nat} (monomial : Monomial arity)
    (index : Fin arity) (degree : Nat) (parameter : R) (environment : Fin arity → R)
    (relation : environment index ^ degree = parameter) :
    (reduceAt degree parameter monomial index).1 * (reduceAt degree parameter monomial index).2.eval environment =
      monomial.eval environment := by
  induction monomial with
  | nil => exact Fin.elim0 index
  | cons exponent tail ih =>
      revert relation
      refine Fin.cases ?_ ?_ index
      · intro relation
        change parameter ^ (exponent / degree) *
          (environment 0 ^ (exponent % degree) * tail.eval (fun next => environment next.succ)) = _
        rewrite [← mul_assoc, power_reduction (environment 0) parameter degree exponent relation]
        rfl
      · intro tailIndex relation
        let reduced := reduceAt degree parameter tail tailIndex
        change reduced.1 * (environment 0 ^ exponent * reduced.2.eval (fun next => environment next.succ)) = _
        have tail_eq := ih tailIndex (fun next => environment next.succ) relation
        calc
          reduced.1 * (environment 0 ^ exponent * reduced.2.eval (fun next => environment next.succ)) =
              environment 0 ^ exponent * (reduced.1 * reduced.2.eval (fun next => environment next.succ)) := by ring0
          _ = environment 0 ^ exponent * tail.eval (fun next => environment next.succ) :=
            congrArg (fun value => environment 0 ^ exponent * value) tail_eq

end Monomial

namespace Term

/-- Move the selected variable's whole-degree powers into the actual retained coefficient. -/
@[expose] def reduceAt {R : Type} [Pow R Nat] [Mul R] {arity : Nat} (term : Term R arity)
    (index : Fin arity) (degree : Nat) (parameter : R) : Term R arity :=
  let reduced := term.monomial.reduceAt degree parameter index
  ⟨reduced.2, term.coefficient * reduced.1⟩

/-- Term reduction preserves its scalar reading under the selected original variable's power equation. -/
theorem eval_reduceAt {R : Type} [CommRing R] {arity : Nat} (term : Term R arity)
    (index : Fin arity) (degree : Nat) (parameter : R) (environment : Fin arity → R)
    (relation : environment index ^ degree = parameter) :
    (term.reduceAt index degree parameter).eval environment = term.eval environment := by
  change (term.coefficient * (term.monomial.reduceAt degree parameter index).1) *
    (term.monomial.reduceAt degree parameter index).2.eval environment = _
  rewrite [mul_assoc, Monomial.eval_reduceAt term.monomial index degree parameter environment relation]
  rfl

end Term

namespace Terms

/-- Every retained monomial has a selected bounded exponent below the given natural degree. -/
@[expose] def ExponentBelow {R : Type} {arity : Nat} (index : Fin arity) (degree : Nat) :
    List (Term R arity) → Prop
  | [] => True
  | first :: remaining => first.monomial.exponentAt index < degree ∧ ExponentBelow index degree remaining

/-- Reading a finite exponent predicate gives the original selected-exponent bound. -/
theorem exponentBelow_of_monomialsSatisfy {R : Type} {arity : Nat} (index : Fin arity) (bound : Nat) :
    (terms : List (Term R arity)) → MonomialsSatisfy (fun monomial => monomial.exponentAt index < bound) terms →
    ExponentBelow index bound terms
  | [], _ => True.intro
  | _ :: remaining, holds => ⟨holds.1, exponentBelow_of_monomialsSatisfy index bound remaining holds.2⟩

/-- The original selected-exponent bound supplies its finite monomial predicate. -/
theorem monomialsSatisfy_of_exponentBelow {R : Type} {arity : Nat} (index : Fin arity) (bound : Nat) :
    (terms : List (Term R arity)) → ExponentBelow index bound terms →
    MonomialsSatisfy (fun monomial => monomial.exponentAt index < bound) terms
  | [], _ => True.intro
  | _ :: remaining, holds => ⟨holds.1, monomialsSatisfy_of_exponentBelow index bound remaining holds.2⟩

/-- A finite ceiling strictly above each original selected exponent. -/
@[expose] def exponentBound {R : Type} {arity : Nat} (index : Fin arity) : List (Term R arity) → Nat
  | [] => 1
  | first :: remaining => max (first.monomial.exponentAt index + 1) (exponentBound index remaining)

/-- A larger scalar ceiling preserves every original term's selected-exponent bound. -/
theorem exponentBelow_mono {R : Type} {arity : Nat} (index : Fin arity) {firstBound lastBound : Nat}
    (order : firstBound ≤ lastBound) : (terms : List (Term R arity)) →
    ExponentBelow index firstBound terms → ExponentBelow index lastBound terms
  | [], _ => True.intro
  | _ :: remaining, below => ⟨Nat.lt_of_lt_of_le below.1 order, exponentBelow_mono index order remaining below.2⟩

/-- The computed finite ceiling bounds all original selected exponents. -/
theorem exponentBound_below {R : Type} {arity : Nat} (index : Fin arity) :
    (terms : List (Term R arity)) → ExponentBelow index (exponentBound index terms) terms
  | [] => True.intro
  | _ :: remaining =>
      ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Data.Nat.Order.le_max_left _ _),
        exponentBelow_mono index (Data.Nat.Order.le_max_right _ _) remaining (exponentBound_below index remaining)⟩

/-- Canonical insertion preserves a common selected-exponent bound for the actual retained monomials. -/
theorem insert_exponentBelow {R : Type} [Zero R] [Add R] [DecidableEq R] {arity : Nat}
    (index : Fin arity) (degree : Nat) (term : Term R arity) (terms : List (Term R arity))
    (termBelow : term.monomial.exponentAt index < degree) (below : ExponentBelow index degree terms) :
    ExponentBelow index degree (insert term terms) :=
  exponentBelow_of_monomialsSatisfy index degree _
    (insert_monomialsSatisfy (fun monomial => monomial.exponentAt index < degree) term terms termBelow
      (monomialsSatisfy_of_exponentBelow index degree terms below))

/-- Canonical accumulation preserves a selected-exponent bound for both actual input lists. -/
theorem accumulate_exponentBelow {R : Type} [Zero R] [Add R] [DecidableEq R] {arity : Nat}
    (index : Fin arity) (degree : Nat) (input result : List (Term R arity))
    (inputBelow : ExponentBelow index degree input) (resultBelow : ExponentBelow index degree result) :
    ExponentBelow index degree (accumulate input result) :=
  exponentBelow_of_monomialsSatisfy index degree _
    (accumulate_monomialsSatisfy (fun monomial => monomial.exponentAt index < degree) input result
      (monomialsSatisfy_of_exponentBelow index degree input inputBelow)
      (monomialsSatisfy_of_exponentBelow index degree result resultBelow))

/-- Reduce the actual retained terms at one original variable, without recomputing their other coefficients. -/
@[expose] def reducedAt {R : Type} [Pow R Nat] [Mul R] {arity : Nat} (terms : List (Term R arity))
    (index : Fin arity) (degree : Nat) (parameter : R) : List (Term R arity) :=
  terms.map (fun term => term.reduceAt index degree parameter)

/-- Every selected exponent in the reduced list is below the supplied positive degree. -/
theorem reducedAt_exponentBelow {R : Type} [Pow R Nat] [Mul R] {arity : Nat}
    (terms : List (Term R arity)) (index : Fin arity) (degree : Nat) (parameter : R) (positive : 0 < degree) :
    ExponentBelow index degree (reducedAt terms index degree parameter) := by
  induction terms with
  | nil => exact True.intro
  | cons first remaining ih =>
      exact ⟨Monomial.exponentAt_reduceAt_lt first.monomial index degree parameter positive, ih⟩

/-- Reduction of a retained term list preserves its scalar sum under the supplied power equation. -/
theorem eval_reducedAt {R : Type} [CommRing R] {arity : Nat} (terms : List (Term R arity))
    (index : Fin arity) (degree : Nat) (parameter : R) (environment : Fin arity → R)
    (relation : environment index ^ degree = parameter) :
    eval environment (reducedAt terms index degree parameter) = eval environment terms := by
  induction terms with
  | nil => rfl
  | cons first remaining ih =>
      change (first.reduceAt index degree parameter).eval environment +
        eval environment (reducedAt remaining index degree parameter) = _
      rewrite [Term.eval_reduceAt first index degree parameter environment relation, ih]
      rfl

/-- An actual source term differs from the target only at the same selected bounded coordinate. -/
@[expose] def ReplacementOrigin {R : Type} {arity : Nat} (index : Fin arity)
    (original : List (Term R arity)) (target : Monomial arity) : Prop :=
  ∃ term, term ∈ original ∧ term.monomial.withExponentAt index (target.exponentAt index) = target

/-- Inclusion of original source occurrences preserves a selected-coordinate replacement witness. -/
theorem replacementOrigin_mono {R : Type} {arity : Nat} (index : Fin arity)
    {first last : List (Term R arity)} (included : ∀ term, term ∈ first → term ∈ last)
    {target : Monomial arity} (origin : ReplacementOrigin index first target) :
    ReplacementOrigin index last target := by
  rcases origin with ⟨term, present, same⟩
  exact ⟨term, included term present, same⟩

/-- Every pure-power reduced term retains an actual original source term and unchanged other exponents. -/
theorem reducedAt_replacementOrigins {R : Type} [Pow R Nat] [Mul R] {arity : Nat}
    (index : Fin arity) (degree : Nat) (parameter : R) : (terms : List (Term R arity)) →
    MonomialsSatisfy (ReplacementOrigin index terms) (reducedAt terms index degree parameter)
  | [] => True.intro
  | first :: remaining => by
      constructor
      · refine ⟨first, mem_cons.mpr (Or.inl rfl), ?_⟩
        change first.monomial.withExponentAt index
          ((first.monomial.reduceAt degree parameter index).2.exponentAt index) = _
        rewrite [Monomial.exponentAt_reduceAt]
        exact (Monomial.reduceAt_withExponentAt first.monomial index degree parameter).symm
      · exact monomialsSatisfy_mono
          (fun _ origin => replacementOrigin_mono index (fun _ present => mem_cons.mpr (Or.inr present)) origin)
          _ (reducedAt_replacementOrigins index degree parameter remaining)

end Terms

namespace Sparse

/-- Reduce cached coefficients at one original power relation and canonically combine the resulting monomials. -/
@[expose] def reduceAt {R : Type} [Zero R] [Add R] [Mul R] [Pow R Nat] [DecidableEq R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) (parameter : R) : Sparse R arity :=
  ofTerms (Terms.reducedAt polynomial.terms index degree parameter)

/-- Canonical reduced coefficients have selected exponents strictly below the supplied positive degree. -/
theorem reduceAt_exponentBelow {R : Type} [Zero R] [Add R] [Mul R] [Pow R Nat] [DecidableEq R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) (parameter : R) (positive : 0 < degree) :
    Terms.ExponentBelow index degree (polynomial.reduceAt index degree parameter).terms :=
  Terms.accumulate_exponentBelow index degree _ []
    (Terms.reducedAt_exponentBelow polynomial.terms index degree parameter positive) True.intro

/-- Canonical reduction preserves scalar evaluation under the supplied original variable's power equation. -/
theorem eval_reduceAt {R : Type} [CommRing R] [DecidableEq R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) (parameter : R)
    (environment : Fin arity → R) (relation : environment index ^ degree = parameter) :
    (polynomial.reduceAt index degree parameter).eval environment = polynomial.eval environment := by
  rewrite [reduceAt, eval_ofTerms]
  exact Terms.eval_reducedAt polynomial.terms index degree parameter environment relation

/-- Every canonical pure-power remainder retains an original source monomial differing only at the selected coordinate.
-/
theorem reduceAt_replacementOrigins {R : Type} [Zero R] [Add R] [Mul R] [Pow R Nat] [DecidableEq R]
    {arity : Nat} (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) (parameter : R) :
    Terms.MonomialsSatisfy (Terms.ReplacementOrigin index polynomial.terms)
      (polynomial.reduceAt index degree parameter).terms :=
  ofTerms_monomialsSatisfy _ _ (Terms.reducedAt_replacementOrigins index degree parameter polynomial.terms)

end Sparse

end Purelib.Polynomial.Multivariate

end
