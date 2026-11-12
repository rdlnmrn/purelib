module

public import Purelib.Polynomial.Multivariate.PowerReduction
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded coordinates in one original polynomial variable

Every successful coordinate retains the original variable index and a bounded
natural exponent. Inspection classifies every original term, retaining an
unrelated monomial or an excessive exponent as a precise formal obligation.
These obligations assert no inequality between the variables' numerical values.
-/

public section

namespace Purelib.Polynomial.Multivariate

namespace Monomial

/-- Retain a single original variable's exponent and zero at every other original position. -/
@[expose] def single : (arity : Nat) → Fin arity → Nat → Monomial arity
  | 0, index, _ => nomatch index
  | arity + 1, index, exponent =>
      Fin.cases (.cons exponent (zero arity)) (fun tail => .cons 0 (single arity tail exponent)) index

/-- The selected coordinate of a single-variable monomial is its original supplied exponent. -/
theorem exponentAt_single (arity : Nat) (index : Fin arity) (exponent : Nat) :
    (single arity index exponent).exponentAt index = exponent := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ arity ih =>
      refine Fin.cases (Eq.refl _) (fun tail => ih tail) index

/-- A single-variable monomial evaluates to the supplied power at its original index. -/
theorem eval_single {R : Type} [CommRing R] (arity : Nat) (index : Fin arity) (exponent : Nat)
    (environment : Fin arity → R) : (single arity index exponent).eval environment = environment index ^ exponent := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ arity ih =>
      refine Fin.cases ?_ ?_ index
      · change environment 0 ^ exponent * (zero arity).eval (fun next => environment next.succ) = _
        rewrite [eval_zero, mul_one]
        rfl
      · intro tail
        change environment 0 ^ 0 * (single arity tail exponent).eval (fun next => environment next.succ) = _
        rewrite [pow_zero, one_mul, ih]
        rfl

set_option genInjectivity false in
/-- A bounded power of one original variable or a proved formal condition preventing that representation. -/
inductive PowerView {arity : Nat} (monomial : Monomial arity) (index : Fin arity) (degree : Nat) where
  /-- Retain the actual bounded exponent and equality to the original monomial. -/
  | power (exponent : Fin degree) (monomial_eq : monomial = single arity index exponent.val)
  /-- The original monomial is not a power supported solely at the displayed original index. -/
  | other (monomial_ne : monomial ≠ single arity index (monomial.exponentAt index))
  /-- The original monomial has the right support but exceeds the supplied degree bound. -/
  | over (monomial_eq : monomial = single arity index (monomial.exponentAt index))
      (exponent_ge : degree ≤ monomial.exponentAt index)

constructive_injectivity PowerView

/-- Inspect the actual support and selected exponent without changing the original monomial. -/
@[expose] def inspectPower {arity : Nat} (monomial : Monomial arity) (index : Fin arity) (degree : Nat) :
    PowerView monomial index degree :=
  if only : monomial = single arity index (monomial.exponentAt index) then
    if below : monomial.exponentAt index < degree then .power ⟨_, below⟩ only
    else .over only (Nat.le_of_not_gt below)
  else .other only

/-- A represented power has no remaining formal support or exponent obligation. -/
@[expose] def PowerView.Complete {arity : Nat} {monomial : Monomial arity} {index : Fin arity} {degree : Nat} :
    PowerView monomial index degree → Prop
  | .power _ _ => True
  | .other _ => False
  | .over _ _ => False

/-- Decide completeness from the actual retained inspection constructor. -/
instance PowerView.completeDecidable {arity : Nat} {monomial : Monomial arity} {index : Fin arity} {degree : Nat}
    (view : PowerView monomial index degree) : Decidable view.Complete :=
  match view with
  | .power _ _ => isTrue True.intro
  | .other _ => isFalse (fun impossible => impossible)
  | .over _ _ => isFalse (fun impossible => impossible)

end Monomial

namespace Terms

set_option genInjectivity false in
/-- The retained power inspection of every original term in its original list order. -/
inductive PowerView {R : Type} {arity : Nat} (index : Fin arity) (degree : Nat) : List (Term R arity) → Type where
  /-- An empty original list has no pending coordinate obligations. -/
  | nil : PowerView index degree []
  /-- Retain the original head's inspection and the entire original tail's inspections. -/
  | cons {first : Term R arity} {remaining : List (Term R arity)}
      (head : Monomial.PowerView first.monomial index degree) (tail : PowerView index degree remaining) :
      PowerView index degree (first :: remaining)

constructive_injectivity PowerView

/-- Inspect every original term once, retaining all successful coordinates and every unresolved condition. -/
@[expose] def inspectPowers {R : Type} {arity : Nat} (index : Fin arity) (degree : Nat) :
    (terms : List (Term R arity)) → PowerView index degree terms
  | [] => .nil
  | first :: remaining => .cons (first.monomial.inspectPower index degree) (inspectPowers index degree remaining)

/-- Every original term inspection has a bounded supported power. -/
@[expose] def PowerView.Complete {R : Type} {arity : Nat} {index : Fin arity} {degree : Nat} :
    {terms : List (Term R arity)} → PowerView index degree terms → Prop
  | [], .nil => True
  | _ :: _, .cons head tail => head.Complete ∧ tail.Complete

/-- Decide completeness from the actual retained finite inspection tree. -/
instance PowerView.completeDecidable {R : Type} {arity : Nat} {index : Fin arity} {degree : Nat} :
    {terms : List (Term R arity)} → (view : PowerView index degree terms) → Decidable view.Complete
  | [], .nil => isTrue True.intro
  | _ :: _, .cons head tail =>
      letI := completeDecidable tail
      inferInstanceAs (Decidable (head.Complete ∧ tail.Complete))

/-- Read bounded exponents with the actual original coefficients from a complete retained inspection. -/
@[expose] def PowerView.entries {R : Type} {arity : Nat} {index : Fin arity} {degree : Nat} :
    {terms : List (Term R arity)} → (view : PowerView index degree terms) → view.Complete → List (Fin degree × R)
  | [], .nil, _ => []
  | first :: _, .cons (.power exponent _) tail, complete =>
      (exponent, first.coefficient) :: entries tail complete.2
  | _ :: _, .cons (.other _) _, complete => False.elim complete.1
  | _ :: _, .cons (.over _ _) _, complete => False.elim complete.1

/-- Complete retained coordinates reconstruct the entire original term list with its unchanged coefficients. -/
theorem PowerView.entries_terms {R : Type} {arity : Nat} {index : Fin arity} {degree : Nat}
    {terms : List (Term R arity)} (view : PowerView index degree terms) (complete : view.Complete) :
    terms = (view.entries complete).map (fun entry => ⟨Monomial.single arity index entry.1.val, entry.2⟩) := by
  induction terms with
  | nil => cases view; rfl
  | cons first remaining ih =>
      cases view with
      | cons head tail =>
          cases head with
          | power exponent same =>
              change first :: remaining =
                ⟨Monomial.single arity index exponent.val, first.coefficient⟩ ::
                  (tail.entries complete.2).map (fun entry => ⟨Monomial.single arity index entry.1.val, entry.2⟩)
              have first_eq : first = ⟨Monomial.single arity index exponent.val, first.coefficient⟩ := by
                cases first with
                | mk monomial coefficient =>
                    change monomial = Monomial.single arity index exponent.val at same
                    cases same
                    rfl
              exact congrArg₂ List.cons first_eq (ih tail complete.2)
          | other different => exact False.elim complete.1
          | over same beyond => exact False.elim complete.1

end Terms

namespace Sparse

set_option genInjectivity false in
/-- Cached bounded powers retaining their original sparse polynomial, selected variable index and degree. -/
structure PowerCoordinates {R : Type} [Zero R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) where
  /-- Bounded exponents paired with the actual original coefficients in their original order. -/
  entries : List (Fin degree × R)
  /-- The cached entries reconstruct the entire original term list. -/
  terms_eq : polynomial.terms = entries.map (fun entry => ⟨Monomial.single arity index entry.1.val, entry.2⟩)

constructive_injectivity PowerCoordinates

set_option genInjectivity false in
/-- Cached coordinate success or the complete original inspection with all unresolved formal conditions. -/
inductive PowerOutcome {R : Type} [Zero R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) where
  /-- Retain the certified coordinate cache at this original polynomial and index. -/
  | coordinates (result : PowerCoordinates polynomial index degree)
  /-- Retain every inspected term and prove that their requested power representation is incomplete. -/
  | unresolved (view : Terms.PowerView index degree polynomial.terms) (incomplete : ¬ view.Complete)

constructive_injectivity PowerOutcome

set_option genInjectivity false in
/-- A complete finite power inspection retaining the actual original polynomial and request as executable data. -/
structure PowerCheck {R : Type} [Zero R] {arity : Nat}
    (original : Sparse R arity) (requestedIndex : Fin arity) (requestedDegree : Nat) where
  /-- The actual original polynomial inspected by the procedure. -/
  polynomial : Sparse R arity
  /-- The retained polynomial is the entire original input owner. -/
  polynomial_eq : polynomial = original
  /-- The actual original selected variable position. -/
  index : Fin arity
  /-- The retained position is the requested original index. -/
  index_eq : index = requestedIndex
  /-- The actual natural degree bound inspected by the procedure. -/
  degree : Nat
  /-- The retained bound is the requested degree. -/
  degree_eq : degree = requestedDegree
  /-- Cached coordinates or all original unresolved term conditions at the retained input and request. -/
  outcome : PowerOutcome polynomial index degree

constructive_injectivity PowerCheck

/-- Read the same retained outcome at its original polynomial, bounded index and finite-degree request. -/
@[expose] def PowerCheck.originalOutcome {R : Type} [Zero R] {arity : Nat}
    {polynomial : Sparse R arity} {index : Fin arity} {degree : Nat}
    (check : PowerCheck polynomial index degree) : PowerOutcome polynomial index degree := by
  cases check with
  | mk retained retained_eq selected selected_eq bound bound_eq outcome =>
      cases retained_eq
      cases selected_eq
      cases bound_eq
      exact outcome

/-- Check bounded single-variable support, returning cached coordinates or every retained formal obligation. -/
@[expose] def inspectPowers {R : Type} [Zero R] {arity : Nat}
    (polynomial : Sparse R arity) (index : Fin arity) (degree : Nat) :
    PowerCheck polynomial index degree :=
  let view := Terms.inspectPowers index degree polynomial.terms
  let outcome := if complete : view.Complete then
      PowerOutcome.coordinates ⟨view.entries complete, view.entries_terms complete⟩
    else .unresolved view complete
  ⟨polynomial, rfl, index, rfl, degree, rfl, outcome⟩

end Sparse

end Purelib.Polynomial.Multivariate

end
