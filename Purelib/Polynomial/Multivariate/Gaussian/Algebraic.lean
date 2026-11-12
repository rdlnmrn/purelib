module

public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Approximation.Gaussian.Provenance.Algebraic

/-!
# Algebraic interpretation of supported retained coefficient forms

Interpretation consumes the actual original coefficient, power, product and
sum caches. Only variables with nonzero exponents require admissions; absent
variables of a reduced form remain the original opaque numerical channels.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient

/-- An original bounded variable has a nonzero exponent in at least one retained term. -/
@[expose] def Terms.Required {arity : Nat} (terms : List (Term Coefficient arity)) (index : Fin arity) : Prop :=
  match terms with
  | [] => False
  | first :: remaining => first.monomial.exponentAt index ≠ 0 ∨ Required remaining index

/-- Decide required support by the same finite exponent table. -/
instance Terms.requiredDecidable {arity : Nat} :
    (terms : List (Term Coefficient arity)) → (index : Fin arity) → Decidable (Required terms index)
  | [], _ => isFalse (fun impossible => impossible)
  | _ :: remaining, index =>
      letI := requiredDecidable remaining index
      inferInstanceAs (Decidable (_ ∨ Required remaining index))

/-- Availability at every nonzero original exponent establishes structural monomial support. -/
theorem Monomial.supported_of_required : {arity : Nat} → (monomial : Monomial arity) →
    (available : Fin arity → Prop) →
    (∀ index, monomial.exponentAt index ≠ 0 → available index) → monomial.Supported available
  | 0, .nil, _, _ => True.intro
  | _ + 1, .cons exponent remaining, available, ready =>
      ⟨if zero : exponent = 0 then Or.inl zero else Or.inr (ready 0 zero),
        supported_of_required remaining (fun index => available index.succ)
          (fun index required => ready index.succ required)⟩

/-- Availability at exactly the required original variables supplies the retained term support. -/
theorem Terms.supported_of_required {arity : Nat} (available : Fin arity → Prop) :
    (terms : List (Term Coefficient arity)) →
    (∀ index, Required terms index → available index) → Supported available terms
  | [], _ => True.intro
  | first :: remaining, ready =>
      ⟨first.monomial.supported_of_required available (fun index required => ready index (Or.inl required)),
        supported_of_required available remaining (fun index required => ready index (Or.inr required))⟩

/-- Interpret the same retained products, requiring original sidecars only at nonzero exponents. -/
@[noinline, nospecialize] def Monomial.Products.algebraic :
    {arity : Nat} → {monomial : Monomial arity} → {bindings : Fin arity → CoherentNamed} →
    {channel : CoherentNamed} → Products monomial bindings channel →
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) →
    monomial.Supported (fun index => (evidence index).isSome = true) → Algebraic.Sidecar channel
  | _, _, _, _, .nil _ _ same, _, _ =>
      same.symm ▸ Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)
  | _, _, _, _, .cons exponent _ bindings power power_eq _ tail _ product_eq, evidence, supported =>
      let first : Algebraic.Sidecar (Power.namedPower (bindings 0) exponent) :=
        if zero : exponent = 0 then
          zero.symm ▸ Algebraic.Sidecar.ofRational (RationalSidecar.exact 1)
        else ((evidence 0).get (by
          cases supported.1 with
          | inl same => exact False.elim (zero same)
          | inr available => exact available)).pow exponent
      let atPower : Algebraic.Sidecar power := power_eq.symm ▸ first
      let remaining := tail.algebraic (fun index => evidence index.succ) supported.2
      product_eq.symm ▸ atPower.mul remaining

/-- Interpret an actual original monomial cache from sidecars at precisely its required variables. -/
@[noinline, nospecialize] def Monomial.Denotation.algebraic {arity : Nat} {monomial : Monomial arity}
    {bindings : Fin arity → CoherentNamed} (retained : Denotation monomial bindings)
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supported : monomial.Supported (fun index => (evidence index).isSome = true)) :
    Algebraic.Sidecar retained.channel := retained.products.algebraic evidence supported

/-- Interpret a retained term using its same stored coefficient and monomial channels. -/
@[noinline, nospecialize] def Term.Denotation.algebraic {arity : Nat}
    {term : Term Coefficient arity} {bindings : Fin arity → CoherentNamed}
    (retained : Denotation bindings term)
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supported : term.monomial.Supported (fun index => (evidence index).isSome = true)) :
    Algebraic.Sidecar retained.channel :=
  let coefficient : Algebraic.Sidecar retained.coefficient :=
    retained.coefficient_eq.symm ▸ Algebraic.Sidecar.ofRational (RationalSidecar.exact term.coefficient)
  retained.product_eq.symm ▸ coefficient.mul (retained.monomial.algebraic evidence supported)

/-- Interpret the same original finite sum caches, requiring sidecars only on the reduced term support. -/
@[noinline, nospecialize] def Terms.Sums.algebraic {arity : Nat} {bindings : Fin arity → CoherentNamed}
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index))) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums bindings terms channel →
    Supported (fun index => (evidence index).isSome = true) terms → Algebraic.Sidecar channel
  | _, _, .nil _ same, _ => same.symm ▸ Algebraic.Sidecar.ofRational (RationalSidecar.exact 0)
  | _, _, .cons _ _ head _ tail _ same, supported =>
      same.symm ▸ (head.algebraic evidence supported.1).add (tail.algebraic evidence supported.2)

/-- Interpret the exact retained term-list cache from original sidecars at its surviving support. -/
@[noinline, nospecialize] def Terms.Denotation.algebraic {arity : Nat}
    {bindings : Fin arity → CoherentNamed} {terms : List (Term Coefficient arity)}
    (retained : Denotation bindings terms)
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supported : Supported (fun index => (evidence index).isSome = true) terms) :
    Algebraic.Sidecar retained.channel := retained.sums.algebraic evidence supported

/-- Transport the actual supported algebraic interpretation to its unchanged original source channel. -/
@[noinline, nospecialize] def Gaussian.Normalized.algebraic {arity : Nat}
    {bindings : Fin arity → CoherentNamed} {channel : CoherentNamed} (normalized : Gaussian.Normalized bindings channel)
    (evidence : (index : Fin arity) → Option (Algebraic.Sidecar (bindings index)))
    (supported : Terms.Supported (fun index => (evidence index).isSome = true) normalized.form.terms) :
    Algebraic.Sidecar channel :=
  let atCache := normalized.denotation.algebraic evidence supported
  let atNormal : Algebraic.Sidecar normalized.channel := normalized.denotation_eq.symm ▸ atCache
  atNormal.transport normalized.equivalent

end Purelib.Polynomial.Multivariate

end
