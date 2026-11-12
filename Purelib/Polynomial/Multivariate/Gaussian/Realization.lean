module

public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Polynomial.Multivariate.Evaluation
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Sidecar
public import Purelib.Data.Gaussian.Cast.Real
public import Purelib.Data.List.DependentProduct
import Purelib.Data.Rat.Fraction.Field

/-!
# Exact coordinate evaluation of original sparse Gaussian polynomials

The original variable channels carry coordinate evidence at one supplied
realization. Each original coefficient has an explicit scalar preimage under
that same realization's map. Evaluation uses the existing pair arithmetic,
finite numerical powers and original monomial indices; no defining equation
is invented for composite variable channels.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)

variable {K : Type} [ExplicitField K]

/-- Interpret the cached original powers and products, requiring evidence only at nonzero exponents. -/
@[noinline, nospecialize] def Monomial.Products.realize (realization : Realization K) :
    {arity : Nat} → {monomial : Monomial arity} → {environment : Fin arity → CoherentNamed} →
    {channel : CoherentNamed} → Products monomial environment channel →
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index))) →
    monomial.Supported (fun index => (evidence index).isSome = true) →
      Realization.Sidecar realization channel
  | _, _, _, _, .nil _ _ same, _, _ =>
      (Realization.Sidecar.constant realization 1 1 realization.one_eq.symm).reindex same
  | _, _, _, _, .cons exponent _ environment power power_eq _ tail _ product_eq, evidence, supported =>
      let first : Realization.Sidecar realization
          (Power.namedPower (environment 0) exponent) :=
        if zero : exponent = 0 then
          zero.symm ▸ Realization.Sidecar.constant realization 1 1 realization.one_eq.symm
        else (Realization.Sidecar.get (evidence 0) (by
          cases supported.1 with
          | inl same => exact False.elim (zero same)
          | inr available => exact available)).pow exponent
      ((first.reindex power_eq).mul
        (tail.realize realization (fun index => evidence index.succ) supported.2)).reindex product_eq

/-- Monomial interpretation reads the same supported coordinates, ignoring absent zero-exponent variables. -/
theorem Monomial.Products.realize_value (realization : Realization K) :
    {arity : Nat} → {monomial : Monomial arity} → {environment : Fin arity → CoherentNamed} →
    {channel : CoherentNamed} → (products : Products monomial environment channel) →
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index))) →
    (supported : monomial.Supported (fun index => (evidence index).isSome = true)) →
    (products.realize realization evidence supported).value =
      monomial.eval (fun index => Realization.Sidecar.valueOrZero (evidence index))
  | _, _, _, _, .nil _ _ same, _, _ =>
      (Realization.Sidecar.reindex_value _ same).trans
        ((Realization.Sidecar.constant_value realization 1 1 realization.one_eq.symm).trans Pair.scalar_one)
  | _, _, _, _, .cons exponent _ environment power power_eq _ remaining _ product_eq, evidence, supported => by
      have tail := remaining.realize_value realization (fun index => evidence index.succ) supported.2
      by_cases zero : exponent = 0
      · subst exponent
        rewrite [Products.realize, Realization.Sidecar.reindex_value, dif_pos rfl,
          Realization.Sidecar.mul_value, Realization.Sidecar.reindex_value,
          Realization.Sidecar.constant_value, tail]
        change Pair.scalar (1 : K) * _ = Realization.Sidecar.valueOrZero (evidence 0) ^ 0 * _
        rewrite [Pair.scalar_one, pow_zero]
        rfl
      · rewrite [Products.realize, Realization.Sidecar.reindex_value, dif_neg zero,
          Realization.Sidecar.mul_value, Realization.Sidecar.reindex_value,
          Realization.Sidecar.pow_value, Realization.Sidecar.get_value, tail]
        rfl

/-- Interpret the same retained monomial construction at its actual cached source channel. -/
@[noinline, nospecialize] def Monomial.Denotation.realize (realization : Realization K)
    {arity : Nat} {monomial : Monomial arity} {environment : Fin arity → CoherentNamed}
    (retained : Denotation monomial environment)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : monomial.Supported (fun index => (evidence index).isSome = true)) :
    Realization.Sidecar realization retained.channel := retained.products.realize realization evidence supported

/-- Cached monomial interpretation retains evaluation of the same original supported coordinates. -/
theorem Monomial.Denotation.realize_value (realization : Realization K)
    {arity : Nat} {monomial : Monomial arity} {environment : Fin arity → CoherentNamed}
    (retained : Denotation monomial environment)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : monomial.Supported (fun index => (evidence index).isSome = true)) :
    (retained.realize realization evidence supported).value =
      monomial.eval (fun index => Realization.Sidecar.valueOrZero (evidence index)) :=
  retained.products.realize_value realization evidence supported

/-- Scalar preimages certify every coefficient in the original term list under the supplied realization's map. -/
@[expose] def Terms.Coefficients (realization : Realization K) {arity : Nat}
    (terms : List (Term Coefficient arity)) : Type :=
  DependentProduct terms (fun index => {value : K // (terms[index.val]'index.isLt).coefficient =
    realization.coefficient value})

/-- Map the original monomials to their certified scalar-pair coefficients at the same realization. -/
@[expose] def Terms.Coefficients.scalarTerms (realization : Realization K) {arity : Nat} :
    {terms : List (Term Coefficient arity)} → Coefficients realization terms →
      List (Term (Pair K realization.parameter) arity)
  | [], _ => []
  | first :: _, coefficients =>
      ⟨first.monomial, Pair.scalar coefficients.1.1⟩ :: scalarTerms realization coefficients.2

/-- Read the original monomial keys and coefficients for exact real-axis inspection. -/
@[expose] def Terms.coefficientEntries {arity : Nat} (terms : List (Term Coefficient arity)) :=
  terms.map (fun term => (term.monomial, term.coefficient))

/-- Retained complete real-axis inspections supply scalar preimages under the same admitted coefficient map. -/
@[expose] def Terms.coefficientsOfRealView (realization : Realization Rational)
    (coefficient_eq : ∀ value, realization.coefficient value = Cast.CoordinateTaylor.ofCoordinate value)
    {arity : Nat} : {terms : List (Term Coefficient arity)} →
    (view : Cast.RealListView (coefficientEntries terms)) → view.Complete → Coefficients realization terms
  | [], .nil, _ => PUnit.unit
  | first :: _, .cons (.real value same) remaining, complete =>
      (⟨value, same.trans (coefficient_eq value).symm⟩,
        coefficientsOfRealView realization coefficient_eq remaining complete.2)
  | _ :: _, .cons (.complex _) _, complete => False.elim complete.1

/-- Interpret one original term from its scalar preimage and evidence at its actual supported variables. -/
@[noinline, nospecialize] def Term.Denotation.realize (realization : Realization K) {arity : Nat}
    {term : Term Coefficient arity} {environment : Fin arity → CoherentNamed}
    (retained : Denotation environment term)
    (coefficient : {value : K // term.coefficient = realization.coefficient value})
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : term.monomial.Supported (fun index => (evidence index).isSome = true)) :
    Realization.Sidecar realization retained.channel :=
  (((Realization.Sidecar.constant realization term.coefficient coefficient.1 coefficient.2).reindex
    retained.coefficient_eq).mul (retained.monomial.realize realization evidence supported)).reindex retained.product_eq

/-- Term interpretation multiplies its original coefficient by the same supported monomial coordinates. -/
theorem Term.Denotation.realize_value (realization : Realization K) {arity : Nat}
    {term : Term Coefficient arity} {environment : Fin arity → CoherentNamed}
    (retained : Denotation environment term)
    (coefficient : {value : K // term.coefficient = realization.coefficient value})
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : term.monomial.Supported (fun index => (evidence index).isSome = true)) :
    (retained.realize realization coefficient evidence supported).value =
      Pair.scalar coefficient.1 *
        term.monomial.eval (fun index => Realization.Sidecar.valueOrZero (evidence index)) := by
  unfold Term.Denotation.realize
  rewrite [Realization.Sidecar.reindex_value, Realization.Sidecar.mul_value, Realization.Sidecar.reindex_value,
    Realization.Sidecar.constant_value, Monomial.Denotation.realize_value]
  rfl

/-- Evaluate the original term list without requesting evidence for variables absent from its monomials. -/
@[noinline, nospecialize] def Terms.Sums.realize (realization : Realization K) {arity : Nat}
    {environment : Fin arity → CoherentNamed}
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index))) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} → Sums environment terms channel →
    Coefficients realization terms →
    Supported (fun index => (evidence index).isSome = true) terms →
      Realization.Sidecar realization channel
  | _, _, .nil _ same, _, _ =>
      (Realization.Sidecar.constant realization 0 0 realization.zero_eq.symm).reindex same
  | _, _, .cons _ _ head _ tail _ same, coefficients, supported =>
      ((head.realize realization coefficients.1 evidence supported.1).add
        (tail.realize realization evidence coefficients.2 supported.2)).reindex same

/-- Term-list interpretation agrees with evaluation of its same mapped coefficients and supported coordinates. -/
theorem Terms.Sums.realize_value (realization : Realization K) {arity : Nat}
    {environment : Fin arity → CoherentNamed}
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index))) :
    {terms : List (Term Coefficient arity)} → {channel : CoherentNamed} →
    (sums : Sums environment terms channel) → (coefficients : Coefficients realization terms) →
    (supported : Supported (fun index => (evidence index).isSome = true) terms) →
    (sums.realize realization evidence coefficients supported).value =
      Terms.eval (fun index => Realization.Sidecar.valueOrZero (evidence index)) (coefficients.scalarTerms realization)
  | _, _, .nil _ same, _, _ =>
      (Realization.Sidecar.reindex_value _ same).trans
        ((Realization.Sidecar.constant_value realization 0 0 realization.zero_eq.symm).trans Pair.scalar_zero)
  | _, _, .cons _ _ head _ tail _ same, coefficients, supported => by
      rewrite [Sums.realize, Realization.Sidecar.reindex_value, Realization.Sidecar.add_value,
        Term.Denotation.realize_value, tail.realize_value realization evidence coefficients.2 supported.2]
      rfl

/-- Interpret the original finite polynomial at its same cached term and sum channels. -/
@[noinline, nospecialize] def Terms.Denotation.realize (realization : Realization K) {arity : Nat}
    {environment : Fin arity → CoherentNamed} {terms : List (Term Coefficient arity)}
    (retained : Denotation environment terms) (coefficients : Coefficients realization terms)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : Supported (fun index => (evidence index).isSome = true) terms) :
    Realization.Sidecar realization retained.channel :=
  retained.sums.realize realization evidence coefficients supported

/-- Cached finite polynomial interpretation reads the same coefficients and supported original coordinates. -/
theorem Terms.Denotation.realize_value (realization : Realization K) {arity : Nat}
    {environment : Fin arity → CoherentNamed} {terms : List (Term Coefficient arity)}
    (retained : Denotation environment terms) (coefficients : Coefficients realization terms)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : Supported (fun index => (evidence index).isSome = true) terms) :
    (retained.realize realization coefficients evidence supported).value =
      Terms.eval (fun index => Realization.Sidecar.valueOrZero (evidence index))
        (coefficients.scalarTerms realization) :=
  retained.sums.realize_value realization evidence coefficients supported

/-- Interpret the original cached form using evidence at its actual support, preserving its original source channel. -/
@[noinline, nospecialize] def Gaussian.Normalized.realize (realization : Realization K)
    {arity : Nat} {environment : Fin arity → CoherentNamed} {channel : CoherentNamed}
    (normalized : Gaussian.Normalized environment channel)
    (coefficients : Terms.Coefficients realization normalized.form.terms)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : Terms.Supported (fun index => (evidence index).isSome = true) normalized.form.terms) :
    Realization.Sidecar realization channel :=
  let atCache := normalized.denotation.realize realization coefficients evidence supported
  (atCache.reindex normalized.denotation_eq).transport normalized.equivalent

/-- Polynomial realization reads the same coefficient cache and available original input coordinates. -/
theorem Gaussian.Normalized.realize_value (realization : Realization K)
    {arity : Nat} {environment : Fin arity → CoherentNamed} {channel : CoherentNamed}
    (normalized : Gaussian.Normalized environment channel)
    (coefficients : Terms.Coefficients realization normalized.form.terms)
    (evidence : (index : Fin arity) → Option (Realization.Sidecar realization (environment index)))
    (supported : Terms.Supported (fun index => (evidence index).isSome = true) normalized.form.terms) :
    (normalized.realize realization coefficients evidence supported).value =
      Terms.eval (fun index => Realization.Sidecar.valueOrZero (evidence index))
        (coefficients.scalarTerms realization) :=
  (Realization.Sidecar.transport_value _ _).trans
    ((Realization.Sidecar.reindex_value _ _).trans
      (normalized.denotation.realize_value realization coefficients evidence supported))

end Purelib.Polynomial.Multivariate

end
