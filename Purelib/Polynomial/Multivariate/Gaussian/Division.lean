module

import Purelib.Data.List.Membership

import Purelib.Polynomial.Multivariate.Sparse
public import Purelib.Polynomial.Multivariate.Gaussian.Dense
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Polynomial.Approximation.CoherentEvaluation.Division
public import Purelib.Polynomial.Multivariate.Gaussian.PowerReduction
public import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Data.List.Range.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Checked coefficient division at one original sparse variable

The original annihilator divides each needed basis power once. Quotient and
remainder terms retain the original other exponents, and exact canonical
coefficient reconstruction is retained independently of operational reduction. The original
completed basis divisions supply unconditional operational completeness. A failed
coefficient check proves only that check's mismatch, with no root-value or
global-impossibility conclusion.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.List.Membership (mem_cons)

open Purelib
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Polynomial.Approximation
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Data.List (DependentProduct)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Monomial

/-- Split one original monomial into its unchanged other-coordinate factor and selected natural power. -/
def denote_splitAt : {arity : Nat} → (monomial : Monomial arity) → (index : Fin arity) →
    (bindings : Fin arity → CoherentNamed) →
    NamedEquivalent (monomial.denote bindings).name
      (CoherentNamed.mul ((monomial.withExponentAt index 0).denote bindings)
        (Power.namedPower (bindings index) (monomial.exponentAt index))).name
  | 0, .nil, index, _ => Fin.elim0 index
  | _ + 1, .cons exponent remaining, index, bindings => by
      refine Fin.cases ?_ ?_ index
      · let head := Power.namedPower (bindings 0) exponent
        let tail := remaining.denote (fun index => bindings index.succ)
        exact (Product.Laws.coherentMul_comm head tail).trans
          (Product.Congruence.coherentMul_respects tail (CoherentNamed.mul (Coherence.exact 1) tail)
            head head (Arithmetic.Mul.coherentMul_one_left tail).symm (NamedEquivalent.refl _))
      · intro tailIndex
        let head := Power.namedPower (bindings 0) exponent
        let tail := remaining.denote (fun index => bindings index.succ)
        let changed := (remaining.withExponentAt tailIndex 0).denote (fun index => bindings index.succ)
        let power := Power.namedPower (bindings tailIndex.succ) (remaining.exponentAt tailIndex)
        exact (Product.Congruence.coherentMul_respects head head tail (CoherentNamed.mul changed power)
          (NamedEquivalent.refl _) (denote_splitAt remaining tailIndex (fun index => bindings index.succ))).trans
            (Product.Laws.coherentMul_assoc head changed power).symm

end Monomial

namespace Sparse

/-- The original dense basis polynomial for one natural power. -/
@[expose] def basisPower (exponent : Nat) : CoefficientPolynomial :=
  DensePolynomial.shift exponent (DensePolynomial.constant 1)

/-- A materialized original division result and actual-run equality for each bounded basis exponent. -/
abbrev PowerDivisions (annihilator : CoefficientPolynomial) (bound : Nat) :=
  DependentProduct (List.range bound) (fun index =>
    {division : DensePolynomial.DivResult (basisPower index.val) annihilator //
      division = (basisPower index.val).divMod annihilator})

namespace PowerDivisions

/-- Run each bounded basis division once and retain its complete original output. -/
@[expose] def prepare (annihilator : CoefficientPolynomial) (bound : Nat) : PowerDivisions annihilator bound :=
  DependentProduct.ofFn (List.range bound) fun index => ⟨(basisPower index.val).divMod annihilator, rfl⟩

/-- Read the literal retained basis division at its unchanged natural exponent. -/
@[expose] def get {annihilator : CoefficientPolynomial} {bound : Nat}
    (divisions : PowerDivisions annihilator bound) (index : Fin bound) :
    {division : DensePolynomial.DivResult (basisPower index.val) annihilator //
      division = (basisPower index.val).divMod annihilator} :=
  DependentProduct.get (List.range bound) divisions
    ⟨index.val, by rewrite [Data.List.Range.Basic.length_range]; exact index.isLt⟩

end PowerDivisions

/-- Form the quotient and remainder coefficients by replacing only the selected power in each original term.

All division results are read from the same materialized table. The original
coefficient and other-variable monomial factor multiply both retained outputs;
existing sparse convolution and accumulation combine the resulting terms.
-/
@[expose] def divideTerms {arity : Nat} (index : Fin arity) (annihilator : CoefficientPolynomial)
    {bound : Nat} (divisions : PowerDivisions annihilator bound) :
    (terms : List (Term Coefficient arity)) → Terms.ExponentBelow index bound terms →
    Sparse Coefficient arity × Sparse Coefficient arity
  | [], _ => (zero, zero)
  | first :: remaining, below =>
      let division := (divisions.get ⟨first.monomial.exponentAt index, below.1⟩).val
      let other := ofTerms [⟨first.monomial.withExponentAt index 0, first.coefficient⟩]
      let later := divideTerms index annihilator divisions remaining below.2
      ((other.mul (ofDenseAt index division.quotient)).add later.1,
        (other.mul (ofDenseAt index division.remainder)).add later.2)

/-- Every term produced from one actual source term and a dense selected-variable factor retains that source monomial.

Canonical insertion may combine or cancel coefficients. Its retained exponent
vectors still differ from this same source term only at the selected coordinate.
-/
theorem termDense_replacementOrigins {arity : Nat} (term : Term Coefficient arity) (index : Fin arity)
    (polynomial : CoefficientPolynomial) (original : List (Term Coefficient arity)) (present : term ∈ original) :
    Terms.MonomialsSatisfy (Terms.ReplacementOrigin index original)
      ((ofTerms [⟨term.monomial.withExponentAt index 0, term.coefficient⟩]).mul
        (ofDenseAt index polynomial)).terms := by
  have other : Terms.MonomialsSatisfy (fun monomial => monomial = term.monomial.withExponentAt index 0)
      (ofTerms [⟨term.monomial.withExponentAt index 0, term.coefficient⟩]).terms :=
    ofTerms_monomialsSatisfy _ _ ⟨rfl, True.intro⟩
  have dense := ofDenseAt_selectedAt index polynomial
  apply mul_monomialsSatisfy
  exact Terms.monomialsSatisfy_mono (fun first same =>
    Terms.monomialsSatisfy_mono (fun second only => by
      have exponent : (Monomial.add first second).exponentAt index = second.exponentAt index := by
        rewrite [Monomial.exponentAt_add, same, Monomial.exponentAt_withExponentAt, Nat.zero_add]
        rfl
      have shape := Monomial.add_selectedAt term.monomial index second only
      rewrite [← same] at shape
      refine ⟨term, present, ?_⟩
      rewrite [exponent]
      exact shape.symm) _ dense) _ other

/-- A dense selected-variable factor bounds every actual source-term product's selected exponent. -/
theorem termDense_exponentBelow {arity : Nat} (term : Term Coefficient arity) (index : Fin arity)
    (polynomial : CoefficientPolynomial) (bound : Nat)
    (below : Terms.ExponentBelow index bound (ofDenseAt index polynomial).terms) :
    Terms.ExponentBelow index bound
      ((ofTerms [⟨term.monomial.withExponentAt index 0, term.coefficient⟩]).mul
        (ofDenseAt index polynomial)).terms := by
  have other : Terms.MonomialsSatisfy (fun monomial => monomial.exponentAt index = 0)
      (ofTerms [⟨term.monomial.withExponentAt index 0, term.coefficient⟩]).terms :=
    ofTerms_monomialsSatisfy _ _ ⟨Monomial.exponentAt_withExponentAt term.monomial index 0, True.intro⟩
  apply Terms.exponentBelow_of_monomialsSatisfy
  apply mul_monomialsSatisfy
  exact Terms.monomialsSatisfy_mono (fun first zero =>
    Terms.monomialsSatisfy_mono (fun second secondBelow => by
      rewrite [Monomial.exponentAt_add, zero, Nat.zero_add]
      exact secondBelow) _ (Terms.monomialsSatisfy_of_exponentBelow index bound _ below)) _ other

/-- Every emitted and surviving division monomial retains a source occurrence with unchanged other exponents.

The proof follows the actual completed basis table, dense Horner embedding,
finite convolution and canonical accumulation. It covers terms after
coefficient combination and cancellation rather than only raw emissions.
-/
theorem divideTerms_replacementOrigins {arity : Nat} (index : Fin arity) (annihilator : CoefficientPolynomial)
    {bound : Nat} (divisions : PowerDivisions annihilator bound) :
    (terms : List (Term Coefficient arity)) → (below : Terms.ExponentBelow index bound terms) →
    Terms.MonomialsSatisfy (Terms.ReplacementOrigin index terms)
        (divideTerms index annihilator divisions terms below).1.terms ∧
      Terms.MonomialsSatisfy (Terms.ReplacementOrigin index terms)
        (divideTerms index annihilator divisions terms below).2.terms
  | [], _ => ⟨True.intro, True.intro⟩
  | first :: remaining, below => by
      let division := (divisions.get ⟨first.monomial.exponentAt index, below.1⟩).val
      have later := divideTerms_replacementOrigins index annihilator divisions remaining below.2
      have keep : (target : Monomial arity) → Terms.ReplacementOrigin index remaining target →
          Terms.ReplacementOrigin index (first :: remaining) target := fun target origin =>
        Terms.replacementOrigin_mono index (fun _ present => mem_cons.mpr (Or.inr present)) origin
      exact ⟨add_monomialsSatisfy _ _ _
        (termDense_replacementOrigins first index division.quotient _ (mem_cons.mpr (Or.inl rfl)))
        (Terms.monomialsSatisfy_mono keep _ later.1),
        add_monomialsSatisfy _ _ _
          (termDense_replacementOrigins first index division.remainder _ (mem_cons.mpr (Or.inl rfl)))
          (Terms.monomialsSatisfy_mono keep _ later.2)⟩

/-- The actual division remainder has selected exponents below its original nonzero annihilator's degree. -/
theorem divideTerms_remainder_exponentBelow {arity : Nat} (index : Fin arity) (annihilator : CoefficientPolynomial)
    {bound : Nat} (divisions : PowerDivisions annihilator bound) (nonzero : annihilator.isZero = false) :
    (terms : List (Term Coefficient arity)) → (below : Terms.ExponentBelow index bound terms) →
    Terms.ExponentBelow index annihilator.natDegree (divideTerms index annihilator divisions terms below).2.terms
  | [], _ => True.intro
  | first :: remaining, below => by
      let division := divisions.get ⟨first.monomial.exponentAt index, below.1⟩
      have dense := ofDenseAt_remainder_exponentBelow index (basisPower (first.monomial.exponentAt index))
        annihilator division.val division.property nonzero
      exact Terms.accumulate_exponentBelow index annihilator.natDegree _ _
        (termDense_exponentBelow first index division.val.remainder annihilator.natDegree dense)
        (divideTerms_remainder_exponentBelow index annihilator divisions nonzero remaining below.2)

/-- Reduce one original term by the retained division of its selected basis power.

The coefficient and every other coordinate remain unchanged. The original
operational annihilator equation removes the quotient term; no source sample
is assumed to be an exact root and no canonical sparse extensionality is used.
-/
def denote_termRemainder {arity : Nat} (bindings : Fin arity → CoherentNamed)
    (term : Term Coefficient arity) (index : Fin arity) (annihilator : CoefficientPolynomial)
    (division : DensePolynomial.DivResult (basisPower (term.monomial.exponentAt index)) annihilator)
    (computed : division = (basisPower (term.monomial.exponentAt index)).divMod annihilator)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name (Coherence.exact 0).name) :
    NamedEquivalent (term.denote bindings).name
      (((ofTerms [⟨term.monomial.withExponentAt index 0, term.coefficient⟩]).mul
        (ofDenseAt index division.remainder)).denote bindings).name := by
  let other : Term Coefficient arity := ⟨term.monomial.withExponentAt index 0, term.coefficient⟩
  let factor := ofTerms [other]
  let remainder := ofDenseAt index division.remainder
  let coefficient := Coherence.exact term.coefficient
  let changed := other.monomial.denote bindings
  let power := Power.namedPower (bindings index) (term.monomial.exponentAt index)
  let split := (Product.Congruence.coherentMul_respects coefficient coefficient
    (term.monomial.denote bindings) (CoherentNamed.mul changed power) (NamedEquivalent.refl _)
    (term.monomial.denote_splitAt index bindings)).trans
      (Product.Laws.coherentMul_assoc coefficient changed power).symm
  let basis := CoherentEvaluation.basisPower_agrees (term.monomial.exponentAt index)
    (bindings index) source sourceEq
  let reducedPower := basis.symm.trans
    (CoherentEvaluation.remainder_agrees division computed (bindings index) source sourceEq zero)
  let toRemainder := reducedPower.trans (Sparse.denote_ofDenseAt index division.remainder bindings).symm
  let factorAgreement := (denote_ofTerms bindings [other]).trans
    (Arithmetic.Add.coherentAdd_zero_right (other.denote bindings))
  let replace := Product.Congruence.coherentMul_respects (other.denote bindings) (factor.denote bindings)
    power (remainder.denote bindings) factorAgreement.symm toRemainder
  exact split.trans (replace.trans (denote_mul bindings factor remainder).symm)

/-- Every finite original term sum reduces to its actual computed sparse remainder.

Each step reads its original completed basis division and unchanged other
coordinates. Finite-sum transport and original sparse normalization establish
operational completeness for arbitrary retained annihilators, independently
of the optional exact canonical coefficient-reconstruction check.
-/
def denote_divideTerms_remainder {arity : Nat} (bindings : Fin arity → CoherentNamed)
    (index : Fin arity) (annihilator : CoefficientPolynomial) {bound : Nat}
    (divisions : PowerDivisions annihilator bound) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name (Coherence.exact 0).name) :
    (terms : List (Term Coefficient arity)) → (below : Terms.ExponentBelow index bound terms) →
    NamedEquivalent (Terms.denote bindings terms).name
      ((divideTerms index annihilator divisions terms below).2.denote bindings).name
  | [], _ => NamedEquivalent.refl _
  | first :: remaining, below =>
      let division := divisions.get ⟨first.monomial.exponentAt index, below.1⟩
      let other := ofTerms [⟨first.monomial.withExponentAt index 0, first.coefficient⟩]
      let head := other.mul (ofDenseAt index division.val.remainder)
      let later := divideTerms index annihilator divisions remaining below.2
      (Sum.Congruence.coherentAdd_respects (first.denote bindings) (head.denote bindings)
        (Terms.denote bindings remaining) (later.2.denote bindings)
        (denote_termRemainder bindings first index annihilator division.val division.property source sourceEq zero)
        (denote_divideTerms_remainder bindings index annihilator divisions source sourceEq zero
          remaining below.2)).trans
          (denote_add bindings head later.2).symm

set_option genInjectivity false in
/-- One complete finite coefficient-division attempt on an original sparse polynomial and original variable.

The original basis divisions, exact quotient/remainder outputs and coefficient
reconstruction decision are retained together. The decision is typed evidence
of exact reconstruction or of this specific coefficient mismatch.
-/
structure DivisionAt {arity : Nat} (original : Sparse Coefficient arity) (index : Fin arity)
    (annihilator : CoefficientPolynomial) where
  /-- The actual original selected-exponent ceiling. -/
  bound : Nat
  /-- The ceiling was computed from these same original terms. -/
  bound_eq : bound = Terms.exponentBound index original.terms
  /-- Every original selected exponent is within this same retained ceiling. -/
  below : Terms.ExponentBelow index bound original.terms
  /-- The original completed basis division records. -/
  divisions : PowerDivisions annihilator bound
  /-- These records came from the actual original bounded basis division procedure. -/
  divisions_eq : divisions = PowerDivisions.prepare annihilator bound
  /-- The actual computed multivariate quotient coefficient form. -/
  quotient : Sparse Coefficient arity
  /-- The actual computed multivariate remainder coefficient form. -/
  remainder : Sparse Coefficient arity
  /-- The two outputs were computed from these same retained terms and divisions. -/
  computed : (quotient, remainder) = divideTerms index annihilator divisions original.terms below
  /-- Exact canonical coefficient reconstruction or a proof of this attempted reconstruction's mismatch. -/
  reconstruction : Decidable (original.terms = (remainder.add ((ofDenseAt index annihilator).mul quotient)).terms)

constructive_injectivity DivisionAt

namespace DivisionAt

/-- Retain one original coefficient-division attempt and its exact reconstruction check. -/
@[expose] def prepare {arity : Nat} (original : Sparse Coefficient arity) (index : Fin arity)
    (annihilator : CoefficientPolynomial) : DivisionAt original index annihilator :=
  let bound := Terms.exponentBound index original.terms
  let below := Terms.exponentBound_below index original.terms
  let divisions := PowerDivisions.prepare annihilator bound
  let result := divideTerms index annihilator divisions original.terms below
  ⟨bound, rfl, below, divisions, rfl, result.1, result.2, rfl, inferInstance⟩

/-- Every actual retained quotient monomial differs from an original source term only at the selected coordinate. -/
theorem quotient_replacementOrigins {arity : Nat} {original : Sparse Coefficient arity} {index : Fin arity}
    {annihilator : CoefficientPolynomial} (attempt : DivisionAt original index annihilator) :
    Terms.MonomialsSatisfy (Terms.ReplacementOrigin index original.terms) attempt.quotient.terms := by
  have origins := (divideTerms_replacementOrigins index annihilator attempt.divisions original.terms attempt.below).1
  have same := congrArg Prod.fst attempt.computed
  rewrite [← same] at origins
  exact origins

/-- Every actual retained remainder monomial differs from an original source term only at the selected coordinate. -/
theorem remainder_replacementOrigins {arity : Nat} {original : Sparse Coefficient arity} {index : Fin arity}
    {annihilator : CoefficientPolynomial} (attempt : DivisionAt original index annihilator) :
    Terms.MonomialsSatisfy (Terms.ReplacementOrigin index original.terms) attempt.remainder.terms := by
  have origins := (divideTerms_replacementOrigins index annihilator attempt.divisions original.terms attempt.below).2
  have same := congrArg Prod.snd attempt.computed
  rewrite [← same] at origins
  exact origins

/-- The retained multivariate remainder has degree below the original nonzero annihilator at the selected coordinate. -/
theorem remainder_exponentBelow {arity : Nat} {original : Sparse Coefficient arity} {index : Fin arity}
    {annihilator : CoefficientPolynomial} (attempt : DivisionAt original index annihilator)
    (nonzero : annihilator.isZero = false) :
    Terms.ExponentBelow index annihilator.natDegree attempt.remainder.terms := by
  have below := divideTerms_remainder_exponentBelow index annihilator attempt.divisions nonzero
    original.terms attempt.below
  have same := congrArg Prod.snd attempt.computed
  rewrite [← same] at below
  exact below

end DivisionAt

end Sparse

namespace Gaussian.Normalized

/-- Consume every retained original basis division and annihilator equation on the unchanged source channel.

Operational completeness follows term by term from the original division
identities. The stored coefficient-reconstruction decision remains available
as separate exact coefficient evidence; neither success nor cache consumption
requires semantic equality to be upgraded to sparse coefficient equality.
-/
@[expose] def reduceBy {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Normalized bindings original) (index : Fin arity) (annihilator : CoefficientPolynomial)
    (attempt : Sparse.DivisionAt normalized.form index annihilator)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name (Coherence.exact 0).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached attempt.remainder.terms) :
    Normalized bindings original := by
  have remainder := Sparse.denote_divideTerms_remainder bindings index annihilator attempt.divisions
    source sourceEq zero normalized.form.terms attempt.below
  have remainder_eq := congrArg Prod.snd attempt.computed
  rewrite [← remainder_eq] at remainder
  exact ofForm bindings attempt.remainder (normalized.toForm.trans remainder) cached (some ⟨complete⟩)

/-- General annihilator reduction consumes the exact complete retained-cache builder on its actual remainder terms. -/
theorem reduceBy_denotation {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Normalized bindings original) (index : Fin arity) (annihilator : CoefficientPolynomial)
    (attempt : Sparse.DivisionAt normalized.form index annihilator) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name (Coherence.exact 0).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached attempt.remainder.terms) :
    (normalized.reduceBy index annihilator attempt source sourceEq zero cached complete).denotation =
      Terms.retainFrom bindings cached attempt.remainder.terms complete := rfl

/-- Arbitrary original annihilator reduction uses the actual retained remainder coefficient form. -/
theorem reduceBy_form {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Normalized bindings original) (index : Fin arity) (annihilator : CoefficientPolynomial)
    (attempt : Sparse.DivisionAt normalized.form index annihilator) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name (Coherence.exact 0).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached attempt.remainder.terms) :
    (normalized.reduceBy index annihilator attempt source sourceEq zero cached complete).form = attempt.remainder := rfl

/-- Apply a pure-power equation using actual retained monomial caches and an optional stored coefficient form.

The supplied form is linked to the original coefficient reduction and is
consumed directly for normalization and denotation construction. Omitting
it uses the same original reduction as the constructor default. The
operational comparison remains the original independent producer.
-/
@[expose] def reduceAtCached {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : Provenance.Power.PowerIdentity (bindings index) degree parameter)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached (normalized.form.reduceAt index degree parameter).terms)
    (retained : {form : Sparse Coefficient arity // form = normalized.form.reduceAt index degree parameter} :=
      ⟨normalized.form.reduceAt index degree parameter, rfl⟩) : Gaussian.Normalized bindings original := by
  let form := retained.val
  have compared := normalized.toForm.trans
    (Sparse.denote_reduceAt normalized.form index degree parameter bindings relation)
  have actualCompared : NamedEquivalent original.name (form.denote bindings).name :=
    Eq.mp (congrArg (fun form : Sparse Coefficient arity =>
      NamedEquivalent original.name (form.denote bindings).name) retained.property.symm) compared
  have actualComplete : Terms.CacheComplete bindings cached form.terms :=
    Eq.mp (congrArg (fun form : Sparse Coefficient arity =>
      Terms.CacheComplete bindings cached form.terms) retained.property.symm) complete
  exact ofForm bindings form actualCompared cached (some ⟨actualComplete⟩)

/-- Pure-power reduction consumes the exact complete retained-cache builder after canonical exponent reduction. -/
theorem reduceAtCached_denotation {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : Provenance.Power.PowerIdentity (bindings index) degree parameter)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached (normalized.form.reduceAt index degree parameter).terms) :
    (normalized.reduceAtCached index degree parameter relation cached complete).denotation =
      Terms.retainFrom bindings cached (normalized.form.reduceAt index degree parameter).terms complete := rfl

/-- The default cached pure-power builder retains the exact original computed coefficient form. -/
theorem reduceAtCached_form {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : Provenance.Power.PowerIdentity (bindings index) degree parameter)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached (normalized.form.reduceAt index degree parameter).terms) :
    (normalized.reduceAtCached index degree parameter relation cached complete).form =
      normalized.form.reduceAt index degree parameter := rfl

/-- The supplied pure-power coefficient cache is the identical form retained by the output normalization. -/
theorem reduceAtCached_retained_form {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : Provenance.Power.PowerIdentity (bindings index) degree parameter)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached (normalized.form.reduceAt index degree parameter).terms)
    (retained : {form : Sparse Coefficient arity // form = normalized.form.reduceAt index degree parameter}) :
    (normalized.reduceAtCached index degree parameter relation cached complete retained).form = retained.val := rfl

/-- The supplied pure-power cache is interpreted by the same complete retained-product builder. -/
theorem reduceAtCached_retained_denotation {arity : Nat} {original : CoherentNamed}
    {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : Provenance.Power.PowerIdentity (bindings index) degree parameter)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached (normalized.form.reduceAt index degree parameter).terms)
    (retained : {form : Sparse Coefficient arity // form = normalized.form.reduceAt index degree parameter}) :
    (normalized.reduceAtCached index degree parameter relation cached complete retained).denotation =
      Terms.retainFrom bindings cached retained.val.terms
        (Eq.mp (congrArg (fun form : Sparse Coefficient arity => Terms.CacheComplete bindings cached form.terms)
          retained.property.symm) complete) := rfl

end Gaussian.Normalized

end Purelib.Polynomial.Multivariate
