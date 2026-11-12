module

import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Polynomial.Approximation.Evaluation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Polynomial.Multivariate.Sparse
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Polynomial.Approximation.CoherentEvaluation.Division
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence

/-!
# Dense presentations at an original bounded polynomial variable

Finite dense coefficients embed into the original sparse normalization family
at one actual variable position. Operational Horner transport identifies that
same presentation; a retained division run then reduces it under an original
annihilator equation without constructing a resultant or isolating a root.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Sparse

/-- Embed a descending coefficient loop at the selected original sparse variable.

Every step uses the existing canonical sparse multiplication by that atom
and addition of the next exact coefficient. The accumulator and all other
original variable positions remain in the same finite environment.
-/
@[expose] def hornerAt {arity : Nat} (index : Fin arity) :
    Sparse Coefficient arity → List Coefficient → Sparse Coefficient arity
  | initial, [] => initial
  | initial, coefficient :: remaining =>
      hornerAt index ((initial.mul (atom index)).add (constant coefficient)) remaining

/-- Embed a dense polynomial at one actual original sparse variable position. -/
@[expose] def ofDenseAt {arity : Nat} (index : Fin arity) (polynomial : CoefficientPolynomial) :
    Sparse Coefficient arity := hornerAt index zero polynomial.coeffs

/-- The original sparse Horner scan has the same scalar accumulator recurrence at every finite environment. -/
theorem eval_hornerAt {arity : Nat} (index : Fin arity) (environment : Fin arity → Coefficient) :
    (initial : Sparse Coefficient arity) → (coefficients : List Coefficient) →
    (hornerAt index initial coefficients).eval environment =
      coefficients.foldl (fun accumulator coefficient => accumulator * environment index + coefficient)
        (initial.eval environment)
  | _, [] => rfl
  | initial, coefficient :: remaining => by
      change (hornerAt index ((initial.mul (atom index)).add (constant coefficient)) remaining).eval environment = _
      rewrite [eval_hornerAt, eval_add, eval_mul, eval_atom, eval_constant]
      rfl

/-- Sparse dense embedding preserves the original dense polynomial reading at the same selected finite variable. -/
theorem eval_ofDenseAt {arity : Nat} (index : Fin arity) (polynomial : CoefficientPolynomial)
    (environment : Fin arity → Coefficient) :
    (ofDenseAt index polynomial).eval environment = polynomial.eval (environment index) := by
  change (hornerAt index zero polynomial.coeffs).eval environment = _
  rewrite [eval_hornerAt, eval_zero]
  rfl

/-- Sparse coefficient recursion compares to coherent Horner recursion at the same selected original input.

The supplied accumulator comparison is transported through each original
coefficient operation. Every other variable remains opaque and unchanged;
no algebraic equation for those channels is required.
-/
@[expose] def denote_hornerAt {arity : Nat} (index : Fin arity)
    (bindings : Fin arity → CoherentNamed) :
    (initial : Sparse Coefficient arity) → (start : CoherentNamed) →
    NamedEquivalent (initial.denote bindings).name start.name →
    (coefficients : List Coefficient) →
    NamedEquivalent ((hornerAt index initial coefficients).denote bindings).name
      (Horner.horner (bindings index) start coefficients).name
  | _, _, compared, [] => compared
  | initial, start, compared, coefficient :: remaining => by
      let product := initial.mul (atom index)
      let next := product.add (constant coefficient)
      let actualProduct := CoherentNamed.mul start (bindings index)
      let actualNext := CoherentNamed.add actualProduct (Coherence.exact coefficient)
      let productCompared := (denote_mul bindings initial (atom index)).trans
        (Product.Congruence.coherentMul_respects (initial.denote bindings) start
          ((atom index).denote bindings) (bindings index) compared (denote_atom bindings index))
      let nextCompared := (denote_add bindings product (constant coefficient)).trans
        (Sum.Congruence.coherentAdd_respects (product.denote bindings) actualProduct
          ((constant coefficient).denote bindings) (Coherence.exact coefficient)
          productCompared (denote_constant bindings coefficient))
      exact denote_hornerAt index bindings next actualNext nextCompared remaining

/-- The sparse dense embedding compares to the original coherent polynomial evaluator at that same variable. -/
@[expose] def denote_ofDenseAt {arity : Nat} (index : Fin arity) (polynomial : CoefficientPolynomial)
    (bindings : Fin arity → CoherentNamed) :
    NamedEquivalent ((ofDenseAt index polynomial).denote bindings).name
      (Horner.polynomialEval polynomial (bindings index)).name :=
  denote_hornerAt index bindings zero (Coherence.exact 0) (NamedEquivalent.refl _) polynomial.coeffs

/-- Every scalar term has no support outside a selected original variable. -/
theorem constant_selectedAt {arity : Nat} (index : Fin arity) (coefficient : Coefficient) :
    Terms.MonomialsSatisfy (Monomial.SelectedAt index) (constant coefficient : Sparse Coefficient arity).terms :=
  ofTerms_monomialsSatisfy _ _ ⟨Monomial.selectedAt_zero index, True.intro⟩

/-- The original selected atom's canonical terms have no support outside that same variable. -/
theorem atom_selectedAt {arity : Nat} (index : Fin arity) :
    Terms.MonomialsSatisfy (Monomial.SelectedAt index) (atom index : Sparse Coefficient arity).terms :=
  ofTerms_monomialsSatisfy _ _ ⟨Monomial.selectedAt_atom arity index, True.intro⟩

/-- Multiplication preserves actual support restricted to a common selected original variable. -/
theorem mul_selectedAt {arity : Nat} (index : Fin arity) (first second : Sparse Coefficient arity)
    (left : Terms.MonomialsSatisfy (Monomial.SelectedAt index) first.terms)
    (right : Terms.MonomialsSatisfy (Monomial.SelectedAt index) second.terms) :
    Terms.MonomialsSatisfy (Monomial.SelectedAt index) (first.mul second).terms := by
  apply mul_monomialsSatisfy
  exact Terms.monomialsSatisfy_mono (fun a left =>
    Terms.monomialsSatisfy_mono (fun b right => Monomial.selectedAt_add index a b left right) _ right) _ left

/-- The actual sparse Horner loop preserves support restricted to its selected original variable. -/
theorem hornerAt_selectedAt {arity : Nat} (index : Fin arity) :
    (initial : Sparse Coefficient arity) → Terms.MonomialsSatisfy (Monomial.SelectedAt index) initial.terms →
    (coefficients : List Coefficient) →
    Terms.MonomialsSatisfy (Monomial.SelectedAt index) (hornerAt index initial coefficients).terms
  | _, holds, [] => holds
  | initial, holds, coefficient :: remaining =>
      hornerAt_selectedAt index ((initial.mul (atom index)).add (constant coefficient))
        (add_monomialsSatisfy _ _ _
          (mul_selectedAt index initial (atom index) holds (atom_selectedAt index))
          (constant_selectedAt index coefficient)) remaining

/-- Every actual dense embedding monomial has powers only at the same selected original variable. -/
theorem ofDenseAt_selectedAt {arity : Nat} (index : Fin arity) (polynomial : CoefficientPolynomial) :
    Terms.MonomialsSatisfy (Monomial.SelectedAt index) (ofDenseAt index polynomial).terms :=
  hornerAt_selectedAt index zero True.intro polynomial.coeffs

/-- One actual sparse Horner multiplication increases the common selected-exponent ceiling by one. -/
theorem mul_atom_exponentBelow {arity : Nat} (index : Fin arity) (bound : Nat)
    (initial : Sparse Coefficient arity) (below : Terms.ExponentBelow index bound initial.terms) :
    Terms.ExponentBelow index (bound + 1) (initial.mul (atom index)).terms := by
  apply Terms.exponentBelow_of_monomialsSatisfy
  apply mul_monomialsSatisfy
  have atomExponents : Terms.MonomialsSatisfy (fun monomial => monomial.exponentAt index = 1)
      (atom index : Sparse Coefficient arity).terms :=
    ofTerms_monomialsSatisfy _ _ ⟨Monomial.exponentAt_atom arity index, True.intro⟩
  exact Terms.monomialsSatisfy_mono (fun first firstBelow =>
    Terms.monomialsSatisfy_mono (fun second secondExponent => by
      rewrite [Monomial.exponentAt_add, secondExponent]
      exact Nat.add_lt_add_right firstBelow 1) _ atomExponents) _
        (Terms.monomialsSatisfy_of_exponentBelow index bound initial.terms below)

/-- A scalar Horner addend is below every successor selected-exponent ceiling. -/
theorem constant_exponentBelow {arity : Nat} (index : Fin arity) (bound : Nat) (coefficient : Coefficient) :
    Terms.ExponentBelow index (bound + 1) (constant coefficient : Sparse Coefficient arity).terms := by
  apply Terms.exponentBelow_of_monomialsSatisfy
  apply ofTerms_monomialsSatisfy
  constructor
  · change (Monomial.zero arity).exponentAt index < bound + 1
    rewrite [Monomial.exponentAt_zero]
    exact Nat.zero_lt_succ bound
  · exact True.intro

/-- Sparse Horner embedding increases an original selected-exponent ceiling by its actual coefficient count. -/
theorem hornerAt_exponentBelow {arity : Nat} (index : Fin arity) :
    (initial : Sparse Coefficient arity) → (bound : Nat) → Terms.ExponentBelow index bound initial.terms →
    (coefficients : List Coefficient) →
    Terms.ExponentBelow index (bound + coefficients.length) (hornerAt index initial coefficients).terms
  | _, _, below, [] => below
  | initial, bound, below, coefficient :: remaining => by
      let stage := (initial.mul (atom index)).add (constant coefficient)
      have next : Terms.ExponentBelow index (bound + 1) stage.terms :=
        Terms.accumulate_exponentBelow index (bound + 1) _ _
          (mul_atom_exponentBelow index bound initial below) (constant_exponentBelow index bound coefficient)
      have later := hornerAt_exponentBelow index stage (bound + 1) next remaining
      have count : (bound + 1) + remaining.length = bound + (remaining.length + 1) :=
        (Nat.add_assoc bound 1 remaining.length).trans (congrArg (Nat.add bound) (Nat.add_comm 1 remaining.length))
      rewrite [count] at later
      exact later

/-- Every dense embedding exponent is strictly below the original displayed coefficient-list length. -/
theorem ofDenseAt_exponentBelow {arity : Nat} (index : Fin arity) (polynomial : CoefficientPolynomial) :
    Terms.ExponentBelow index polynomial.coeffs.length (ofDenseAt index polynomial).terms := by
  have bound := hornerAt_exponentBelow index zero 0 True.intro polynomial.coeffs
  rewrite [Nat.zero_add] at bound
  exact bound

/-- An actual retained dense remainder embeds with selected exponents below its original nonzero divisor's degree.

The original division normalization converts its cached coefficient count to
its literal list length. The same completed run's strict remainder bound
then supplies the sparse selected-coordinate bound, including an empty
remainder for a nonzero constant divisor.
-/
theorem ofDenseAt_remainder_exponentBelow {arity : Nat} (index : Fin arity)
    (polynomial annihilator : CoefficientPolynomial)
    (division : DensePolynomial.DivResult polynomial annihilator) (computed : division = polynomial.divMod annihilator)
    (nonzero : annihilator.isZero = false) :
    Terms.ExponentBelow index annihilator.natDegree (ofDenseAt index division.remainder).terms := by
  have normalized := DensePolynomial.divMod_remainder_normalize polynomial annihilator
  have smaller := DensePolynomial.divMod_remainder_degreeCount_lt polynomial annihilator nonzero
  rewrite [← computed] at normalized smaller
  have count : division.remainder.degreeCount = division.remainder.coeffs.length :=
    congrArg (fun value : CoefficientPolynomial => value.coeffs.length) normalized
  have divisorCount := DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  rewrite [count, ← divisorCount] at smaller
  apply Terms.exponentBelow_of_monomialsSatisfy
  exact Terms.monomialsSatisfy_mono (fun _ below => Nat.lt_of_lt_of_le below (Nat.le_of_lt_succ smaller)) _
    (Terms.monomialsSatisfy_of_exponentBelow index division.remainder.coeffs.length _
      (ofDenseAt_exponentBelow index division.remainder))

end Sparse

namespace Gaussian.Normalized

/-- Normalize an original channel through its actual retained Horner execution and coefficient interpretation.

The cached Horner steps retain the original selected numerical input and final
accumulator. The computed sparse form and output interpretation are consumed
literally; only pointwise finite scalar readback connects their two retained
source programs. No Horner or sparse numerical prefix is reconstructed.
-/
@[expose] def ofDenseAt {arity : Nat} (bindings : Fin arity → CoherentNamed) (index : Fin arity)
    (polynomial : CoefficientPolynomial)
    (numerical : Horner.Accumulations (bindings index) (Coherence.exact 0) polynomial.coeffs)
    {original : CoherentNamed}
    (equivalent : NamedEquivalent original.name
      (numerical.output (bindings index) (Coherence.exact 0) polynomial.coeffs).name)
    {sources : Terms.Caches bindings}
    (cached : Terms.Denotation.Prepared bindings sources (Sparse.ofDenseAt index polynomial)) :
    Normalized bindings original := by
  let inputs := Terms.Denotation.inputs bindings
  let dense := Evaluation.evaluate polynomial (inputs.source index)
  let sparse := Terms.source inputs.source cached.form.terms
  let compared := CoherentEvaluation.evaluate_cached_agrees polynomial (bindings index)
    (inputs.source index) (inputs.equivalent index) numerical
  let samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq dense.toApproximation sparse.toApproximation
    (fun stage => by
      change dense.sample stage = sparse.sample stage
      dsimp only [dense, sparse]
      rewrite [Evaluation.evaluate_sample, Terms.source_sample, cached.form_eq]
      exact (Sparse.eval_ofDenseAt index polynomial
        (fun inputIndex => (inputs.source inputIndex).sample stage)).symm)
  exact ofPrepared cached inputs (equivalent.trans (compared.trans samples.toNamed))

/-- Dense normalization retains its literal prepared output interpretation. -/
theorem ofDenseAt_denotation {arity : Nat} (bindings : Fin arity → CoherentNamed) (index : Fin arity)
    (polynomial : CoefficientPolynomial)
    (numerical : Horner.Accumulations (bindings index) (Coherence.exact 0) polynomial.coeffs)
    {original : CoherentNamed}
    (equivalent : NamedEquivalent original.name
      (numerical.output (bindings index) (Coherence.exact 0) polynomial.coeffs).name)
    {sources : Terms.Caches bindings}
    (cached : Terms.Denotation.Prepared bindings sources (Sparse.ofDenseAt index polynomial)) :
    (ofDenseAt bindings index polynomial numerical equivalent cached).denotation = cached.denotation := rfl

/-- Dense normalization reads the stored original sparse coefficient construction. -/
theorem ofDenseAt_form {arity : Nat} (bindings : Fin arity → CoherentNamed) (index : Fin arity)
    (polynomial : CoefficientPolynomial)
    (numerical : Horner.Accumulations (bindings index) (Coherence.exact 0) polynomial.coeffs)
    {original : CoherentNamed}
    (equivalent : NamedEquivalent original.name
      (numerical.output (bindings index) (Coherence.exact 0) polynomial.coeffs).name)
    {sources : Terms.Caches bindings}
    (cached : Terms.Denotation.Prepared bindings sources (Sparse.ofDenseAt index polynomial)) :
    (ofDenseAt bindings index polynomial numerical equivalent cached).form = Sparse.ofDenseAt index polynomial :=
  cached.form_eq

/-- Reduce a retained dense presentation at one original variable by its retained annihilator division.

The exact form identity authenticates the original normalization's dense
presentation. Reduction consumes the original division record and same
generator sampler. The output keeps the unchanged original channel and
reuses existing monomial caches through the original denotation lookup.
-/
@[expose] def reduceDenseAt {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {original : CoherentNamed} (normalized : Normalized bindings original)
    (index : Fin arity) (polynomial annihilator : CoefficientPolynomial)
    (formEq : normalized.form.terms = (Sparse.ofDenseAt index polynomial).terms)
    (division : DensePolynomial.DivResult polynomial annihilator)
    (computed : division = polynomial.divMod annihilator)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name
      (Coherence.exact 0).name) : Normalized bindings original := by
  have originalToDense : NamedEquivalent original.name
      (Horner.polynomialEval polynomial (bindings index)).name := by
    have comparison := normalized.toForm
    change NamedEquivalent original.name (Terms.denote bindings normalized.form.terms).name at comparison
    rewrite [formEq] at comparison
    exact comparison.trans (Sparse.denote_ofDenseAt index polynomial bindings)
  let remainderComparison := CoherentEvaluation.remainder_agrees division computed
    (bindings index) source sourceEq zero
  let form := Sparse.ofDenseAt index division.remainder
  let comparison := originalToDense.trans
    (remainderComparison.trans (Sparse.denote_ofDenseAt index division.remainder bindings).symm)
  exact ofForm bindings form comparison normalized.denotation.findMonomial

/-- Dense reduction stores the sparse embedding of the exact original retained remainder. -/
theorem reduceDenseAt_form {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {original : CoherentNamed} (normalized : Normalized bindings original)
    (index : Fin arity) (polynomial annihilator : CoefficientPolynomial)
    (formEq : normalized.form.terms = (Sparse.ofDenseAt index polynomial).terms)
    (division : DensePolynomial.DivResult polynomial annihilator)
    (computed : division = polynomial.divMod annihilator)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (bindings index).name source.toApproximation.toNamed)
    (zero : NamedEquivalent (Horner.polynomialEval annihilator (bindings index)).name
      (Coherence.exact 0).name) :
    (normalized.reduceDenseAt index polynomial annihilator formEq division computed source sourceEq zero).form =
      Sparse.ofDenseAt index division.remainder := rfl

end Gaussian.Normalized

end Purelib.Polynomial.Multivariate
