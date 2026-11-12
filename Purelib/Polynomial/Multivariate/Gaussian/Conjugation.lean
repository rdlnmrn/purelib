module

public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Gaussian.Power
import Purelib.Approximation.Gaussian.Sequence.Equivalence

/-!
# Conjugated retained polynomial coordinates

Coefficients, original finite variable positions and actual interpreted
channels are conjugated together. The original normalization remains an input
owner, and its stored powers and suffix sums feed the operational comparison.
-/

public section
namespace Purelib.Polynomial.Multivariate

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Sequence.Equivalence (approximationEquivalentOfSamplesEq)
open Purelib.Data.Vector (DependentVector)

namespace Monomial

/-- Conjugating each original variable conjugates the same finite monomial reading. -/
theorem eval_conj : {arity : Nat} → (monomial : Monomial arity) →
    (environment : Fin arity → Coefficient) →
      monomial.eval (fun index => Coefficient.conj (environment index)) =
        Coefficient.conj (monomial.eval environment)
  | 0, .nil, _ => rfl
  | _ + 1, .cons exponent tail, environment => by
      change Coefficient.conj (environment 0) ^ exponent *
        tail.eval (fun index => Coefficient.conj (environment index.succ)) =
          Coefficient.conj (environment 0 ^ exponent * tail.eval (fun index => environment index.succ))
      have power : Coefficient.conj (environment 0 ^ exponent) = Coefficient.conj (environment 0) ^ exponent :=
        Purelib.Data.Gaussian.Power.conj_pow (environment 0) exponent
      rewrite [Coefficient.conj_mul, power, eval_conj]
      rfl

end Monomial

namespace Terms

/-- Conjugate every actual coefficient while retaining its original monomial and order. -/
@[expose] def conjugated {arity : Nat} : List (Term Coefficient arity) → List (Term Coefficient arity)
  | [] => []
  | first :: remaining => ⟨first.monomial, Coefficient.conj first.coefficient⟩ :: conjugated remaining

/-- Coefficient conjugation retains every strict original monomial bound. -/
theorem above_conjugated {arity : Nat} (lower : Monomial arity) :
    (terms : List (Term Coefficient arity)) → Above lower terms → Above lower (conjugated terms)
  | [], _ => True.intro
  | _ :: remaining, above => ⟨above.1, above_conjugated lower remaining above.2⟩

/-- Nonzero coefficients and strict finite monomial order survive conjugation. -/
theorem canonical_conjugated {arity : Nat} : (terms : List (Term Coefficient arity)) →
    Canonical terms → Canonical (conjugated terms)
  | [], _ => True.intro
  | _ :: remaining, canonical =>
      ⟨Coefficient.conj_ne_zero canonical.1, above_conjugated _ remaining canonical.2.1,
        canonical_conjugated remaining canonical.2.2⟩

/-- Conjugated coefficients at conjugated variables give the conjugate of the original ordered finite sum. -/
theorem eval_conjugated {arity : Nat} (environment : Fin arity → Coefficient) :
    (terms : List (Term Coefficient arity)) →
      eval (fun index => Coefficient.conj (environment index)) (conjugated terms) =
        Coefficient.conj (eval environment terms)
  | [] => rfl
  | first :: remaining => by
      change Coefficient.conj first.coefficient * first.monomial.eval
        (fun index => Coefficient.conj (environment index)) +
          eval (fun index => Coefficient.conj (environment index)) (conjugated remaining) =
            Coefficient.conj (first.coefficient * first.monomial.eval environment + eval environment remaining)
      rewrite [Coefficient.conj_add, Coefficient.conj_mul, Monomial.eval_conj, eval_conjugated]
      rfl

end Terms

namespace Sparse

/-- Conjugate the actual coefficient list, preserving every original monomial and canonical order. -/
@[expose] def conj {arity : Nat} (input : Sparse Coefficient arity) : Sparse Coefficient arity :=
  ⟨Terms.conjugated input.terms, Terms.canonical_conjugated input.terms input.canonical⟩

/-- The conjugated form stores the coefficient operation's actual output list. -/
theorem conj_terms {arity : Nat} (input : Sparse Coefficient arity) :
    input.conj.terms = Terms.conjugated input.terms := rfl

/-- Coefficient conjugation agrees with the same finite scalar operation at conjugated variables. -/
theorem eval_conj {arity : Nat} (environment : Fin arity → Coefficient) (input : Sparse Coefficient arity) :
    input.conj.eval (fun index => Coefficient.conj (environment index)) =
      Coefficient.conj (input.eval environment) := Terms.eval_conjugated environment input.terms

end Sparse

namespace Gaussian.Normalized

/-- Actual conjugated channels and both retained finite interpretation constructions.

The original side contains the supplied normalization's exact stored
interpretation. The target side has the actual conjugated coefficient form
and its own genuine powers at the stored conjugated variable channels.
-/
abbrev ConjInputs {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) :=
  (channels : DependentVector (fun _ : Fin arity => CoherentNamed)) ×
    PLift (∀ index, channels.get index = CoherentNamed.conj (bindings index)) ×
      Terms.Denotation.Prepared bindings input.sources input.form ×
        Terms.Denotation.Prepared (fun index => channels.get index) [] input.form.conj

/-- Read the actual stored target variable channel at its original finite position. -/
abbrev ConjInputs.channels {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {input : Normalized bindings original} (cached : ConjInputs input) (index : Fin arity) := cached.1.get index

/-- Read the exact construction identity of each retained conjugated channel. -/
theorem ConjInputs.channels_eq {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {input : Normalized bindings original} (cached : ConjInputs input) (index : Fin arity) :
    cached.channels index = CoherentNamed.conj (bindings index) := cached.2.1.down index

/-- Read the actual original interpretation preparation with the original retained source denotation. -/
abbrev ConjInputs.before {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {input : Normalized bindings original} (cached : ConjInputs input) := cached.2.2.1

/-- Read the actual target coefficient form, variable powers and suffix interpretation. -/
abbrev ConjInputs.after {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {input : Normalized bindings original} (cached : ConjInputs input) := cached.2.2.2

/-- Prepare each actual conjugated variable and coefficient output once, consuming the original stored denotation. -/
@[expose] def prepareConj {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) : ConjInputs input := by
  let channels := DependentVector.ofFn (fun index => CoherentNamed.conj (bindings index))
  have channelEq : ∀ index, channels.get index = CoherentNamed.conj (bindings index) := by
    intro index
    exact DependentVector.ofFn_get _ index
  let before := Terms.Denotation.prepare bindings input.sources input.form (some input.denotation)
  let after := Terms.Denotation.prepare (fun index => channels.get index) [] input.form.conj
  exact ⟨channels, ⟨channelEq⟩, before, after⟩

/-- The source preparation consumes the whole literal original interpretation. -/
theorem prepareConj_before_denotation {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) : input.prepareConj.before.denotation = input.denotation := rfl

/-- Conjugate the indexed original channel using the supplied actual original and target interpretation caches.

The source comparison consumes retained products and suffix sums. Target
powers belong to the actual conjugated channels, and its relation carries its
own quantitative bound and paid request indices. No nominal double-conjugate
identity or canonical numerical polynomial interpreter is assumed.
-/
@[expose] def conj {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (cached : ConjInputs input := input.prepareConj) :
    Normalized cached.channels (CoherentNamed.conj original) := by
  let beforeInputs := Terms.Denotation.inputs bindings
  let afterInputs : Terms.Denotation.Inputs cached.channels :=
    DependentVector.ofFn (fun index => by
      let source := (beforeInputs.source index).conj
      have equivalent := CoherentNamed.conj_geometric (beforeInputs.source index) (beforeInputs.equivalent index)
      have same := cached.channels_eq index
      rewrite [← same] at equivalent
      exact ⟨source, equivalent⟩)
  let before := Terms.source beforeInputs.source input.form.terms
  let after := Terms.source afterInputs.source cached.after.form.terms
  have compared := CoherentNamed.conj_geometric before
    (input.source_equivalent cached.before beforeInputs input.source_mem)
  have samples := approximationEquivalentOfSamplesEq before.conj.toApproximation after.toApproximation (by
    intro index
    change before.conj.sample index = after.sample index
    dsimp only [before, after]
    rewrite [GeometricApproximation.conj_sample, Terms.source_sample, Terms.source_sample, cached.after.form_eq]
    have channels : ∀ inputIndex, (afterInputs.source inputIndex).sample index =
        Coefficient.conj ((beforeInputs.source inputIndex).sample index) := by
      intro inputIndex
      dsimp only [afterInputs, Terms.Denotation.Inputs.source]
      rewrite [DependentVector.ofFn_get]
      exact GeometricApproximation.conj_sample _ index
    exact ((Terms.eval_congr _ _ channels input.form.conj.terms).trans
      (Sparse.eval_conj (fun inputIndex => (beforeInputs.source inputIndex).sample index) input.form)).symm)
  exact ofPrepared cached.after afterInputs (compared.trans samples.toNamed)

/-- Conjugation consumes the literal supplied target interpretation, including its actual stored power channels. -/
theorem conj_denotation {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (cached : ConjInputs input) :
    (input.conj cached).denotation = cached.after.denotation := rfl

/-- Conjugation stores the actual computed target coefficient form. -/
theorem conj_form {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (cached : ConjInputs input) :
    (input.conj cached).form = cached.after.form := rfl

end Gaussian.Normalized
end Purelib.Polynomial.Multivariate
end
