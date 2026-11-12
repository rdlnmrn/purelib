module

import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Polynomial.Multivariate.Gaussian.Denotation
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Coherent.Additive
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained operational polynomial normalizations

The original coherent channel remains an index of its normalization. Finite
coefficient data, the normal channel and the executable comparison are retained
together; comparison and rational evidence consume those same cached fields.
-/

public section

namespace Purelib.Polynomial.Multivariate.Gaussian

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Data.List.Membership (mem_cons)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Approximation
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Sequence.Equivalence (approximationEquivalentOfSamplesEq)
open Purelib.Approximation.Gaussian.Coherent

set_option genInjectivity false in
/-- A cached polynomial normalization indexed by its original bindings and original coherent channel. -/
structure Normalized {arity : Nat} (bindings : Fin arity → CoherentNamed) (original : CoherentNamed) where
  /-- The actual computed canonical finite coefficient data. -/
  form : Sparse Coefficient arity
  /-- The actual original coefficient, monomial-product and suffix-sum caches. -/
  denotation : Terms.Denotation bindings form.terms
  /-- The retained coherent interpretation of the computed normal form. -/
  channel : CoherentNamed
  /-- The normal channel is this same retained interpretation's actual output. -/
  denotation_eq : channel = denotation.channel
  /-- Exact readback of the retained normal channel to its defining interpretation. -/
  channel_eq : channel = form.denote bindings
  /-- The retained executable comparison from the original channel to this same normal channel. -/
  equivalent : NamedEquivalent original.name channel.name

constructive_injectivity Normalized

namespace Normalized

variable {arity : Nat} {bindings : Fin arity → CoherentNamed}

/-- Retain a supplied coefficient form and its interpretation, transporting a comparison to the same cached output. -/
@[expose] def ofForm (bindings : Fin arity → CoherentNamed) (form : Sparse Coefficient arity)
    {original : CoherentNamed} (equivalent : NamedEquivalent original.name (form.denote bindings).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings) := fun _ => none)
    (complete : Option (PLift (Terms.CacheComplete bindings cached form.terms)) := none) :
    Normalized bindings original := by
  let denotation := match complete with
    | none => Terms.retainWith bindings cached form.terms
    | some known => Terms.retainFrom bindings cached form.terms known.down
  have cache_eq : denotation.channel = form.denote bindings := denotation.channel_eq
  have compared := equivalent
  rewrite [← cache_eq] at compared
  exact ⟨form, denotation, denotation.channel, rfl, cache_eq, compared⟩

/-- Form construction retains the exact interpretation produced with the supplied monomial lookup. -/
theorem ofForm_denotation (bindings : Fin arity → CoherentNamed) (form : Sparse Coefficient arity)
    {original : CoherentNamed} (equivalent : NamedEquivalent original.name (form.denote bindings).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings)) :
    (ofForm bindings form equivalent cached).denotation = Terms.retainWith bindings cached form.terms := rfl

/-- Complete-cache form construction consumes the certified retained interpretation without a fresh product fallback. -/
theorem ofForm_complete_denotation (bindings : Fin arity → CoherentNamed) (form : Sparse Coefficient arity)
    {original : CoherentNamed} (equivalent : NamedEquivalent original.name (form.denote bindings).name)
    (cached : (monomial : Monomial arity) → Option (Monomial.Denotation monomial bindings))
    (complete : Terms.CacheComplete bindings cached form.terms) :
    (ofForm bindings form equivalent cached (some ⟨complete⟩)).denotation =
      Terms.retainFrom bindings cached form.terms complete := rfl

/-- Read the same retained comparison with its normal-form specification as the target index. -/
def toForm {original : CoherentNamed} (normalized : Normalized bindings original) :
    NamedEquivalent original.name (normalized.form.denote bindings).name := by
  have comparison := normalized.equivalent
  rewrite [normalized.channel_eq] at comparison
  exact comparison

/-- Normalize an actual original channel directly from its retained exact-coefficient comparison. -/
@[expose] def ofRational (bindings : Fin arity → CoherentNamed) {original : CoherentNamed}
    (rational : RationalSidecar original) : Normalized bindings original :=
  let form := Sparse.constant rational.value
  ofForm bindings form (NamedEquivalent.trans rational.equivalent
    (NamedEquivalent.symm (Sparse.denote_constant bindings rational.value)))

/-- Retain the normalized exact coefficient without changing its original terminating channel. -/
@[expose] def constant (bindings : Fin arity → CoherentNamed) (value : Coefficient) :
    Normalized bindings (Coherence.exact value) :=
  let form := Sparse.constant value
  ofForm bindings form (NamedEquivalent.symm (Sparse.denote_constant bindings value))

/-- Retain the original binding owner and its canonical degree-one coefficient form. -/
@[expose] def atom (bindings : Fin arity → CoherentNamed) (index : Fin arity) :
    Normalized bindings (bindings index) :=
  let form := Sparse.atom index
  ofForm bindings form (NamedEquivalent.symm (Sparse.denote_atom bindings index))

/-- Normalize an original channel at a binding justified by its supplied operational comparison.

The atom's coefficient position remains in the original binding environment.
The original input channel and its comparison are retained by the resulting
normalization, so normalization does not replace the input's nominal owner.
-/
@[expose] def ofAtomComparison (bindings : Fin arity → CoherentNamed) (index : Fin arity)
    {original : CoherentNamed} (equivalent : NamedEquivalent original.name (bindings index).name) :
    Normalized bindings original :=
  ofForm bindings (Sparse.atom index)
    (equivalent.trans (Sparse.denote_atom bindings index).symm)

/-- Construct a normalization from the literal supplied complete interpretation and original relation witness.

The coefficient form, product/sum caches, numerical output and executable
comparison are stored without invoking the canonical polynomial interpreter.
The original numerical input remains the normalization's index.
-/
@[expose] def ofDenotation (bindings : Fin arity → CoherentNamed) (form : Sparse Coefficient arity)
    (denotation : Terms.Denotation bindings form.terms) {original : CoherentNamed}
    (equivalent : NamedEquivalent original.name denotation.channel.name) : Normalized bindings original :=
  ⟨form, denotation, denotation.channel, rfl, denotation.channel_eq, equivalent⟩

/-- Complete-interpretation construction retains the exact supplied product and ordered-sum cache. -/
theorem ofDenotation_denotation (bindings : Fin arity → CoherentNamed) (form : Sparse Coefficient arity)
    (denotation : Terms.Denotation bindings form.terms) {original : CoherentNamed}
    (equivalent : NamedEquivalent original.name denotation.channel.name) :
    (ofDenotation bindings form denotation equivalent).denotation = denotation := rfl

/-- The original single input occurrence used by a retained exact coefficient operation. -/
@[expose] def sources {original : CoherentNamed} (input : Normalized bindings original) : Terms.Caches bindings :=
  [⟨input.form.terms, input.denotation⟩]

/-- The two original input occurrences used by an ordered binary coefficient operation. -/
@[expose] def pairedSources {first second : CoherentNamed}
    (left : Normalized bindings first) (right : Normalized bindings second) : Terms.Caches bindings :=
  [⟨left.form.terms, left.denotation⟩, ⟨right.form.terms, right.denotation⟩]

/-- The actual original input is the retained unary source occurrence. -/
theorem source_mem {original : CoherentNamed} (input : Normalized bindings original) :
    (⟨input.form.terms, input.denotation⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation bindings items) ∈ input.sources :=
  mem_cons.mpr (Or.inl rfl)

/-- The actual left input remains the first retained binary source occurrence. -/
theorem left_mem {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    (⟨left.form.terms, left.denotation⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation bindings items) ∈ pairedSources left right :=
  mem_cons.mpr (Or.inl rfl)

/-- The actual right input remains the second retained binary source occurrence. -/
theorem right_mem {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    (⟨right.form.terms, right.denotation⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation bindings items) ∈ pairedSources left right :=
  mem_cons.mpr
    (Or.inr (mem_cons.mpr (Or.inl rfl)))

/-- Compare the original indexed numerical input using its actual cached source occurrence and original relation.

The prepared bank receives the literal source denotation. Endpoint transport
uses its construction equality, while execution composes the original stored
comparison with the actual product/sum-cache bridge.
-/
def source_equivalent {original : CoherentNamed} (input : Normalized bindings original)
    {sources : Terms.Caches bindings} {target : Sparse Coefficient arity}
    (cached : Terms.Denotation.Prepared bindings sources target) (inputs : Terms.Denotation.Inputs bindings)
    (present : (⟨input.form.terms, input.denotation⟩ : (items : List (Term Coefficient arity)) ×
      Terms.Denotation bindings items) ∈ sources) :
    NamedEquivalent original.name (Terms.source inputs.source input.form.terms).toApproximation.toNamed := by
  have actual := cached.source_equivalent inputs input.denotation present
  rewrite [← input.denotation_eq] at actual
  exact input.equivalent.trans actual

/-- Retain a prepared coefficient construction and its actual comparison from the original numerical input. -/
@[expose] def ofPrepared {original : CoherentNamed} {sources : Terms.Caches bindings}
    {target : Sparse Coefficient arity} (cached : Terms.Denotation.Prepared bindings sources target)
    (inputs : Terms.Denotation.Inputs bindings)
    (equivalent : NamedEquivalent original.name
      (Terms.source inputs.source cached.form.terms).toApproximation.toNamed) :
    Normalized bindings original :=
  ofDenotation bindings cached.form cached.denotation (equivalent.trans (cached.equivalent inputs).symm)

/-- Prepared construction retains its actual comparison, including starts, tolerance and paid indices. -/
theorem ofPrepared_equivalent {original : CoherentNamed} {sources : Terms.Caches bindings}
    {target : Sparse Coefficient arity} (cached : Terms.Denotation.Prepared bindings sources target)
    (inputs : Terms.Denotation.Inputs bindings)
    (equivalent : NamedEquivalent original.name
      (Terms.source inputs.source cached.form.terms).toApproximation.toNamed) :
    (ofPrepared cached inputs equivalent).equivalent = equivalent.trans (cached.equivalent inputs).symm := rfl

/-- Prepared construction stores the literal actual coefficient-operation output cache. -/
theorem ofPrepared_denotation {original : CoherentNamed} {sources : Terms.Caches bindings}
    {target : Sparse Coefficient arity} (cached : Terms.Denotation.Prepared bindings sources target)
    (inputs : Terms.Denotation.Inputs bindings)
    (equivalent : NamedEquivalent original.name
      (Terms.source inputs.source cached.form.terms).toApproximation.toNamed) :
    (ofPrepared cached inputs equivalent).denotation = cached.denotation := rfl

/-- Prepare the original negated coefficient form from the same retained input powers and suffix products. -/
@[expose] def prepareNeg {original : CoherentNamed} (input : Normalized bindings original) :
    Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form) :=
  Terms.Denotation.prepare bindings input.sources (Sparse.neg input.form)

/-- Normalize negation using the retained child coefficients and original child comparison. -/
@[expose] def neg {original : CoherentNamed} (input : Normalized bindings original)
    (cached : Option (Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form)) := none) :
    Normalized bindings (CoherentNamed.neg original) :=
  match cached with
  | none => by
      let form := Sparse.neg input.form
      have normal := NamedEquivalent.symm (Sparse.denote_neg bindings input.form)
      rewrite [← input.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Additive.coherentNeg_respects original input.channel input.equivalent) normal
      exact ofForm bindings form comparison input.denotation.findMonomial
  | some actual => by
      let inputs := Terms.Denotation.inputs bindings
      let before := Terms.source inputs.source input.form.terms
      let after := Terms.source inputs.source actual.form.terms
      let comparison := CoherentEvaluation.neg_agrees original before
        (input.source_equivalent actual inputs input.source_mem)
      let samples := approximationEquivalentOfSamplesEq before.neg.toApproximation after.toApproximation
        (fun index => by
          change before.neg.sample index = after.sample index
          dsimp only [before, after]
          rewrite [GeometricApproximation.neg_sample, Terms.source_sample, Terms.source_sample, actual.form_eq]
          exact (Sparse.eval_neg (fun inputIndex => (inputs.source inputIndex).sample index) input.form).symm)
      exact ofPrepared actual inputs (comparison.trans samples.toNamed)

/-- The complete default neg construction is the original numerical, coefficient and relation result. -/
theorem neg_default {original : CoherentNamed} (input : Normalized bindings original) :
    neg input none = (by
      let form := Sparse.neg input.form
      have normal := NamedEquivalent.symm (Sparse.denote_neg bindings input.form)
      rewrite [← input.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Additive.coherentNeg_respects original input.channel input.equivalent) normal
      exact ofForm bindings form comparison input.denotation.findMonomial
    ) := rfl

/-- Cached neg consumes the literal prepared output interpretation. -/
theorem neg_cached_denotation {original : CoherentNamed} (input : Normalized bindings original)
    (cached : Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form)) :
    (neg input (some cached)).denotation = cached.denotation := rfl

/-- Cached neg retains the complete original numerical output channel. -/
theorem neg_cached_channel {original : CoherentNamed} (input : Normalized bindings original)
    (cached : Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form)) :
    (neg input (some cached)).channel = (neg input).channel :=
  (neg input (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote bindings) cached.form_eq).trans (neg input).channel_eq.symm)

/-- Cached neg reads the stored coefficient construction rather than computing its form again. -/
theorem neg_cached_form {original : CoherentNamed} (input : Normalized bindings original)
    (cached : Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form)) :
    (neg input (some cached)).form = cached.form := rfl

/-- Prepare the original ordered sum coefficient form from both retained input caches. -/
@[expose] def prepareAdd {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.add left.form right.form) :=
  Terms.Denotation.prepare bindings (pairedSources left right) (Sparse.add left.form right.form)

/-- Normalize the actual original sum using both retained child forms and comparisons. -/
@[expose] def add {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option (Terms.Denotation.Prepared bindings (pairedSources left right)
      (Sparse.add left.form right.form)) := none) : Normalized bindings (CoherentNamed.add first second) :=
  match cached with
  | none => by
      let form := Sparse.add left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_add bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects first left.channel second right.channel
          left.equivalent right.equivalent) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
  | some actual => by
      let inputs := Terms.Denotation.inputs bindings
      let firstSource := Terms.source inputs.source left.form.terms
      let secondSource := Terms.source inputs.source right.form.terms
      let after := Terms.source inputs.source actual.form.terms
      let comparison := CoherentEvaluation.add_agrees first second firstSource secondSource
        (left.source_equivalent actual inputs (left_mem left right))
        (right.source_equivalent actual inputs (right_mem left right))
      let samples := approximationEquivalentOfSamplesEq
        (firstSource.add secondSource).toApproximation after.toApproximation
        (fun index => by
          change (firstSource.add secondSource).sample index = after.sample index
          dsimp only [firstSource, secondSource, after]
          rewrite [GeometricApproximation.add_sample, Terms.source_sample, Terms.source_sample, Terms.source_sample,
            actual.form_eq]
          exact (Sparse.eval_add (fun inputIndex => (inputs.source inputIndex).sample index) left.form right.form).symm)
      exact ofPrepared actual inputs (comparison.trans samples.toNamed)

/-- The complete default add construction is the original numerical, coefficient and relation result. -/
theorem add_default {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    add left right none = (by
      let form := Sparse.add left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_add bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects first left.channel second right.channel
          left.equivalent right.equivalent) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
    ) := rfl

/-- Cached add consumes the literal prepared output interpretation. -/
theorem add_cached_denotation {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.add left.form right.form)) :
    (add left right (some cached)).denotation = cached.denotation := rfl

/-- Cached add retains the complete original numerical output channel. -/
theorem add_cached_channel {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.add left.form right.form)) :
    (add left right (some cached)).channel = (add left right).channel :=
  (add left right (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote bindings) cached.form_eq).trans (add left right).channel_eq.symm)

/-- Cached add reads the stored coefficient construction rather than computing its form again. -/
theorem add_cached_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.add left.form right.form)) :
    (add left right (some cached)).form = cached.form := rfl

/-- Prepare the original ordered difference coefficient form from both retained input caches. -/
@[expose] def prepareSub {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.sub left.form right.form) :=
  Terms.Denotation.prepare bindings (pairedSources left right) (Sparse.sub left.form right.form)

/-- Normalize the actual original difference using both retained child forms and comparisons. -/
@[expose] def sub {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option (Terms.Denotation.Prepared bindings (pairedSources left right)
      (Sparse.sub left.form right.form)) := none) :
    Normalized bindings (CoherentNamed.add first (CoherentNamed.neg second)) :=
  match cached with
  | none => by
      let form := Sparse.sub left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_sub bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects first left.channel
          (CoherentNamed.neg second) (CoherentNamed.neg right.channel) left.equivalent
          (Additive.coherentNeg_respects second right.channel right.equivalent)) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
  | some actual => by
      let inputs := Terms.Denotation.inputs bindings
      let firstSource := Terms.source inputs.source left.form.terms
      let secondSource := Terms.source inputs.source right.form.terms
      let after := Terms.source inputs.source actual.form.terms
      let comparison := CoherentEvaluation.add_agrees first (CoherentNamed.neg second) firstSource secondSource.neg
        (left.source_equivalent actual inputs (left_mem left right))
        (CoherentEvaluation.neg_agrees second secondSource
          (right.source_equivalent actual inputs (right_mem left right)))
      let samples := approximationEquivalentOfSamplesEq
        (firstSource.add secondSource.neg).toApproximation after.toApproximation
        (fun index => by
          change (firstSource.add secondSource.neg).sample index = after.sample index
          dsimp only [firstSource, secondSource, after]
          rewrite [GeometricApproximation.add_sample, GeometricApproximation.neg_sample,
            Terms.source_sample, Terms.source_sample, Terms.source_sample,
            actual.form_eq]
          have identity := Sparse.eval_sub
            (fun inputIndex => (inputs.source inputIndex).sample index) left.form right.form
          exact ((sub_eq_add_neg _ _).symm.trans identity.symm))
      exact ofPrepared actual inputs (comparison.trans samples.toNamed)

/-- The complete default sub construction is the original numerical, coefficient and relation result. -/
theorem sub_default {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    sub left right none = (by
      let form := Sparse.sub left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_sub bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects first left.channel
          (CoherentNamed.neg second) (CoherentNamed.neg right.channel) left.equivalent
          (Additive.coherentNeg_respects second right.channel right.equivalent)) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
    ) := rfl

/-- Cached sub consumes the literal prepared output interpretation. -/
theorem sub_cached_denotation {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.sub left.form right.form)) :
    (sub left right (some cached)).denotation = cached.denotation := rfl

/-- Cached sub retains the complete original numerical output channel. -/
theorem sub_cached_channel {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.sub left.form right.form)) :
    (sub left right (some cached)).channel = (sub left right).channel :=
  (sub left right (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote bindings) cached.form_eq).trans (sub left right).channel_eq.symm)

/-- Cached sub reads the stored coefficient construction rather than computing its form again. -/
theorem sub_cached_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.sub left.form right.form)) :
    (sub left right (some cached)).form = cached.form := rfl

/-- Prepare the original product coefficient form from both retained input caches. -/
@[expose] def prepareMul {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.mul left.form right.form) :=
  Terms.Denotation.prepare bindings (pairedSources left right) (Sparse.mul left.form right.form)

/-- Normalize the actual original product using both retained child forms and comparisons. -/
@[expose] def mul {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option (Terms.Denotation.Prepared bindings (pairedSources left right)
      (Sparse.mul left.form right.form)) := none) : Normalized bindings (CoherentNamed.mul first second) :=
  match cached with
  | none => by
      let form := Sparse.mul left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_mul bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects first left.channel second right.channel
          left.equivalent right.equivalent) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
  | some actual => by
      let inputs := Terms.Denotation.inputs bindings
      let firstSource := Terms.source inputs.source left.form.terms
      let secondSource := Terms.source inputs.source right.form.terms
      let after := Terms.source inputs.source actual.form.terms
      let comparison := CoherentEvaluation.mul_agrees first second firstSource secondSource
        (left.source_equivalent actual inputs (left_mem left right))
        (right.source_equivalent actual inputs (right_mem left right))
      let samples := approximationEquivalentOfSamplesEq
        (firstSource.mul secondSource).toApproximation after.toApproximation
        (fun index => by
          change (firstSource.mul secondSource).sample index = after.sample index
          dsimp only [firstSource, secondSource, after]
          rewrite [GeometricApproximation.mul_sample, Terms.source_sample, Terms.source_sample, Terms.source_sample,
            actual.form_eq]
          exact (Sparse.eval_mul (fun inputIndex => (inputs.source inputIndex).sample index) left.form right.form).symm)
      exact ofPrepared actual inputs (comparison.trans samples.toNamed)

/-- The complete default mul construction is the original numerical, coefficient and relation result. -/
theorem mul_default {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second) :
    mul left right none = (by
      let form := Sparse.mul left.form right.form
      have normal := NamedEquivalent.symm (Sparse.denote_mul bindings left.form right.form)
      rewrite [← left.channel_eq, ← right.channel_eq] at normal
      let comparison := NamedEquivalent.trans
        (Product.Congruence.coherentMul_respects first left.channel second right.channel
          left.equivalent right.equivalent) normal
      exact ofForm bindings form comparison (fun monomial =>
        match left.denotation.findMonomial monomial with
        | some retained => some retained
        | none => right.denotation.findMonomial monomial)
    ) := rfl

/-- Cached mul consumes the literal prepared output interpretation. -/
theorem mul_cached_denotation {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.mul left.form right.form)) :
    (mul left right (some cached)).denotation = cached.denotation := rfl

/-- Cached mul retains the complete original numerical output channel. -/
theorem mul_cached_channel {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.mul left.form right.form)) :
    (mul left right (some cached)).channel = (mul left right).channel :=
  (mul left right (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote bindings) cached.form_eq).trans (mul left right).channel_eq.symm)

/-- Cached mul reads the stored coefficient construction rather than computing its form again. -/
theorem mul_cached_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.mul left.form right.form)) :
    (mul left right (some cached)).form = cached.form := rfl

/-- Exact coefficient normalization retains the original constant form. -/
theorem constant_form (bindings : Fin arity → CoherentNamed) (value : Coefficient) :
    (constant bindings value).form = Sparse.constant value := rfl

/-- Variable normalization retains the original degree-one coefficient form. -/
theorem atom_form (bindings : Fin arity → CoherentNamed) (index : Fin arity) :
    (atom bindings index).form = Sparse.atom index := rfl

/-- Exact rational normalization reads its original supplied coefficient without rebuilding its certificate. -/
theorem ofRational_form (bindings : Fin arity → CoherentNamed) {original : CoherentNamed}
    (rational : RationalSidecar original) :
    (ofRational bindings rational).form = Sparse.constant rational.value := rfl

/-- An original-channel comparison retains the same bounded atom position in its coefficient form. -/
theorem ofAtomComparison_form (bindings : Fin arity → CoherentNamed) (index : Fin arity)
    {original : CoherentNamed} (equivalent : NamedEquivalent original.name (bindings index).name) :
    (ofAtomComparison bindings index equivalent).form = Sparse.atom index := rfl

/-- Negation reads only the retained child's original coefficient form. -/
theorem neg_form {original : CoherentNamed} (input : Normalized bindings original)
    (cached : Option (Terms.Denotation.Prepared bindings input.sources (Sparse.neg input.form)) := none) :
    (input.neg cached).form = Sparse.neg input.form := by
  cases cached with
  | none => rfl
  | some actual => exact (neg_cached_form input actual).trans actual.form_eq

/-- Addition reads the same two retained original coefficient forms. -/
theorem add_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option
      (Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.add left.form right.form)) := none) :
    (left.add right cached).form = Sparse.add left.form right.form := by
  cases cached with
  | none => rfl
  | some actual => exact (add_cached_form left right actual).trans actual.form_eq

/-- Subtraction reads the same two retained original coefficient forms. -/
theorem sub_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option
      (Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.sub left.form right.form)) := none) :
    (left.sub right cached).form = Sparse.sub left.form right.form := by
  cases cached with
  | none => rfl
  | some actual => exact (sub_cached_form left right actual).trans actual.form_eq

/-- Multiplication reads the same two retained original coefficient forms. -/
theorem mul_form {first second : CoherentNamed} (left : Normalized bindings first)
    (right : Normalized bindings second)
    (cached : Option
      (Terms.Denotation.Prepared bindings (pairedSources left right) (Sparse.mul left.form right.form)) := none) :
    (left.mul right cached).form = Sparse.mul left.form right.form := by
  cases cached with
  | none => rfl
  | some actual => exact (mul_cached_form left right actual).trans actual.form_eq

/-- Transport a normalization to an exactly equal original channel, retaining every computed field. -/
@[expose] def transport {first second : CoherentNamed} (normalized : Normalized bindings first)
    (same : first = second) : Normalized bindings second :=
  { form := normalized.form
    denotation := normalized.denotation
    channel := normalized.channel
    denotation_eq := normalized.denotation_eq
    channel_eq := normalized.channel_eq
    equivalent := same ▸ normalized.equivalent }

/-- Original-channel transport preserves the exact supplied coefficient form. -/
theorem transport_form {first second : CoherentNamed} (normalized : Normalized bindings first)
    (same : first = second) : (normalized.transport same).form = normalized.form := rfl

/-- Original-channel transport retains the literal coefficient, monomial and sum interpretation cache. -/
theorem transport_denotation {first second : CoherentNamed} (normalized : Normalized bindings first)
    (same : first = second) : (normalized.transport same).denotation = normalized.denotation := rfl

/-- Precompose an operational source comparison while retaining every existing normalization cache.

Only the original-channel comparison is composed. The coefficient form,
monomial and sum denotation, and normal channel remain the supplied values.
-/
@[expose] def precompose {first second : CoherentNamed} (normalized : Normalized bindings second)
    (equivalent : NamedEquivalent first.name second.name) : Normalized bindings first :=
  { form := normalized.form
    denotation := normalized.denotation
    channel := normalized.channel
    denotation_eq := normalized.denotation_eq
    channel_eq := normalized.channel_eq
    equivalent := equivalent.trans normalized.equivalent }

/-- Precomposition preserves the exact supplied coefficient form. -/
theorem precompose_form {first second : CoherentNamed} (normalized : Normalized bindings second)
    (equivalent : NamedEquivalent first.name second.name) :
    (normalized.precompose equivalent).form = normalized.form := rfl

/-- Precomposition preserves the supplied coefficient, monomial and suffix-sum denotation. -/
theorem precompose_denotation {first second : CoherentNamed} (normalized : Normalized bindings second)
    (equivalent : NamedEquivalent first.name second.name) :
    (normalized.precompose equivalent).denotation = normalized.denotation := rfl

/-- Precomposition preserves the exact supplied normal channel. -/
theorem precompose_channel {first second : CoherentNamed} (normalized : Normalized bindings second)
    (equivalent : NamedEquivalent first.name second.name) :
    (normalized.precompose equivalent).channel = normalized.channel := rfl

/-- Equal retained forms compare the two original channels through their existing cached comparisons.

The channel equality is a specification proof. Execution reads the actual two
retained comparison fields rather than evaluating the polynomial forms again. -/
def compare {first second : CoherentNamed} (left : Normalized bindings first) (right : Normalized bindings second)
    (same : left.form.terms = right.form.terms) : NamedEquivalent first.name second.name := by
  have formsEqual : left.form.denote bindings = right.form.denote bindings :=
    congrArg (Terms.denote bindings) same
  have channelsEqual : left.channel = right.channel :=
    left.channel_eq.trans (formsEqual.trans right.channel_eq.symm)
  have returnToSecond := NamedEquivalent.symm right.equivalent
  rewrite [← channelsEqual] at returnToSecond
  exact NamedEquivalent.trans left.equivalent returnToSecond

/-- A retained constant form gives exact Gaussian evidence for the unchanged original channel. -/
@[expose] def rational {original : CoherentNamed} (normalized : Normalized bindings original) (value : Coefficient)
    (same : normalized.form.terms = (Sparse.constant value).terms) : RationalSidecar original :=
  ⟨value, NamedEquivalent.trans normalized.toForm
    (NamedEquivalent.trans (Sparse.denote_of_terms_eq bindings same) (Sparse.denote_constant bindings value))⟩

/-- The exact evidence records the displayed constant coefficient. -/
theorem rational_value {original : CoherentNamed} (normalized : Normalized bindings original) (value : Coefficient)
    (same : normalized.form.terms = (Sparse.constant value).terms) :
    (normalized.rational value same).value = value := rfl

end Normalized

end Purelib.Polynomial.Multivariate.Gaussian

end
