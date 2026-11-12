module

import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Polynomial.Multivariate.Gaussian.Operational
import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Approximation.Gaussian.Sequence.Equivalence

/-! # Natural powers of retained original-channel normalizations -/

public section

namespace Purelib.Polynomial.Multivariate.Gaussian.Normalized

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation
open Purelib.Approximation.Gaussian.Sequence.Equivalence (approximationEquivalentOfSamplesEq)

/-- The actual coefficient and original numerical-power caches of one finite power construction. -/
abbrev PowInputs {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) :=
  Terms.Denotation.Prepared bindings input.sources (input.form.pow exponent) ×
    Monomial.PowerPrefix original (exponent + 1)

/-- Prepare the original finite coefficient power and stored predecessor bank once.

The optional original power entries retain their actual channels and equations.
Only missing predecessors are built, and the final actual original power is
read directly from that bank when constructing the operational relation.
-/
@[expose] def preparePow {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat)
    (retained : List (Monomial.PowerEntry original) := []) : PowInputs input exponent :=
  ⟨Terms.Denotation.prepare bindings input.sources (input.form.pow exponent),
    Monomial.retainPowerPrefix original retained (exponent + 1)⟩

/-- Normalize a natural power from the original coefficient operation and optional actual retained construction inputs.

The default is the original complete result. A supplied cache is consumed
literally; its original numerical power and coefficient interpretation are
compared through the same retained predecessor and variable-power banks.
-/
@[expose] def pow {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat)
    (cached : Option (PowInputs input exponent) := none) :
    Normalized bindings (Power.namedPower original exponent) :=
  match cached with
  | none => by
      let form := input.form.pow exponent
      have power := Power.namedPower_respects original input.channel input.equivalent exponent
      have normal := (Sparse.denote_pow bindings input.form exponent).symm
      rewrite [← input.channel_eq] at normal
      exact ofForm bindings form (power.trans normal) input.denotation.findMonomial
  | some actual => by
      let inputs := Terms.Denotation.inputs bindings
      let before := Terms.source inputs.source input.form.terms
      let after := Terms.source inputs.source actual.1.form.terms
      let power := Monomial.powerFrom original actual.2.val exponent
        (actual.2.property exponent (Nat.lt_succ_self exponent))
      have compared := Monomial.powerFrom_agrees original before
        (input.source_equivalent actual.1 inputs input.source_mem) actual.2
        ⟨exponent, Nat.lt_succ_self exponent⟩ power
      rewrite [power.property] at compared
      let samples := approximationEquivalentOfSamplesEq
        (CoherentEvaluation.powerSource before exponent).toApproximation after.toApproximation
        (fun index => by
          change (CoherentEvaluation.powerSource before exponent).sample index = after.sample index
          dsimp only [before, after]
          rewrite [CoherentEvaluation.powerSource_sample, Terms.source_sample, Terms.source_sample, actual.1.form_eq]
          exact (Sparse.eval_pow (fun inputIndex => (inputs.source inputIndex).sample index) input.form exponent).symm)
      exact ofPrepared actual.1 inputs (compared.trans samples.toNamed)

/-- The complete default power construction is the original numerical, coefficient and relation result. -/
theorem pow_default {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) :
    pow input exponent none = (by
      let form := input.form.pow exponent
      have power := Power.namedPower_respects original input.channel input.equivalent exponent
      have normal := (Sparse.denote_pow bindings input.form exponent).symm
      rewrite [← input.channel_eq] at normal
      exact ofForm bindings form (power.trans normal) input.denotation.findMonomial
    ) := rfl

/-- Cached power construction retains the exact supplied coefficient interpretation. -/
theorem pow_cached_denotation {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) (cached : PowInputs input exponent) :
    (pow input exponent (some cached)).denotation = cached.1.denotation := rfl

/-- Cached power retains the complete original numerical coefficient-interpretation output. -/
theorem pow_cached_channel {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) (cached : PowInputs input exponent) :
    (pow input exponent (some cached)).channel = (pow input exponent).channel :=
  (pow input exponent (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote bindings) cached.1.form_eq).trans (pow input exponent).channel_eq.symm)

/-- Cached power construction reads its computed coefficient form literally. -/
theorem pow_cached_form {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) (cached : PowInputs input exponent) :
    (pow input exponent (some cached)).form = cached.1.form := rfl

/-- Natural-power normalization computes its form from the same retained input coefficient data. -/
theorem pow_form {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (input : Normalized bindings original) (exponent : Nat) (cached : Option (PowInputs input exponent) := none) :
    (input.pow exponent cached).form = input.form.pow exponent := by
  cases cached with
  | none => rfl
  | some actual => exact (pow_cached_form input exponent actual).trans actual.1.form_eq

end Purelib.Polynomial.Multivariate.Gaussian.Normalized

end
