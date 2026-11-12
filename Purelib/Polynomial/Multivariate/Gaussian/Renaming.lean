module

import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Multivariate.Evaluation
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Polynomial.Multivariate.Renaming
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Sequence.Equivalence

/-!
# Operational variable renaming of retained polynomial forms

Original and target variable channels are linked by supplied comparisons at
their retained bounded positions. Rebasing transports cached coefficient data
and the original comparison; it never recompiles the source expression.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Data.Vector (DependentVector)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Sequence.Equivalence (approximationEquivalentOfSamplesEq)

namespace Monomial

/-- Finite exponent multiplication is operationally the power of the original monomial channel. -/
def denote_power {arity : Nat} (monomial : Monomial arity) (environment : Fin arity → CoherentNamed) :
    (exponent : Nat) → NamedEquivalent ((power monomial exponent).denote environment).name
      (Power.namedPower (monomial.denote environment) exponent).name
  | 0 => denote_zero arity environment
  | exponent + 1 => NamedEquivalent.trans (denote_add (power monomial exponent) monomial environment)
      (Product.Congruence.coherentMul_respects ((power monomial exponent).denote environment)
        (Power.namedPower (monomial.denote environment) exponent) (monomial.denote environment)
        (monomial.denote environment) (denote_power monomial environment exponent) (NamedEquivalent.refl _))

/-- Renamed monomials compare to their original channels through explicit bounded variable comparisons. -/
def denote_rename {target : Nat} : {source : Nat} → (monomial : Monomial source) →
    (mapping : Fin source → Fin target) → (original : Fin source → CoherentNamed) →
    (destination : Fin target → CoherentNamed) →
    (∀ index, NamedEquivalent (original index).name (destination (mapping index)).name) →
    NamedEquivalent ((rename monomial mapping).denote destination).name (monomial.denote original).name
  | 0, .nil, _, _, destination, _ => denote_zero target destination
  | _ + 1, .cons exponent tail, mapping, original, destination, equivalent =>
      NamedEquivalent.trans
        (denote_add (power (atom target (mapping 0)) exponent)
          (rename tail (fun index => mapping index.succ)) destination)
        (Product.Congruence.coherentMul_respects
          ((power (atom target (mapping 0)) exponent).denote destination)
          (Power.namedPower (original 0) exponent)
          ((rename tail (fun index => mapping index.succ)).denote destination)
          (tail.denote (fun index => original index.succ))
          (NamedEquivalent.trans (denote_power (atom target (mapping 0)) destination exponent)
            (Power.namedPower_respects ((atom target (mapping 0)).denote destination) (original 0)
              (NamedEquivalent.trans (denote_atom target (mapping 0) destination)
                (NamedEquivalent.symm (equivalent 0))) exponent))
          (denote_rename tail (fun index => mapping index.succ) (fun index => original index.succ)
            destination (fun index => equivalent index.succ)))

end Monomial

namespace Term

/-- Renaming a retained term preserves its original operational channel under the supplied variable comparisons. -/
def denote_rename {source target : Nat} (term : Term Coefficient source) (mapping : Fin source → Fin target)
    (original : Fin source → CoherentNamed) (destination : Fin target → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (original index).name (destination (mapping index)).name) :
    NamedEquivalent ((term.rename mapping).denote destination).name (term.denote original).name :=
  Product.Congruence.coherentMul_respects (Coherence.exact term.coefficient) (Coherence.exact term.coefficient)
    ((term.monomial.rename mapping).denote destination) (term.monomial.denote original) (NamedEquivalent.refl _)
    (Monomial.denote_rename term.monomial mapping original destination equivalent)

end Term

namespace Terms

/-- Renaming a retained finite coefficient list preserves its original operational sum. -/
def denote_renamed {source target : Nat} (mapping : Fin source → Fin target)
    (original : Fin source → CoherentNamed) (destination : Fin target → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (original index).name (destination (mapping index)).name) :
    (terms : List (Term Coefficient source)) →
      NamedEquivalent (denote destination (renamed terms mapping)).name (denote original terms).name
  | [] => NamedEquivalent.refl _
  | first :: remaining => Sum.Congruence.coherentAdd_respects ((first.rename mapping).denote destination)
      (first.denote original) (denote destination (renamed remaining mapping)) (denote original remaining)
      (first.denote_rename mapping original destination equivalent)
      (denote_renamed mapping original destination equivalent remaining)

end Terms

namespace Sparse

/-- Canonical variable renaming preserves the original polynomial channel under explicit variable comparisons. -/
def denote_rename {source target : Nat} (polynomial : Sparse Coefficient source)
    (mapping : Fin source → Fin target) (original : Fin source → CoherentNamed)
    (destination : Fin target → CoherentNamed)
    (equivalent : ∀ index, NamedEquivalent (original index).name (destination (mapping index)).name) :
    NamedEquivalent ((polynomial.rename mapping).denote destination).name (polynomial.denote original).name :=
  NamedEquivalent.trans (denote_ofTerms destination (Terms.renamed polynomial.terms mapping))
    (Terms.denote_renamed mapping original destination equivalent polynomial.terms)

end Sparse

namespace Gaussian.Normalized

/-- Actual source and target interpretation caches for the original variable renaming. -/
abbrev RenameInputs {source target : Nat} {original : CoherentNamed} {bindings : Fin source → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (destination : Fin target → CoherentNamed)
    (mapping : Fin source → Fin target) :=
  Terms.Denotation.Prepared bindings normalized.sources normalized.form ×
    Terms.Denotation.Prepared destination [] (normalized.form.rename mapping)

/-- Prepare the original renamed coefficient form and retain its original input interpretation.

When literal variable-channel equalities are supplied, target power banks
consume the same actual source power channels in original occurrence order.
With only operational variable agreement, target powers are genuine new
numerical operations; the original source cache is still retained completely.
-/
@[expose] def prepareRename {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (same : Option (PLift (∀ index, bindings index = destination (mapping index))) := none) :
    RenameInputs normalized destination mapping :=
  let powers := match same with
    | none => none
    | some literal => some (DependentVector.ofFn (fun index =>
        normalized.denotation.sums.renamePowers destination mapping literal.down index))
  ⟨Terms.Denotation.prepare bindings normalized.sources normalized.form (some normalized.denotation),
    Terms.Denotation.prepare destination [] (normalized.form.rename mapping) none powers⟩

/-- Rebase the original normalization through supplied variable relations and optional retained construction inputs.

The default is the original complete result. The cached route retains both
original binding environments and consumes their actual stored power and sum
channels. It transports scalar readings pointwise, without equating functions
or replacing either numerical input owner.
-/
@[expose] def rename {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name)
    (cached : Option (RenameInputs normalized destination mapping) := none) :
    Gaussian.Normalized destination original :=
  match cached with
  | none => by
      let form := normalized.form.rename mapping
      have renamed := Sparse.denote_rename normalized.form mapping bindings destination equivalent
      rewrite [← normalized.channel_eq] at renamed
      exact ofForm destination form (NamedEquivalent.trans normalized.equivalent (NamedEquivalent.symm renamed))
  | some actual => by
      let inputs := Terms.Denotation.inputs destination
      let sourceInputs : Terms.Denotation.Inputs bindings :=
        DependentVector.ofFn (fun index =>
          ⟨inputs.source (mapping index), (equivalent index).trans (inputs.equivalent (mapping index))⟩)
      let before := Terms.source sourceInputs.source normalized.form.terms
      let after := Terms.source inputs.source actual.2.form.terms
      let compared := normalized.source_equivalent actual.1 sourceInputs normalized.source_mem
      let samples := approximationEquivalentOfSamplesEq before.toApproximation after.toApproximation
        (fun index => by
          change before.sample index = after.sample index
          dsimp only [before, after]
          rewrite [Terms.source_sample, Terms.source_sample, actual.2.form_eq]
          have sameSamples := Terms.eval_congr
            (fun inputIndex => (sourceInputs.source inputIndex).sample index)
            (fun inputIndex => (inputs.source (mapping inputIndex)).sample index)
            (fun inputIndex => by
              change ((DependentVector.ofFn (fun position =>
                (⟨inputs.source (mapping position),
                  (equivalent position).trans (inputs.equivalent (mapping position))⟩ :
                    (value : GeometricApproximation) × NamedEquivalent (bindings position).name
                      value.toApproximation.toNamed))).get inputIndex).1.sample index = _
              rewrite [DependentVector.ofFn_get]
              rfl) normalized.form.terms
          exact sameSamples.trans
            (Sparse.eval_rename normalized.form mapping
              (fun inputIndex => (inputs.source inputIndex).sample index)).symm)
      exact ofPrepared actual.2 inputs (compared.trans samples.toNamed)

/-- The complete default renaming is the original coefficient, numerical and relation construction. -/
theorem rename_default {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name) :
    rename normalized destination mapping equivalent none = (by
      let form := normalized.form.rename mapping
      have renamed := Sparse.denote_rename normalized.form mapping bindings destination equivalent
      rewrite [← normalized.channel_eq] at renamed
      exact ofForm destination form (NamedEquivalent.trans normalized.equivalent (NamedEquivalent.symm renamed))
    ) := rfl

/-- Cached renaming consumes the literal actual target interpretation. -/
theorem rename_cached_denotation {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name)
    (cached : RenameInputs normalized destination mapping) :
    (rename normalized destination mapping equivalent (some cached)).denotation = cached.2.denotation := rfl

/-- Cached renaming retains the complete original target numerical interpretation channel. -/
theorem rename_cached_channel {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name)
    (cached : RenameInputs normalized destination mapping) :
    (rename normalized destination mapping equivalent (some cached)).channel =
      (rename normalized destination mapping equivalent).channel :=
  (rename normalized destination mapping equivalent (some cached)).channel_eq.trans
    ((congrArg (fun form => form.denote destination) cached.2.form_eq).trans
      (rename normalized destination mapping equivalent).channel_eq.symm)

/-- Cached renaming reads its complete stored coefficient construction. -/
theorem rename_cached_form {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name)
    (cached : RenameInputs normalized destination mapping) :
    (rename normalized destination mapping equivalent (some cached)).form = cached.2.form := rfl

/-- Rebasing reads the original stored coefficients and the supplied bounded map. -/
theorem rename_form {source target : Nat} {original : CoherentNamed}
    {bindings : Fin source → CoherentNamed} (normalized : Gaussian.Normalized bindings original)
    (destination : Fin target → CoherentNamed) (mapping : Fin source → Fin target)
    (equivalent : ∀ index, NamedEquivalent (bindings index).name (destination (mapping index)).name)
    (cached : Option (RenameInputs normalized destination mapping) := none) :
    (normalized.rename destination mapping equivalent cached).form = normalized.form.rename mapping := by
  cases cached with
  | none => rfl
  | some actual => exact (rename_cached_form normalized destination mapping equivalent actual).trans actual.2.form_eq

end Gaussian.Normalized

end Purelib.Polynomial.Multivariate

end
