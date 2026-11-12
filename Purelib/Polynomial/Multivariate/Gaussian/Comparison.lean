module

public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Comparison of retained polynomial normalizations

Equal coefficient forms compare original channels through their cached
certificates. Unequal forms retain a formal obstruction to this comparison
route; no inequality of opaque numerical readings is asserted.
-/

public section

namespace Purelib.Polynomial.Multivariate.Gaussian.Normalized

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {arity : Nat} {bindings : Fin arity → CoherentNamed} {first second : CoherentNamed}

set_option genInjectivity false in
/-- Equal retained coefficients with their operational certificate, or precise formal disagreement. -/
inductive Comparison (left : Normalized bindings first) (right : Normalized bindings second) where
  /-- Retain whole-form equality and the comparison of the two actual original channels. -/
  | equal (forms_eq : left.form.terms = right.form.terms) (equivalent : NamedEquivalent first.name second.name)
  /-- Retain unequal formal coefficient data, which supplies no inequality of numerical values. -/
  | unresolved (forms_ne : left.form.terms ≠ right.form.terms)

constructive_injectivity Comparison

/-- Compare existing cached forms, producing a certified identity or a retained unresolved formal comparison. -/
@[expose] def compareForms (left : Normalized bindings first) (right : Normalized bindings second) :
    Comparison left right :=
  if same : left.form.terms = right.form.terms then .equal same (left.compare right same)
  else .unresolved same

/-- Compare original channels across two explicitly related original environments.

The atom-wise comparisons are supplied for every retained bounded position.
Both original normalizations and their independent channels remain the inputs. -/
def compareAcross {leftBindings rightBindings : Fin arity → CoherentNamed}
    (left : Normalized leftBindings first) (right : Normalized rightBindings second)
    (bindingsEquivalent : ∀ index, NamedEquivalent (leftBindings index).name (rightBindings index).name)
    (same : left.form.terms = right.form.terms) : NamedEquivalent first.name second.name := by
  let comparedRight := right.denotation.cast same.symm
  have compared := left.denotation.compareAcross comparedRight bindingsEquivalent
  change NamedEquivalent left.denotation.channel.name right.denotation.channel.name at compared
  rewrite [← left.denotation_eq, ← right.denotation_eq] at compared
  exact NamedEquivalent.trans left.equivalent (NamedEquivalent.trans compared (NamedEquivalent.symm right.equivalent))

end Purelib.Polynomial.Multivariate.Gaussian.Normalized

end
