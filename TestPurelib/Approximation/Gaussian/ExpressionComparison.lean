module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Comparison
import Purelib.Polynomial.Multivariate.Gaussian.Comparison
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Original expression comparison regressions

Commuted expressions use shared retained original bindings. Distinct source
indices remain formally unresolved even when their numerical channels are
identical. Independent channels require an explicit operational comparison.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionComparison

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Multivariate

/-- The original opaque annotations at two distinct source indices. -/
private def environment (first second : CoherentNamed) : Fin 2 → Annotated :=
  Fin.cases (Annotated.opaque first) (fun _ => Annotated.opaque second)

/-- Observe the route of an already typed comparison result. -/
private def equalRoute {arity : Nat} {bindings : Fin arity → CoherentNamed} {first second : CoherentNamed}
    {left : Gaussian.Normalized bindings first} {right : Gaussian.Normalized bindings second} :
    Gaussian.Normalized.Comparison left right → Bool
  | .equal _ _ => true
  | .unresolved _ => false

/-- The typed comparison's route is determined by its actual retained coefficient equality test. -/
private theorem equalRoute_compareForms {arity : Nat} {bindings : Fin arity → CoherentNamed}
    {first second : CoherentNamed} (left : Gaussian.Normalized bindings first)
    (right : Gaussian.Normalized bindings second) :
    equalRoute (left.compareForms right) = decide (left.form.terms = right.form.terms) := by
  unfold Gaussian.Normalized.compareForms
  split
  · rename_i same
    exact (decide_eq_true same).symm
  · rename_i different
    exact (decide_eq_false different).symm

example (first second : CoherentNamed) :
    equalRoute (((Expr.add (.atom 0) (.atom 1)).comparison (environment first second)
      (.add (.atom 1) (.atom 0))).decide) = true := by
  unfold Comparison.decide
  rewrite [equalRoute_compareForms]
  unfold Expr.comparison Compiled.comparison
  rewrite [Normalized.comparison_left_form, Normalized.comparison_right_form]
  unfold Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form, Construction.normalize_form]
  unfold Normalized.comparison Binding.Alignment.ofInclusion
  dsimp only
  cbv

example (input : CoherentNamed) :
    equalRoute (((Expr.atom (0 : Fin 2)).comparison (fun _ => Annotated.opaque input) (.atom 1)).decide) = false := by
  unfold Comparison.decide
  rewrite [equalRoute_compareForms]
  unfold Expr.comparison Compiled.comparison
  rewrite [Normalized.comparison_left_form, Normalized.comparison_right_form]
  unfold Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form, Construction.normalize_form]
  unfold Normalized.comparison Binding.Alignment.ofInclusion
  dsimp only
  cbv

example (first second : CoherentNamed) (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent first.name second.name :=
  (Gaussian.Normalized.atom (fun _ : Fin 1 => first) 0).compareAcross
    (Gaussian.Normalized.atom (fun _ : Fin 1 => second) 0) (fun _ => equivalent) rfl

end TestPurelib.Approximation.Gaussian.ExpressionComparison
