module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Comparison
import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence

/-!
# Comparison consumes the actual retained coefficient caches

A sound cached presentation of zero can still contain formally distinct opaque
variables. Comparing that presentation with canonical zero must retain formal
disagreement. Renormalizing its original constant source would lose this data
and incorrectly change the comparison route.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionRebinding

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Multivariate

/-- Retain identical actual input channels at two distinct original opaque atom indices. -/
private def environment (input : CoherentNamed) : Fin 2 → Annotated := fun _ => Annotated.opaque input

/-- The actual two original opaque annotations remain distinct source keys. -/
private def bindings (input : CoherentNamed) : List (Binding (environment input)) :=
  [⟨.atom 0, Annotated.opaque input, rfl⟩, ⟨.atom 1, Annotated.opaque input, rfl⟩]

/-- Retain a sound nonconstant formal presentation of the original exact-zero expression.

The two atom channels agree literally, so their difference compares to zero.
Its formal coefficients remain distinct because the original indices differ. -/
private def retainedDifference (input : CoherentNamed) : Normalized (environment input) (.rational 0) :=
  let source := (Expr.rational 0 : Expr 2).retain (environment input)
  let table := bindings input
  let first : Fin table.length := ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩
  let second : Fin table.length := ⟨1, by change 1 < 2; exact Nat.lt_succ_self 1⟩
  let difference := (Gaussian.Normalized.atom (Binding.channels table) first).sub
    (Gaussian.Normalized.atom (Binding.channels table) second)
  { compiled := source
    bindings := table
    inspections := Binding.inspect table
    supported := True.intro
    polynomial :=
      { form := difference.form
        denotation := difference.denotation
        channel := difference.channel
        denotation_eq := difference.denotation_eq
        channel_eq := difference.channel_eq
        equivalent := NamedEquivalent.trans (NamedEquivalent.symm (RationalSidecar.addNeg input).equivalent)
          difference.equivalent } }

/-- Read the route of the complete typed comparison outcome. -/
private def equalRoute {arity : Nat} {table : Fin arity → CoherentNamed} {first second : CoherentNamed}
    {left : Gaussian.Normalized table first} {right : Gaussian.Normalized table second} :
    Gaussian.Normalized.Comparison left right → Bool
  | .equal _ _ => true
  | .unresolved _ => false

/-- Inspecting the typed result reads its actual retained coefficient decision. -/
private theorem equalRoute_compareForms {arity : Nat} {table : Fin arity → CoherentNamed}
    {first second : CoherentNamed} (left : Gaussian.Normalized table first)
    (right : Gaussian.Normalized table second) :
    equalRoute (left.compareForms right) = decide (left.form.terms = right.form.terms) := by
  unfold Gaussian.Normalized.compareForms
  split
  · rename_i same
    exact (decide_eq_true same).symm
  · rename_i different
    exact (decide_eq_false different).symm

example (input : CoherentNamed) :
    equalRoute (((retainedDifference input).comparison
      ((Expr.rational 0 : Expr 2).normalize (environment input))).decide) = false := by
  unfold Comparison.decide
  rewrite [equalRoute_compareForms]
  rewrite [Normalized.comparison_left_form, Normalized.comparison_right_form]
  change decide ((Sparse.sub (Sparse.atom (0 : Fin 2)) (Sparse.atom 1)).terms =
    (Sparse.constant (0 : Purelib.Data.Gaussian.Basic.Canonical)).terms) = false
  cbv

end TestPurelib.Approximation.Gaussian.ExpressionRebinding
