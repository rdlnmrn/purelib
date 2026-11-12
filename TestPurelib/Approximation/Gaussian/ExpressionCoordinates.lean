module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Coordinates
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Riemann.RootContinuation.SquareRootSidecar

/-!
# Pair coordinates retain the original expression and root owner

A linear expression reads its two rational coordinates at the same supplied
generator. The original compilation and entire annotated binding cache remain
the retained source of the inspection, including either isolated root sheet.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionCoordinates

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Multivariate
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Acquisition

-- Keep the certified cache boundary opaque while computing only coefficient data.
attribute [local cbv_opaque] Provenance.inspect Provenance.Inspection.scalar

/-- The original linear expression with two exact rational coefficients. -/
private def expression : Expr 1 := .add (.rational 1) (.mul (.rational 2) (.atom 0))

/-- Retain the actual supplied generator and its full original root sidecar. -/
private def environment (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    Fin 1 → Annotated := fun _ => ⟨generator, some (.squareRoot sidecar)⟩

/-- Read the cached pair's two actual rational fields. -/
private def fields {parameter : Rational} : Option (Purelib.Algebra.Quadratic.Pair Rational parameter) →
    Option (Rational × Rational)
  | none => none
  | some value => some (value.re, value.im)

/-- The same original generator has the exact two coordinates of the retained linear expression. -/
private theorem coordinates (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) :
    let normalized := expression.normalize (environment generator sidecar)
    let index : Fin normalized.bindings.length := ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩
    fields (normalized.inspectPair index 2).result.value? = some (1, 2) := by
  dsimp only
  unfold Normalized.inspectPair
  rewrite [Gaussian.Normalized.inspectPair_value]
  have scalarNone := Provenance.inspect_root_nonsquare sidecar 2 parameter_eq
    (by decide +kernel) (by decide +kernel)
  let bindings := (expression.retain (environment generator sidecar)).bindings
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  generalize cacheEq : Binding.inspect bindings = cache
  have cachedNone : (cache.get bindings (⟨0, by change 0 < 1; decide⟩ : Fin bindings.length)).scalar = none := by
    rewrite [← cacheEq]
    exact scalarNone
  change fields (Gaussian.Normalized.pairValue
    (Sparse.add (Sparse.constant 1) (Sparse.mul (Sparse.constant 2)
      (Binding.coefficients bindings cache (.atom 0) (by exact Or.inl rfl))))
    (⟨0, by decide⟩ : Fin 1) 2) = _
  unfold Binding.coefficients
  rewrite [Binding.locate_zero (.atom 0) bindings (Or.inl rfl) (by change 0 < 1; exact Nat.zero_lt_succ 0) (by rfl)]
  rewrite [Binding.coefficientsAt_nonscalar bindings cache _ cachedNone]
  change fields (Gaussian.Normalized.pairValue
    (Sparse.add (Sparse.constant 1) (Sparse.mul (Sparse.constant 2)
      (Sparse.atom (⟨0, by decide⟩ : Fin 1)))) (⟨0, by decide⟩ : Fin 1) 2) = some (1, 2)
  decide +kernel

example (sheet : Fin 2) :
    let retained := SquareRootSidecar.isolated 2 sheet
    let normalized := expression.normalize (environment retained.1 retained.2)
    let index : Fin normalized.bindings.length := ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩
    fields (normalized.inspectPair index 2).result.value? = some (1, 2) :=
  let retained := SquareRootSidecar.isolated 2 sheet
  coordinates retained.1 retained.2 (SquareRootSidecar.isolated_parameter 2 sheet)

example (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    let normalized := expression.normalize (environment generator sidecar)
    let index : Fin normalized.bindings.length := ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩
    (normalized.inspectPair index 2).source.compiled = normalized.compiled := rfl

example (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    let normalized := expression.normalize (environment generator sidecar)
    let index : Fin normalized.bindings.length := ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩
    (normalized.inspectPair index 2).source.bindings = normalized.bindings := rfl

end TestPurelib.Approximation.Gaussian.ExpressionCoordinates
