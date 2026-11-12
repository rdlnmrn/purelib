module

import Purelib.Approximation.Gaussian.Acquisition.Expression.PowerReduction
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Approximation.Gaussian.Provenance.Power

/-!
# Reduction preserves original acquisition owners

The source is an arbitrary retained generator carrying its supplied equation.
Opaque absence remains explicit. A retained root sidecar supplies its original
equation without constructing another isolated root or identifying sheets.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionPowerReduction

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Polynomial.Multivariate

-- Keep the certified cache boundary opaque while computing only coefficient data.
attribute [local cbv_opaque] Provenance.inspect Provenance.Inspection.scalar

/-- Retain the actual original generator without automatically supplied provenance. -/
private def environment (generator : CoherentNamed) : Fin 1 → Annotated := fun _ => Annotated.opaque generator

/-- The original product of the generator's two shifted expressions. -/
private def expression : Expr 1 :=
  .mul (.add (.atom 0) (.rational 1)) (.sub (.atom 0) (.rational 1))

/-- The coefficient-only product at the original first generator among two retained occurrences. -/
private def productForm : Sparse Purelib.Data.Gaussian.Basic.Canonical 2 :=
  Sparse.mul (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 2)) (Sparse.constant 1))
    (Sparse.sub (Sparse.atom (⟨0, by decide⟩ : Fin 2)) (Sparse.constant 1))

/-- The retained product has two different formal monomials before its supplied equation is used. -/
private theorem product_nonconstant : productForm.constantView.Nonconstant := by
  exact Sparse.constantView_nonconstant_of_multiple productForm
    ⟨.cons 0 (.cons 0 .nil), -1⟩ ⟨.cons 2 (.cons 0 .nil), 1⟩ [] (by decide +kernel)

/-- The normalizer's original first generator position has its retained literal channel. -/
private theorem first_channel (generator : CoherentNamed) :
    Binding.channels (expression.normalize (environment generator)).bindings
      ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩ = generator := rfl

/-- Opaque input coefficients retain their original atom while numerical comparisons remain opaque. -/
private theorem opaque_form (generator : CoherentNamed) :
    (expression.normalize (environment generator)).polynomial.form = productForm := by
  let bindings := (expression.retain (environment generator)).bindings
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  generalize cacheEq : Binding.inspect bindings = cache
  have cachedNone : (cache.get bindings (⟨0, by change 0 < 2; decide⟩ : Fin bindings.length)).scalar = none := by
    rewrite [← cacheEq]
    exact Provenance.inspect_opaque_scalar generator
  change Sparse.mul
      (Sparse.add (Binding.coefficients bindings cache (.atom 0) (by exact Or.inl rfl)) (Sparse.constant 1))
      (Sparse.sub (Binding.coefficients bindings cache (.atom 0) (by exact Or.inl rfl)) (Sparse.constant 1)) = _
  unfold Binding.coefficients
  rewrite [Binding.locate_zero (.atom 0) bindings (Or.inl rfl) (by change 0 < 2; exact Nat.zero_lt_succ 1) (by rfl)]
  rewrite [Binding.coefficientsAt_nonscalar bindings cache _ cachedNone]
  rfl

example (generator : CoherentNamed) (relation : PowerIdentity generator 2 2) :
    RationalSidecar (expression.normalize (environment generator)).compiled.annotation.channel := by
  let normalized := expression.normalize (environment generator)
  let index : Fin normalized.bindings.length := ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩
  have retained : PowerIdentity (Binding.channels normalized.bindings index) 2 2 := by
    rewrite [first_channel generator]
    exact relation
  let reduced := normalized.reduceAt index 2 2 retained
  exact reduced.polynomial.rational 1 (by
    change (normalized.polynomial.reduceAt index 2 2 retained).form.terms = _
    rewrite [Gaussian.Normalized.reduceAt_form, opaque_form generator]
    change (productForm.reduceAt (⟨0, by decide⟩ : Fin 2) 2 2).terms =
      (Sparse.constant 1).terms
    decide +kernel)

example (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    Binding.PowerEvidence (⟨.atom (0 : Fin 1), ⟨generator, some (.squareRoot sidecar)⟩, rfl⟩ :
      Binding (fun _ => ⟨generator, some (.squareRoot sidecar)⟩)) :=
  Binding.powerEvidence _

/-- The original generator environment with its actual supplied root sidecar. -/
private def suppliedEnvironment (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    Fin 1 → Annotated := fun _ => ⟨generator, some (.squareRoot sidecar)⟩

/-- Nonsquare source evidence keeps the retained generator as the original formal atom. -/
private theorem supplied_normal_form (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) :
    (expression.normalize (suppliedEnvironment generator sidecar)).polynomial.form = productForm := by
  have scalarNone := Provenance.inspect_root_nonsquare sidecar 2 parameter_eq
    (by decide +kernel) (by decide +kernel)
  let bindings := (expression.retain (suppliedEnvironment generator sidecar)).bindings
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  generalize cacheEq : Binding.inspect bindings = cache
  have cachedNone : (cache.get bindings (⟨0, by change 0 < 2; decide⟩ : Fin bindings.length)).scalar = none := by
    rewrite [← cacheEq]
    exact scalarNone
  change Sparse.mul
      (Sparse.add
        (Binding.coefficients bindings cache (.atom 0) (by exact Or.inl rfl))
        (Sparse.constant 1))
      (Sparse.sub
        (Binding.coefficients bindings cache (.atom 0) (by exact Or.inl rfl))
        (Sparse.constant 1)) = _
  unfold Binding.coefficients
  rewrite [Binding.locate_zero (.atom 0) bindings (Or.inl rfl) (by change 0 < 2; exact Nat.zero_lt_succ 1) (by rfl)]
  rewrite [Binding.coefficientsAt_nonscalar bindings cache _ cachedNone]
  rfl

/-- Automatic retained-equation reduction reads the two original binding positions and yields one. -/
private theorem supplied_form (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) :
    (expression.normalize (suppliedEnvironment generator sidecar)).reduceRetained.polynomial.form.terms =
      (Sparse.constant 1).terms := by
  let normalized := expression.normalize (suppliedEnvironment generator sidecar)
  have firstBound : 1 ≤ normalized.bindings.length := by
    change 1 ≤ 2
    exact Nat.succ_le_succ (Nat.zero_le 1)
  have secondBound : 2 ≤ normalized.bindings.length := by
    change 2 ≤ 2
    exact Nat.le_refl 2
  have first := Binding.powerEvidence_root
    (Binding.read normalized.bindings ⟨0, Nat.lt_of_lt_of_le (Nat.lt_succ_self 0) firstBound⟩) sidecar (by rfl)
  have second := Binding.powerEvidence_root
    (Binding.read normalized.bindings ⟨1, Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) secondBound⟩) sidecar (by rfl)
  have firstStep := Binding.reducePowers_known_form normalized.bindings normalized.polynomial 0 firstBound
    2 (by decide) sidecar.parameter (PowerIdentity.ofSquare sidecar.square) first
  have secondStep := Binding.reducePowers_known_form normalized.bindings normalized.polynomial 1 secondBound
    2 (by decide) sidecar.parameter (PowerIdentity.ofSquare sidecar.square) second
  unfold Normalized.reduceRetained
  change (Binding.reducePowers normalized.bindings normalized.polynomial 2 secondBound).form.terms = _
  rewrite [secondStep, firstStep, parameter_eq]
  change ((normalized.polynomial.form.reduceAt (⟨0, by decide⟩ : Fin 2) 2 2).reduceAt
    (⟨1, by decide⟩ : Fin 2) 2 2).terms = _
  rewrite [supplied_normal_form generator sidecar parameter_eq]
  change ((productForm.reduceAt (⟨0, by decide⟩ : Fin 2) 2 2).reduceAt
    (⟨1, by decide⟩ : Fin 2) 2 2).terms = (Sparse.constant 1).terms
  decide +kernel

/-- The actual compiler infers one from supplied generator evidence at its unchanged original expression. -/
private theorem supplied_value (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) :
    (expression.compile (suppliedEnvironment generator sidecar)).rationalValue = some 1 := by
  apply Expr.compile_reduced_value
  · rfl
  · have same := supplied_normal_form generator sidecar parameter_eq
    exact Normalized.nonconstant_of_form (expression.normalize (suppliedEnvironment generator sidecar))
      productForm same product_nonconstant
  · exact supplied_form generator sidecar parameter_eq

example (sheet : Fin 2) :
    let retained := SquareRootSidecar.isolated 2 sheet
    (expression.compile (suppliedEnvironment retained.1 retained.2)).rationalValue = some 1 :=
  let retained := SquareRootSidecar.isolated 2 sheet
  supplied_value retained.1 retained.2 (SquareRootSidecar.isolated_parameter 2 sheet)

example (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) :
    (expression.compile (suppliedEnvironment generator sidecar)).channel =
      expression.denote (suppliedEnvironment generator sidecar) :=
  expression.compile_channel (suppliedEnvironment generator sidecar)

end TestPurelib.Approximation.Gaussian.ExpressionPowerReduction
