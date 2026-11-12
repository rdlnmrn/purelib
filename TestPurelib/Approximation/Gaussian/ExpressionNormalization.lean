module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Polynomial.Multivariate.Sparse
import Purelib.Data.Gaussian.Basic

/-!
# Retained expression normalization regressions

The source channels are opaque and arbitrary. Exact coefficient checks exercise
the complete expression compiler and normalizer, rather than supplying a ring
identity certificate. Root-free tests also check zero-arity numerical readback.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionNormalization

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate (Sparse)

/-- A two-atom environment retaining the original arbitrary opaque input channels. -/
private def environment (first second : CoherentNamed) : Fin 2 → Annotated :=
  Fin.cases (Annotated.opaque first) (fun _ => Annotated.opaque second)

/-- The commuted-cancellation expression over the two original atom indices. -/
private def commuted : Expr 2 :=
  .sub (.add (.atom ⟨0, by decide⟩) (.atom ⟨1, by decide⟩))
    (.add (.atom ⟨1, by decide⟩) (.atom ⟨0, by decide⟩))

/-- The expanded one-variable polynomial identity over the original first atom. -/
private def expanded : Expr 2 :=
  .sub (.sub (.mul (.add (.atom ⟨0, by decide⟩) (.rational 1))
      (.add (.atom ⟨0, by decide⟩) (.rational 1)))
      (.mul (.atom ⟨0, by decide⟩) (.atom ⟨0, by decide⟩)))
    (.mul (.rational 2) (.atom ⟨0, by decide⟩))

/-- The retained compiler and normalizer cancel commuted sums for arbitrary opaque channels. -/
private theorem commuted_form (first second : CoherentNamed) :
    (commuted.normalize (environment first second)).polynomial.form.terms = [] := by
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  dsimp only [Compiled.bindings]
  change (Sparse.sub
    (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 4))
      (Sparse.atom (⟨1, by decide⟩ : Fin 4)))
    (Sparse.add (Sparse.atom (⟨1, by decide⟩ : Fin 4))
      (Sparse.atom (⟨0, by decide⟩ : Fin 4)))).terms = []
  decide +kernel

/-- The retained compiler and normalizer evaluate the expanded opaque identity to one. -/
private theorem expanded_form (first second : CoherentNamed) :
    (expanded.normalize (environment first second)).polynomial.form.terms =
      (Sparse.constant (1 : Canonical)).terms := by
  unfold Expr.normalize Compiled.normalize
  dsimp only
  rewrite [Construction.normalize_form]
  dsimp only [Compiled.bindings]
  change (Sparse.sub
    (Sparse.sub
      (Sparse.mul
        (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1))
        (Sparse.add (Sparse.atom (⟨0, by decide⟩ : Fin 3)) (Sparse.constant 1)))
      (Sparse.mul (Sparse.atom (⟨0, by decide⟩ : Fin 3))
        (Sparse.atom (⟨0, by decide⟩ : Fin 3))))
    (Sparse.mul (Sparse.constant 2) (Sparse.atom (⟨0, by decide⟩ : Fin 3)))).terms =
      (Sparse.constant (1 : Canonical)).terms
  decide +kernel

example (first second : CoherentNamed) :
    RationalSidecar (commuted.normalize (environment first second)).compiled.annotation.channel :=
  (commuted.normalize (environment first second)).polynomial.rational 0 (commuted_form first second)

example (first second : CoherentNamed) :
    RationalSidecar (expanded.normalize (environment first second)).compiled.annotation.channel :=
  (expanded.normalize (environment first second)).polynomial.rational 1 (expanded_form first second)

example (first second : CoherentNamed) :
    (commuted.compile (environment first second)).rationalValue = some 0 :=
  commuted.compile_inferred_value (environment first second) 0 (by rfl) (commuted_form first second)

example (first second : CoherentNamed) :
    (expanded.compile (environment first second)).rationalValue = some 1 :=
  expanded.compile_inferred_value (environment first second) 1 (by rfl) (expanded_form first second)

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (Provenance.inspect (Annotated.algebraic (original.pow 0))).scalar =
      some (RationalSidecar.exact 1) := by
  rw [Provenance.inspect_algebraic_scalar, original.pow_zero_scalar]

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel) :
    (Annotated.algebraic (original.pow 0)).rationalValue = none := rfl

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel)
    (fallback : Unit → Sparse Canonical 1) :
    (Annotated.algebraic (original.pow 0)).coefficientsWith fallback = Sparse.constant 1 := by
  unfold Annotated.coefficientsWith
  change (match (original.pow 0).scalar? with
    | some reading => Sparse.constant reading.value
    | none => fallback ()) = Sparse.constant 1
  rw [original.pow_zero_scalar]
  rfl

example {channel : CoherentNamed} (original : Algebraic.Sidecar channel)
    (missing : original.scalar? = none) :
    (Provenance.inspect (Annotated.algebraic original)).scalar = none :=
  (Provenance.inspect_algebraic_scalar original).trans missing

example (first second : CoherentNamed) :
    (commuted.normalize (environment first second)).compiled.annotation.channel =
      commuted.denote (environment first second) :=
  (commuted.normalize (environment first second)).original_eq

example :
    ((Expr.rational (⟨0, 1⟩ : Canonical) : Expr 0).normalize
      Fin.elim0).compiled.annotation.channel =
      (Expr.rational ⟨0, 1⟩ : Expr 0).denote Fin.elim0 :=
  ((Expr.rational ⟨0, 1⟩ : Expr 0).normalize Fin.elim0).original_eq

end TestPurelib.Approximation.Gaussian.ExpressionNormalization
