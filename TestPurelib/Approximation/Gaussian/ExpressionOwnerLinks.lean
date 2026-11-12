module

import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compilation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
import Purelib.Approximation.Gaussian.Acquisition.Expression.Realization
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Realization
meta import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
meta import Purelib.Approximation.Gaussian.Provenance.Quadratic
meta import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Data.Gaussian.Cast

/-!
# Explicit common-owner links preserve distinct original input keys

Two original channels with coordinates `1+r` and `3+r` have separate atom
indices. Typed certificates at their one retained realization supply their
actual coordinate links. Their product receives coordinates `5+4*r` while
retaining both original keys and the exact supplied certificates.
-/

namespace TestPurelib.Approximation.Gaussian.ExpressionOwnerLinks

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation

/-- Verify both distinct original source occurrences and their supplied cached coordinate certificates. -/
private meta def checkLinks : IO Unit := do
  for sheet in ([0, 1] : List (Fin 2)) do
    let root := SquareRootSidecar.isolated 2 sheet
    let owner := Realization.rational 2 root.1
      (Realization.rootEquation root.2 2 (SquareRootSidecar.isolated_parameter 2 sheet))
      (Square.inspect 2) (by decide +kernel)
    let first := (owner.retain (⟨1, 1⟩ : Pair Rational (-2))).sidecar
    let second := (owner.retain (⟨3, 1⟩ : Pair Rational (-2))).sidecar
    let environment : Fin 2 → Annotated :=
      Fin.cases (Annotated.opaque first.source) (fun _ => Annotated.opaque second.source)
    let expression : Expr 2 := .mul (.atom 0) (.atom 1)
    let normalized := expression.normalize environment
    let basis := Binding.read normalized.bindings ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩
    let firstSource : Realization.Sidecar owner first.source := first.transport (by
      rewrite [first.source_eq]
      exact NamedEquivalent.refl _)
    let secondSource : Realization.Sidecar owner second.source := second.transport (by
      rewrite [second.source_eq]
      exact NamedEquivalent.refl _)
    have basisEvidence : Realization.Sidecar owner basis.channel := by
      change Realization.Sidecar owner first.source
      exact firstSource
    let supplied : (index : Fin normalized.bindings.length) →
        Option (Realization.Sidecar owner (Binding.channels normalized.bindings index)) := by
      intro index
      change Fin 2 at index
      refine Fin.cases ?_ ?_ index
      · change Option (Realization.Sidecar owner first.source)
        exact some firstSource
      · intro tail
        refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail
        change Option (Realization.Sidecar owner second.source)
        exact some secondSource
    let links := Binding.RealizationLinks.ofEvidence owner normalized.bindings supplied
    let checked := normalized.inspectRealizationWith owner (fun _ => rfl) basis basisEvidence links
    match checked.outcome with
    | .ready _ _ result _ =>
        unless result.value.re = 5 ∧ result.value.im = 4 do
          throw (IO.userError "explicit original source links produced incorrect product coordinates")
    | .unresolved _ => throw (IO.userError "complete original common-owner evidence remained unresolved")
    unless (Binding.read normalized.bindings ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩).leaf = .atom 0 ∧
        (Binding.read normalized.bindings ⟨1, by change 1 < 2; exact Nat.lt_succ_self 1⟩).leaf = .atom 1 do
      throw (IO.userError "common-owner interpretation replaced the two original atom keys")
    match checked.links.get normalized.bindings ⟨1, by change 1 < 2; exact Nat.lt_succ_self 1⟩ with
    | some retained =>
        unless retained.value.re = 3 ∧ retained.value.im = 1 do
          throw (IO.userError "the returned attempt did not retain the actual supplied second source coordinates")
    | none => throw (IO.userError "the supplied original second occurrence was discarded")

/-- A checked common-owner result attaches original-source provenance using its original supplied root admission. -/
private meta def checkAnnotation : IO Unit := do
  for sheet in ([0, 1] : List (Fin 2)) do
    let root := SquareRootSidecar.isolated 2 sheet
    let rootEnvironment : Fin 1 → Annotated := fun _ => ⟨root.1, some (.squareRoot root.2)⟩
    let input := (Expr.add (.rational 1) (.atom 0)).compile rootEnvironment
    match input.provenance with
    | some (.quadratic original) =>
        let owner := original.admission.realization
        let first := original.evidence
        let scalar := Realization.Sidecar.constant owner 2 2 (by
          rewrite [original.admission.coefficient_eq]
          rfl)
        let second := first.add scalar
        let environment : Fin 2 → Annotated := fun index =>
          if index.val = 0 then Annotated.opaque input.channel else Annotated.opaque second.source
        let normalized := (Expr.mul (.atom 0) (.atom 1)).normalize environment
        let basis := Binding.read normalized.bindings ⟨0, by change 0 < 2; exact Nat.zero_lt_succ 1⟩
        let secondSource : Realization.Sidecar owner second.source := second.transport (by
          rewrite [second.source_eq]
          exact NamedEquivalent.refl _)
        let supplied : (index : Fin normalized.bindings.length) →
            Option (Realization.Sidecar owner (Binding.channels normalized.bindings index)) := by
          intro index
          change Fin 2 at index
          refine Fin.cases ?_ ?_ index
          · change Option (Realization.Sidecar owner input.channel)
            exact some first
          · intro tail
            refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail
            change Option (Realization.Sidecar owner second.source)
            exact some secondSource
        let links := Binding.RealizationLinks.ofEvidence owner normalized.bindings supplied
        let origin : Purelib.Approximation.Gaussian.Provenance.Quadratic.Sidecar basis.channel := by
          have entries : normalized.bindings =
              [⟨.atom 0, environment 0, rfl⟩, ⟨.atom 1, environment 1, rfl⟩] := by
            dsimp only [normalized, Expr.normalize, Compiled.normalize]
            rewrite [Expr.retain_mul, dif_neg (by decide :
              (Expr.atom (0 : Fin 2) : Expr 2) ≠ Expr.atom 1)]
            simp only [Expr.retain_atom, Compiled.bindings, Construction.bindings, -eq_self, -iff_self]
            rfl
          have atZero : (bound : 0 < normalized.bindings.length) →
              Purelib.Approximation.Gaussian.Provenance.Quadratic.Sidecar
                (Binding.read normalized.bindings ⟨0, bound⟩).channel := by
            rewrite [entries]
            intro bound
            dsimp only [Binding.read, Binding.channel]
            simp only [List.getElem_cons_zero, -eq_self, -iff_self]
            dsimp only [environment, Annotated.opaque]
            rewrite [if_pos (show (0 : Fin 2).val = 0 from rfl)]
            exact original
          exact atZero (by change 0 < 2; exact Nat.zero_lt_succ 1)
        let checked := normalized.inspectRealizationWith origin.admission.realization origin.admission.coefficient_eq
          basis origin.evidence links
        let annotated := Normalized.RealizationCheck.annotate (normalized := normalized) (basis := basis) origin checked
        match annotated.provenance with
        | some (.quadratic result) =>
            unless result.coordinates.re = 5 ∧ result.coordinates.im = 4 ∧ result.admission.parameter = 2 do
              throw (IO.userError "common-owner annotation changed its original coordinates or root admission")
        | _ => throw (IO.userError "checked common-owner interpretation did not attach original-source evidence")
    | _ => throw (IO.userError "the original input did not retain its admitted root owner")

#eval checkAnnotation

#eval checkLinks

end TestPurelib.Approximation.Gaussian.ExpressionOwnerLinks
