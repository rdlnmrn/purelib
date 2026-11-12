module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Checked

/-! # Reuse of actual successful bank endpoint checks without key injectivity

The selected first-match owners and their already paid common refinements
supply the same original cell admission even when the bank repeats a key.
No repeated-key root agreement is inferred merely from coordinate labels.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

namespace Checked

variable {prepared : PreparedParent patch count floor covered targets}
    {bank : Vertex.Bank parameter targets.endpoint} {rootStage : Nat}

/-- Complete an already ready original endpoint pair using its SAME selected Commons, lookups and admission.

The existing common-root branches derive the two operational query
comparisons. Any other Found at that exact bank key retains the SAME first
selected entry by Found.original_eq. No bank Distinct, new refinement,
new lookup or numerical admission factory is needed.
-/
def completeReady : (checked : Checked prepared bank rootStage) → checked.Ready → Completion checked
  | ⟨⟨.found first, .ready firstCommon _, _⟩, ⟨.found last, .ready lastCommon _, _⟩, _⟩, _ =>
      let firstQuery := prepared.firstQueryEquivalent.trans (RootBranch.ofCommonRefinement firstCommon).equivalent
      let lastQuery := prepared.lastQueryEquivalent.trans (RootBranch.ofCommonRefinement lastCommon).equivalent
      let firstToFound := fun (found : Vertex.Bank.Found bank (startPoint parent)) =>
        NamedEquivalent.transport rfl
          (congrArg (fun vertex : Vertex parameter (startPoint parent) =>
            vertex.sample.certificate.value.name) (first.original_eq found)) firstQuery
      let lastToFound := fun (found : Vertex.Bank.Found bank (finishPoint parent)) =>
        NamedEquivalent.transport rfl
          (congrArg (fun vertex : Vertex parameter (finishPoint parent) =>
            vertex.sample.certificate.value.name) (last.original_eq found)) lastQuery
      ⟨firstToFound, lastToFound, PUnit.unit⟩
  | ⟨⟨.absent _, _, _⟩, _, _⟩, ready => False.elim ready.1
  | ⟨⟨.found _, .inconclusive _ _ _ _, _⟩, _, _⟩, ready => False.elim ready.1
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.absent _, _, _⟩, _⟩, ready => False.elim ready.2
  | ⟨⟨.found _, .ready _ _, _⟩, ⟨.found _, .inconclusive _ _ _ _, _⟩, _⟩, ready => False.elim ready.2

/-- Completion from readiness returns the SAME original already materialized admission cache. -/
theorem completeReady_admission (checked : Checked prepared bank rootStage) (ready : checked.Ready) :
    Completion.admission checked (completeReady checked ready) = checked.admission ready :=
  Completion.admission_eq_of_ready checked (completeReady checked ready) ready

end Checked

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
