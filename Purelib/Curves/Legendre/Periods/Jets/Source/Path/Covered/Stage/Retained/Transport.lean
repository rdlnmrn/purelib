module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Transport
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Entries
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Completed families retaining their actual selected completion

One actual canonical covered-stage completion supplies the genuine signed
geometric payment. At its selected stage the whole same Completed value is
transported exactly. Other stages materialize their own original attempt
once, then reuse the selected completion's root acquisitions and their own
actual ready Commons and numerical source caches.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Completed

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- Extend the same actual selected Completed value through the original canonical attempt family.

The selected branch retains the whole supplied object, including its old
attempt, acquisitions and original Stage. A different stage materializes
one original attempt before transporting the selected geometric payment.
No all-stage readiness premise or new root acquisition is required. The
initial selected completion and its actual covered-stage factory remain
necessary genuine inputs; they are not inferred from labels or closure.
-/
public def family
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (selected : Completed covered chain index floor rootStage)
    (factory : selected.1 = fromCovered covered chain index floor rootStage) : selected.1.CompletedFamily :=
  fun stage =>
    if equal : stage = index then
      ⟨Eq.mpr (congrArg (fun selectedIndex => Completed covered chain selectedIndex floor rootStage) equal) selected, by
        cases equal
        exact selected.1.attemptFamily_at.symm⟩
    else
      let current := selected.1.attemptFamily stage
      have currentFactory : current =
          ofPrepared covered chain (CellEndpoints.Targets.build chain.path stage) rfl
            (prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage)) rootStage :=
        selected.1.attemptFamily_other stage equal
      let completed := StageAttempt.Completion.ofCanonical covered chain selected.1 current factory
        currentFactory selected.2
      ⟨⟨current, completed⟩, rfl⟩

/-- The selected family branch retains the same entire original Completed cache, not only its attempt or sources. -/
public theorem family_at
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (selected : Completed covered chain index floor rootStage)
    (factory : selected.1 = fromCovered covered chain index floor rootStage) :
    (family covered chain selected factory index).val = selected := by
  unfold family
  rewrite [dif_pos rfl]
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Completed
