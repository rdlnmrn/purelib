module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! Transfer the original parent-chain order to the actual evaluated source
entries by position, preserving repeated payloads and complete coverage. -/
section

open Purelib.Data.List

open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder

/-- The paired evaluation retains exactly as many entries as the original parent cache. -/
private theorem retained_length (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) :
    evaluated.retained.length = occurrence.compared.entered.cache.parents.length := by
  have equal := congrArg List.length
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated)
  rw [Map.length_map] at equal
  exact equal

/-- Transport a retained source occurrence index to the identical position in the original parent cache. -/
private def cacheIndex (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (index : Fin evaluated.retained.length) : Fin occurrence.compared.entered.cache.parents.length :=
  ⟨index.val, index.isLt.trans_eq (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.retained_length
    evaluated)⟩

/-- Reading the transported cache index gives exactly the original parent of the retained source entry. -/
private theorem cacheIndex_read (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (index : Fin evaluated.retained.length) :
    Purelib.Riemann.Integration.PreparedParentSplitSelection.parentAt occurrence.compared.entered.cache.parents
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated index) =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated index).plan.parent :=
  Integration.PreparedParentSplitSelection.mapped_read evaluated.retained
    (fun entry => entry.plan.parent)
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated) index _

/-- Earlier retained source indices finish before later indices start under an ordered parent projection. -/
theorem indexed_parents_separated (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      project (parent.edge.point 0) ≤ project (parent.edge.point 1))
    (first last : Fin evaluated.retained.length) (before : first.val < last.val) :
    project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      first).plan.parent.edge.point 1) ≤
      project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        last).plan.parent.edge.point 0) := by
  have bound := Integration.PreparedParentAxisLocation.ParentCache.parents_separated occurrence.compared.entered.cache
    project ordered
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated first)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated last) before
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read] at bound
  exact bound

/-- Distinct source indices with coincident endpoints are consecutive;
positive-width parent intervals cannot be silently skipped by grouping. -/
theorem indexed_parents_no_skip (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      project (parent.edge.point 0) < project (parent.edge.point 1))
    (first last : Fin evaluated.retained.length) (before : first.val < last.val)
    (joint : project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      first).plan.parent.edge.point 1) =
      project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        last).plan.parent.edge.point 0)) : last.val = first.val + 1 := by
  apply Integration.PreparedParentAxisLocation.ParentCache.parents_no_skip occurrence.compared.entered.cache project
    ordered
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated first)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated last) before
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read]
  exact joint

/-- A positive-width retained parent beginning at the original occurrence start has index zero. -/
theorem indexed_parent_at_start (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      project (parent.edge.point 0) < project (parent.edge.point 1))
    (index : Fin evaluated.retained.length)
    (endpoint : project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent.edge.point 0) = project occurrence.start) :
    index.val = 0 := by
  apply Integration.PreparedParentAxisLocation.ParentCache.parent_at_start occurrence.compared.entered.cache project
    ordered (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated index)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read]
  exact endpoint

/-- A positive-width retained parent ending at the original occurrence finish is the last retained source index. -/
theorem indexed_parent_at_finish (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate)
    (ordered : ∀ parent ∈ occurrence.compared.entered.cache.parents,
      project (parent.edge.point 0) < project (parent.edge.point 1))
    (index : Fin evaluated.retained.length)
    (endpoint : project ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent.edge.point 1) = project occurrence.finish) :
    index.val + 1 = evaluated.retained.length := by
  have last : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated index).val + 1 =
    occurrence.compared.entered.cache.parents.length := by
    apply Integration.PreparedParentAxisLocation.ParentCache.parent_at_finish occurrence.compared.entered.cache project
      ordered (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex evaluated index)
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.cacheIndex_read]
    exact endpoint
  exact last.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder.retained_length evaluated).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedParentOrder

end
