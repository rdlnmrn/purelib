module
meta import Purelib.Elab.ConstructiveInjectivity
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Riemann.Integration.PreparedParentSplitSelection
public import Purelib.Riemann.Integration.PreparedParentAxisLocation
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches

public section

/-! The paired source evaluation and original splitting spine have the same
parent order. Select their common occurrence by index, preserving duplicates. -/
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

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits

/-- Read one original paired source entry with its retained finite index bound. -/
@[expose] def indexedEntry (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (index : Fin evaluated.retained.length) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine :=
  evaluated.retained[index.val]'index.isLt

/-- The indexed paired source entry belongs to the same retained evaluation list. -/
theorem indexedEntry_member (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (index : Fin evaluated.retained.length) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated index ∈ evaluated.retained
      := List.getElem_mem _

/-- Select the original parent splitting certificate corresponding to a retained paired source index. -/
@[expose] def sourceSplit (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) (index : Fin evaluated.retained.length) :
    Integration.PreparedParentSplitSelection.Selected occurrence.compared.entered.mesh.splits
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated index).plan.parent :=
  Integration.PreparedParentSplitSelection.selectMapped occurrence.compared.entered.mesh.splits evaluated.retained (fun
    entry => entry.plan.parent)
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated) index

set_option genInjectivity false in
/-- An original paired source occurrence crossing the supplied half-open projected axis interval.

Its finite index retains duplicates and identifies the parent whose endpoint bounds contain the query. -/
structure SourceAxisLocation (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate) (query :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original occurrence index in the retained paired source evaluation. -/ index : Fin evaluated.retained.length
  /-- The query lies at or above this original parent's projected initial endpoint. -/ lower : project
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
    index).plan.parent.edge.point 0) ≤ query
  /-- The query lies strictly below this original parent's projected final endpoint. -/ upper : query < project
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
    index).plan.parent.edge.point 1)

constructive_injectivity SourceAxisLocation

/-- Find the paired source occurrence crossing an interior axis query. The
original endpoint chain proves search success; no successful scan is assumed. -/
@[expose] def locateSourceAxis (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (project : Normalization.InverseRootPolynomial.Gaussian → Normalization.InverseRootPolynomial.Coordinate) (query :
      Normalization.InverseRootPolynomial.Coordinate)
    (lower : project occurrence.start ≤ query) (upper : query < project occurrence.finish) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.SourceAxisLocation evaluated project query := by
  let located := Integration.PreparedParentAxisLocation.ParentCache.locateAxis occurrence.compared.entered.cache project
    query lower upper
  have lengthEq : evaluated.retained.length = occurrence.compared.entered.cache.parents.length := by
    have equal := congrArg List.length
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated)
    rw [Map.length_map] at equal
    exact equal
  let index := Fin.cast lengthEq.symm located.index
  have parentEq : Integration.PreparedParentSplitSelection.parentAt
      occurrence.compared.entered.cache.parents located.index =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated index).plan.parent :=
    Integration.PreparedParentSplitSelection.mapped_read evaluated.retained
      (fun entry => entry.plan.parent)
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated) index
        located.index.isLt
  refine ⟨index, ?_, ?_⟩
  · rw [← parentEq]
    exact located.lower
  · rw [← parentEq]
    exact located.upper

/-- The mesh location now consumes an index into the actual paired source
evaluation. The split and its occurrence certificate are selected internally. -/
@[expose] def locateIndexedSourceInterval
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {previous :
        Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    (selected : SourceCuts prepared previous)
    (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
      Normalization.InverseRootPolynomial.Coordinate}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation
      plan sample otherSample fine) (index : Fin evaluated.retained.length)
    (vertical : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (present : physical ∈ Rectangle.SourceIntervals.axisIntervals ((request.entries.get sheet).meshes.entries.get
      position) vertical)
    (range : Rectangle.Partition.PreparedAxisPartitions.Interval) (within : 0 ≤ range.lower ∧ range.upper ≤ 1)
    (correspondence : Rectangle.SourceIntervals.AxisCorrespondence vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        index).plan.parent.edge.point 0) ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry
        evaluated index).plan.parent.edge.point 1) range physical) :
    Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated index).split range :=
  selected.locateInterval request sheet position member
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated index).split
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated index).member
    vertical physical present range within correspondence

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits

end
