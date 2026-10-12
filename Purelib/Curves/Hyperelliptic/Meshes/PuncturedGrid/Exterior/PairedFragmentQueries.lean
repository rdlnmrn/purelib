module
import Purelib.Algebra.Group.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

public section

/-! Fine fragment queries consume the actual shared aligned values and the
same cached source primitives as the paired cap-area evaluation. Containment
and root transport are inherited from the occurrence and fragment caches. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries

open Purelib.Algebra

open Purelib

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

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

/-- One original paired parent entry retained by the supplied source plan and both cap samples. -/
@[expose] def SourceEntry (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  occurrence other target minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox) (fine : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry plan.parents sample otherSample fine

/-- A rectangular segment fragment on the selected parent in the original entered domain geometry. -/
@[expose] def Fragment (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) :=
  Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry
    (entry.plan.parent.edge.point 0) (entry.plan.parent.edge.point 1)

/-- A retained paired source entry has its original parent in the occurrence's cached parent list. -/
private theorem parent_member (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained) :
    entry.plan.parent ∈ occurrence.compared.entered.cache.parents :=
  open Purelib in Eq.mp (congrArg (fun parents => entry.plan.parent ∈ parents)
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated))
    (Data.List.Map.mem_map_of_mem (f := fun value => value.plan.parent) member)

/-- The first differential's retained fragment-query error density at the supplied face stage. -/
@[expose] def firstQueryDensity (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (faceIndex : Nat) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity occurrence.compared.entered.bounds
    piece.column piece.row entry.source.localRequest faceIndex

/-- Bound the first aligned grid increment's error against its original cached source primitive.

Both parameters lie in the same retained fragment; the bound uses its first query density and actual geometric
displacement. -/
theorem first_fragment_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {faceIndex : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives occurrence.compared.entered.domain
      differential faceIndex)
    (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Data.Gaussian.Norm.Basic.normSq ((data.anchors.alignedValue data.offsets piece.column piece.row
      (entry.plan.parent.edge.point last) -
        data.anchors.alignedValue data.offsets piece.column piece.row (entry.plan.parent.edge.point first)) -
      (entry.certified.source.primitive.value.eval (entry.plan.parent.edge.point last) -
        entry.certified.source.primitive.value.eval (entry.plan.parent.edge.point first))) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.firstQueryDensity entry piece faceIndex *
        Data.Gaussian.Norm.Basic.normSq (entry.plan.parent.edge.point last - entry.plan.parent.edge.point first) :=
        by
  have reached := occurrence.compared.entered.reached entry.plan.parent
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.parent_member evaluated entry member)
  have bounded := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.query_increment_le
    occurrence.compared.entered.bounds (parent := entry.plan.parent)
    (count := genus) (target := plan.parents.allowance) piece data.primitives reached
    entry.source.localRequest first last firstInside lastInside
  rw [entry.source_eq] at bounded
  dsimp only [-eq_self, -iff_self, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.firstQueryDensity]
  simpa only [Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue, Group.add_sub_add_left_eq_sub] using
    bounded

/-- The recast second differential's retained fragment-query error density at the supplied face stage. -/
@[expose] def secondQueryDensity (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (faceIndex : Nat) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity (occurrence.recastComparison
    other).entered.bounds
    piece.column piece.row entry.otherSource.localRequest faceIndex

/-- Bound the second aligned grid increment's error against its retained recast source primitive.

Recasting preserves the original parent points and fragment while the second query density pays the geometric
displacement. -/
theorem second_fragment_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {faceIndex : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives (occurrence.recastComparison
      other).entered.domain other faceIndex)
    (first last : Normalization.InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Data.Gaussian.Norm.Basic.normSq ((data.anchors.alignedValue data.offsets piece.column piece.row
      (entry.plan.parent.edge.point last) -
        data.anchors.alignedValue data.offsets piece.column piece.row (entry.plan.parent.edge.point first)) -
      (entry.certified.otherSource.primitive.value.eval (entry.plan.parent.edge.point last) -
        entry.certified.otherSource.primitive.value.eval (entry.plan.parent.edge.point first))) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.secondQueryDensity entry piece faceIndex *
        Data.Gaussian.Norm.Basic.normSq (entry.plan.parent.edge.point last - entry.plan.parent.edge.point first) :=
        open Purelib in by
  have inParents : Integration.PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent ∈
      occurrence.compared.entered.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge other) :=
    Data.List.Map.mem_map_of_mem (f := Integration.PreparedEdgeRecasting.recastCenteredEdge other)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.parent_member evaluated entry member)
  have reached := (occurrence.recastComparison other).entered.reached _ inParents
  have bounded := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.query_increment_le
    (occurrence.recastComparison other).entered.bounds
    (parent := Integration.PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent) (count := genus) (target :=
      plan.parents.allowance)
    piece data.primitives reached
    entry.otherSource.localRequest first last firstInside lastInside
  rw [entry.otherSource_eq] at bounded
  have point_eq (parameter : Normalization.InverseRootPolynomial.Coordinate) :
      (Integration.PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent).edge.point parameter =
        entry.plan.parent.edge.point parameter := rfl
  rw [point_eq first, point_eq last] at bounded
  dsimp only [-eq_self, -iff_self, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.secondQueryDensity]
  simpa only [Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue, Group.add_sub_add_left_eq_sub] using
    bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries

end
