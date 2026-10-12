module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
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
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Tactic.Ring

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-! Conjugate energy comparison on the actual grid/source fragment values.
The retained parameter geometry and scalar query bounds are unchanged. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentArea

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
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

/-- The original retained source density is bounded by the common paired trace density. -/
private theorem source_le_trace (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry
  plan sample otherSample fine) (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment
  entry) (index : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity entry ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index := open
      Purelib.Data.Rat in by
  have extra : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index *
    entry.plan.parent.edge.pointMovement :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
    (Gaussian.Norm.Basic.normSq_nonneg (entry.plan.parent.edge.point 1 - entry.plan.parent.edge.point 0))
  have nonnegative := add_nonneg extra
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative entry)
  exact (le_add_of_nonneg_left extra).trans ((le_add_of_nonneg_right nonnegative).trans_eq (by
      unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity;
      ring1))

/-- Every intermediate sample is retained. The bound has no multiplicative
vertex count; coincident parameters and nonuniform subdivisions are allowed. -/
theorem conjugate_fragment_area_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData
      (parameters vertex))))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex)))) :
    Data.Gaussian.Norm.Basic.normSq (grid.centeredArea - source.centeredArea) ≤
      40 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError entry piece index *
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index *
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last count)))^2 := open Purelib.Data.Rat in by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total forward parameters]
  apply Path.WeightedPathComparison.Sample.weighted_full_comparison grid source
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
  · intro vertex
    rw [grid.centered_eq, source.centered_eq, ←
      Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub, ←
      Path.DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub]
    apply Path.ConjugateIncrementComparison.conjugateFirst_error
    have errors := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.paired_query_error evaluated entry
      member piece data otherData
      (parameters 0) (parameters vertex) (inside 0) (inside vertex)
    have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside vertex))
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside 0))
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
    exact ⟨errors.1.trans upper, errors.2.trans upper⟩
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    exact Path.ConjugateIncrementComparison.conjugateFirst_error
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.grid_increment_bound evaluated entry member piece
      data otherData _ _ (inside edge.castSucc) (inside edge.succ))
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    have bound := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_increment_bound entry piece _
      _ (inside edge.castSucc) (inside edge.succ)
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentArea.source_le_trace entry piece index)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (parameters edge.succ - parameters edge.castSucc))
    exact Path.ConjugateIncrementComparison.conjugateFirst_error ⟨bound.1.trans upper, bound.2.trans upper⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentArea
