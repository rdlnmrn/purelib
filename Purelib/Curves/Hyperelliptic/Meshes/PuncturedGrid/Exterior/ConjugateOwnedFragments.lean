module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.OwnedPathComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentArea
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
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-! The retained owner requests pay conjugate energy on the actual owned
trace, including owner changes at repeated coordinates. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateOwnedFragments

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

/-- Bound the complete conjugate owned-fragment area against its original cached source sample.

The retained owner budget pays both actual reading changes, and the monotone fragment parameters retain the full
grid-to-source area error. -/
theorem conjugate_owned_fragment_area_bound (evaluated :
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
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData
      parameters)
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second vertex)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex)))) :
    Data.Gaussian.Norm.Basic.normSq (owned.centeredArea - source.centeredArea) ≤
      2 * (40 * budget.tolerance * (4 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity
        entry piece index + 3) *
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last count)) + allowance)^2 +
        40 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError entry piece index *
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index *
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0)
            (parameters (Fin.last count)))^2) := by
  let fixed := Periods.CenteredBilinearPath.Sample.build (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData (parameters
    vertex)))
  have densityNonnegative : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece
    index :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
        (Gaussian.Norm.Basic.normSq_nonneg (entry.plan.parent.edge.point 1 - entry.plan.parent.edge.point 0)))
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative entry))
  have ownerError := Path.OwnedPathComparison.LengthErrorBudget.reading_comparison budget owned fixed
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    densityNonnegative (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _ (ordered
      edge))
    (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst_error
      (show Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second vertex).sub
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData
          (parameters vertex))) (budget.tolerance / 4) from
      ⟨by
        have h := owners.first_bound later data first vertex piece.column piece.row
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
          vertex))
        change Fraction.Order.Basic.LessEqual _ _ at h
        change Fraction.Order.Basic.LessEqual _ _
        simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at h
        convert h using 1; rfl,
       by
        have h := owners.second_bound later otherData second vertex piece.column piece.row
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
          vertex))
        change Fraction.Order.Basic.LessEqual _ _ at h
        change Fraction.Order.Basic.LessEqual _ _
        simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at h
        convert h using 1; rfl⟩))
    (fun edge => by
      rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
      exact Path.ConjugateIncrementComparison.conjugateFirst_error
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.grid_increment_bound evaluated entry member
        piece data otherData _ _ (inside edge.castSucc) (inside edge.succ)))
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total] at ownerError
  have sourceError := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateFragmentArea.conjugate_fragment_area_bound
    evaluated entry member piece data otherData parameters inside forward ordered fixed source
  have identity : owned.centeredArea - source.centeredArea =
      (owned.centeredArea - fixed.centeredArea) + (fixed.centeredArea - source.centeredArea) := by ring1
  rw [identity]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct ownerError sourceError) (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateOwnedFragments
