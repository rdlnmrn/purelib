module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalTotals
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IndexedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceConstant
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Preserve exact physical words when selecting an occurrence traversal. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices (occurrenceAt)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalRuns
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedRunBudgets.SharedVerticalRuns

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

open Purelib.Riemann.Normalization.RectangularInverseModels

namespace SharedVerticalRuns
variable (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared)
  {index : Nat} (inputs : retained.Inputs index)
  (outer : Fin prepared.occurrences.length) {stage depth : Nat}

variable {cuts : Paths.RectangularSegmentSplitting.GridCuts ((domains.get (occurrenceAt prepared.occurrences
  outer).sideOccurrence.position).domain (occurrenceAt prepared.occurrences outer).sideOccurrence.sheet).geometry}
  {meshBox : Rational.Box} {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}
  {firstColumn secondColumn : Fin mesh.partition.x.intervals.length} {width :
    Normalization.InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide mesh mesh firstColumn
    secondColumn width}
  (trace : side.Trace depth) (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage)
  (bank : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideBanks.SharedVerticalBank.Data (occurrence :=
    occurrenceAt prepared.occurrences outer) trace cache)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget
    (Paths.RectangularDyadicPairedTrace.dyadicCount depth) allowance)
  (owners : OwnerRequest (occurrenceAt
    prepared.occurrences outer) budget.tolerance) (later : owners.index ≤ stage)
  {junctionAllowance : Normalization.InverseRootPolynomial.Coordinate} (junctionBudget :
    Path.NoisyPathArea.LengthErrorBudget 1 junctionAllowance)
  (junctionOwners : OwnerRequest (occurrenceAt
    prepared.occurrences outer) junctionBudget.tolerance) (junctionLater : junctionOwners.index ≤ stage)

variable (blocks : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank (occurrenceAt
  prepared.occurrences outer) mesh
    (occurrenceAt prepared.occurrences outer).sourceVertical (occurrenceAt prepared.occurrences outer).sourceForward)
  (axis : (occurrenceAt prepared.occurrences outer).sourceVertical = true)
  (fixed : (occurrenceAt prepared.occurrences outer).sourceConstant = width)
  (boxEq : meshBox = (base.faces.regulars[(occurrenceAt prepared.occurrences
    outer).sideOccurrence.position.val]'(occurrenceAt prepared.occurrences
      outer).sideOccurrence.position.isLt).cell.box)

/-- A dependent Boolean case split reads its true branch when the retained direction is true. -/
private theorem rec_true {b : Bool} {T : Sort u}
    (onFalse : b = false → T) (onTrue : b = true → T) (direction : b = true) :
    (Bool.rec (motive := fun t => b = t → T) onFalse onTrue b) rfl = onTrue direction := by
  cases direction
  rfl

/-- A dependent Boolean case split reads its false branch when the retained direction is false. -/
private theorem rec_false {b : Bool} {T : Sort u}
    (onFalse : b = false → T) (onTrue : b = true → T) (direction : b = false) :
    (Bool.rec (motive := fun t => b = t → T) onFalse onTrue b) rfl = onFalse direction := by
  cases direction
  rfl

/-- Applying a Boolean-equality transport gives the original branch value at the reversed equality witness. -/
private theorem transport_apply {a b : Bool} {T : Sort u}
    (value : b = a → T) (equal : a = b) (selfEq : b = b) :
    (Eq.rec (motive := fun x _ => b = x → T) value equal) selfEq = value equal.symm := by
  cases equal
  rfl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices in
/-- Traversal selection preserves the entire acquired side word. -/
theorem forOccurrence_increments :
    (List.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence.SharedVerticalRuns.forOccurrence
      retained inputs outer trace cache bank coefficients
      budget owners later junctionBudget junctionOwners junctionLater blocks axis fixed boxEq).physical).flatten =
      if (occurrenceAt prepared.occurrences outer).sourceForward then
        Path.CenteredPathIncrements.Sample.increments
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedVerticalBank.Data.sample bank
          coefficients)
      else Path.PairedAreaReversal.reverseIncrements (Path.CenteredPathIncrements.Sample.increments
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedSideSamples.SharedVerticalBank.Data.sample bank
        coefficients)) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrence.SharedVerticalRuns.forOccurrence
  rcases Bool.eq_false_or_eq_true (occurrenceAt prepared.occurrences outer).sourceForward with direction | direction
  · simp only [-eq_self, -iff_self, direction, if_pos rfl]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals.SharedVerticalRuns.rec_true
      (direction := direction)]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals.SharedVerticalRuns.transport_apply]
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalTotals.SharedVerticalRuns.forward_increments
      retained inputs outer trace cache bank coefficients _ _
      budget owners later junctionBudget junctionOwners junctionLater _ axis direction boxEq
  · simp only [-eq_self, -iff_self, direction, if_neg (by decide : ¬ false = true)]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals.SharedVerticalRuns.rec_false
      (direction := direction)]
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals.SharedVerticalRuns.transport_apply]
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SharedVerticalTotals.SharedVerticalRuns.reverse_increments
      retained inputs outer trace cache bank coefficients _ _
      budget owners later junctionBudget junctionOwners junctionLater _ axis direction boxEq

end SharedVerticalRuns
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.VerticalOccurrenceTotals
