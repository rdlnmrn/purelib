module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Rectangle.Accuracy

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Topology

public section

/-!
# First-phase scalar budgets for all retained cut-period segments

Only finite scalar bounds and indices are selected here. The maximum is
computed before any segment constructs its numerical primitive polynomials.
The retained spine preserves each segment's original count-dependent budget.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces} {ambient :
    Purelib.Geometry.Rational.Box}

/-- Retain a segment's basis bounds or compute bounds for its supplied odd-power numerator.

The original basis case reads the comparison's exact saved bounds. An
explicit differential keeps its numerator and scale on the same original
face clearance; no path preparation or integration cache is reconstructed.
-/
@[expose] def segmentBounds {start finish : Gaussian}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)} {placement : SegmentFace mesh segment}
    {piece : CoveredSegment segment owner} {differential : Differential genus} {parentSheet : Fin 2}
    (compared : SegmentComparison placement piece differential parentSheet)
    (form : Option (OddPowerDifferential curve.polynomial)) :
    PrimitiveOverlapBounds placement.face.clearance
      (match form with
        | none => differentialNumerator differential
        | some actual => actual.numerator.scale actual.scale) :=
  match form with
  | none => compared.entered.globalBounds
  | some actual => PrimitiveOverlapBounds.build placement.face.clearance (actual.numerator.scale actual.scale)

/-- Scalar fragment budgets on the retained comparison spine, optionally for one original odd-power differential.

Every occurrence keeps its original face, split count and comparison cache.
The default uses the saved basis bounds and one inverse factor; an explicit
form supplies its scaled numerator and actual denominator pair count.
-/
@[expose] def Budgets (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) (target :
  InverseRootPolynomial.Coordinate) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces), AssignedSegments.Comparisons differential
        parentSheet assigned → (form : optParam (Option (OddPowerDifferential curve.polynomial)) none) → Type
  | _, _, _, _, _, _, .nil _ _, _, _ => PUnit
  | _, _, _, _, _, _, .cons _ remaining, compared, form =>
      FragmentAccuracy (segmentBounds compared.1 form) compared.1.entered.domain.steps
        compared.1.entered.mesh.splits.pieceCount (target / 4)
          (form.elim 0 (fun actual => actual.denominatorPairs)) ×
        Budgets differential parentSheet target
          remaining compared.2 form

namespace Budgets

/-- Select every retained segment's count-dependent scalar budget before constructing numerical primitive polynomials.
-/
@[expose] def build (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (form : optParam (Option (OddPowerDifferential curve.polynomial)) none),
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets differential parentSheet target assigned
        compared form
  | _, _, _, _, _, _, .nil _ _, _, _ => ⟨⟩
  | _, _, _, _, _, _, .cons _ remaining, compared, form =>
      ⟨FragmentAccuracy.build (segmentBounds compared.1 form) compared.1.entered.domain.steps
        compared.1.entered.mesh.splits.pieceCount
        (target / 4) (Fraction.Order.Field.div_pos_direct positive (by decide))
          (form.elim 0 (fun actual => actual.denominatorPairs)),
        build differential parentSheet
          target positive remaining compared.2 form⟩

/-- Read the maximum requested grid index over the actual retained segment budgets. -/
@[expose] def maximum (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) {target :
  InverseRootPolynomial.Coordinate} {form : Option (OddPowerDifferential curve.polynomial)} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned),
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets differential parentSheet target assigned
        compared form → Nat
  | _, _, _, _, _, _, .nil _ _, _, _ => 0
  | _, _, _, _, _, _, .cons _ remaining, compared, budgets =>
      max budgets.1.grid.index (maximum
        differential parentSheet remaining compared.2 budgets.2)

/-- Every retained segment budget fits the supplied shared grid index. -/
@[expose] def IndicesBelow (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) {target :
  InverseRootPolynomial.Coordinate} {form : Option (OddPowerDifferential curve.polynomial)} (index : Nat) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned),
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets differential parentSheet target assigned
        compared form → Prop
  | _, _, _, _, _, _, .nil _ _, _, _ => True
  | _, _, _, _, _, _, .cons _ remaining, compared, budgets =>
      budgets.1.grid.index ≤ index ∧
        IndicesBelow differential
        parentSheet index remaining compared.2 budgets.2

/-- A bound on the actual retained budget maximum bounds every original segment's requested grid index. -/
theorem indicesBelow_of_maximum_le (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) {target
  : InverseRootPolynomial.Coordinate} {form : Option (OddPowerDifferential curve.polynomial)} (index : Nat) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared : AssignedSegments.Comparisons
        differential parentSheet assigned)
      (budgets : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets.Budgets differential parentSheet target
        assigned compared form),
      maximum differential parentSheet assigned
        compared budgets ≤ index → IndicesBelow
        differential parentSheet index assigned compared budgets
  | _, _, _, _, _, _, .nil _ _, _, _, _ => trivial
  | _, _, _, _, _, _, .cons _ remaining, compared, budgets, later =>
      ⟨(Purelib.Data.Nat.Order.le_max_left _ _).trans later,
        indicesBelow_of_maximum_le
          differential parentSheet index remaining compared.2 budgets.2 ((Purelib.Data.Nat.Order.le_max_right _ _).trans
          later)⟩

end Budgets
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
