module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest
public import Purelib.Riemann.Normalization.NewtonResplitDeterminantBound
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Data.Vector.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data

/-! Geometric decay on the retained Newton mesh transfers to the original
corrected period models. No original-period determinant bound is assumed. -/
namespace Purelib.Riemann.Normalization.NewtonOriginalDeterminantDecay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (BilinearRequest)
open Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest (CanonicalDeterminantRequest)
open Purelib.Riemann.Normalization.NewtonResplitDeterminantBound (ResplitExteriorPreparation)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison (resplitWordDeterminant)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Rational} {first second : Fin genus} {floor : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- The original canonical determinant request at the retained exterior's exact refinement depth. -/
@[expose] def OriginalDeterminantComparison (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second target radius floor)
    (exterior : ResplitExteriorPreparation paired boundary) (minimum : Nat) :=
  CanonicalDeterminantRequest prepared (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary
    exterior.source.depth) target minimum

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- A shared threshold guaranteeing the original period determinant's quantitative decay.

The actual refined numerical cache, cut readings and annular comparisons are retained; all later period stages satisfy
the original factor-1634 target bound. -/
@[expose] def OriginalDeterminantDecay (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second target radius floor)
    (exterior : ResplitExteriorPreparation paired boundary) (threshold : Nat) : Prop :=
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary exterior.source.depth
  ∀ numericalIndex (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains
    numericalIndex)
    (readings : Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings refined.paid.cut cache)
    (_cached : NewtonRequestedCutComparison.CutAnnularReadings refined.comparison readings), threshold ≤ numericalIndex
      →
    ∀ stage, threshold ≤ stage →
    Data.Gaussian.Norm.Basic.normSq (Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.determinant prepared
      first
      second stage) < 1634 * target

namespace ResplitExteriorPreparation

variable {boundary : BoundaryPreparation preparation first second target radius floor}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Combine original canonical and geometric determinant requests under one threshold.

The original boundary is refined to the retained exterior depth, and the maximum of both actual request floors preserves
the requested minimum and exact determinant comparison. -/
@[expose] def originalDeterminantRequest (exterior : ResplitExteriorPreparation paired boundary)
    (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (minimum : Nat) :
    OriginalDeterminantComparison prepared boundary exterior minimum ×
      {threshold : Nat // minimum ≤ threshold ∧ OriginalDeterminantDecay prepared boundary exterior threshold} := by
  have positive : 0 < target := (Fraction.Order.Arithmetic.mul_pos_direct boundary.fine.positive (by
      decide : (0 : Fraction.Rational) < 4)).trans_eq
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary exterior.source.depth
  let comparison := CanonicalDeterminantRequest.build prepared refined target positive minimum
  let geometric := exterior.determinantRequest prepared
    (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) refined.periodGeometry) minimum
  let threshold := max comparison.threshold geometric.val
  refine ⟨comparison, threshold, comparison.minimum_le.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro numericalIndex cache readings cached later stage after
  have geometry := geometric.property.2 numericalIndex cache readings cached ((Nat.Order.le_max_right _ _).trans later)
  have model := comparison.accurate numericalIndex cache readings.left readings.right
    ((Nat.Order.le_max_left _ _).trans later) stage ((Nat.Order.le_max_left _ _).trans after)
  let resplit := Meshes.Newton.LocalPairedPeriodComparison.resplitWordDeterminant prepared (current := refined.lifted)
    (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) refined.periodGeometry)
    (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values)
  let original := Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.determinant prepared first second stage
  have estimate := (Norm.Bounds.normSq_sub_le_two resplit (resplit - original)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_lt_add_right_direct geometry _).trans
        (Fraction.Order.Arithmetic.add_lt_add_left_direct model _)))
  have equal : resplit - (resplit - original) = original := by ring1
  exact ((congrArg Data.Gaussian.Norm.Basic.normSq equal).symm.trans_lt estimate).trans_eq (by ring1)

end ResplitExteriorPreparation
end Purelib.Riemann.Normalization.NewtonOriginalDeterminantDecay
