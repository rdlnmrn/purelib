module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRow
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
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

/-! One retained finite row bank compares the resplit determinant with the
original corrected period models, for every later pair of numerical stages. -/
namespace Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces (MeshWordReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRow (CanonicalDeterminantRow)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (BilinearRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison (resplitWordDeterminant)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

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
  {boundaryTarget radius : Rational} {floor : Nat}
  {first second differential cycle : Fin genus}
  {target : Rational} {minimum : Nat}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- A dependent vector of original cycle rows at the exact per-term allowance. -/
@[expose] def CanonicalDeterminantRows (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (target : Fraction.Rational) (minimum : Nat) :=
  Vector.DependentVector (fun cycle : Fin genus =>
    CanonicalDeterminantRow prepared boundary cycle (Budget.Aggregate.perTerm target genus) minimum)

open Purelib.Curves.Hyperelliptic in
/-- The exact maximum of the requested minimum and all retained row floors. -/
@[expose] def CanonicalDeterminantThreshold {prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
    {boundary : BoundaryPreparation preparation first second boundaryTarget radius floor}
    (rows : CanonicalDeterminantRows prepared boundary target minimum) (threshold : Nat) : Prop :=
  threshold = max minimum (max (rows.maximum fun _ row => row.numericalIndex)
    (rows.maximum fun _ row => row.periodStage))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Cached original canonical determinant rows with one certified common threshold.

The actual boundary, differential pair and positive target index all rows; the threshold retains both numerical and
period-stage requirements. -/
structure CanonicalDeterminantRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (target : Fraction.Rational) (minimum : Nat) : Type 3 where
  /-- The original requested determinant target is strictly positive. -/ positive : 0 < target
  /-- The cached original dependent vector of cycle-row requests. -/ rows : CanonicalDeterminantRows prepared boundary
    target minimum
  /-- The retained common numerical and period-stage threshold. -/ threshold : Nat
  /-- The threshold is exactly the requested minimum and both cached row maxima. -/ threshold_eq :
    CanonicalDeterminantThreshold (target := target) (minimum := minimum) rows threshold

constructive_injectivity CanonicalDeterminantRequest

namespace CanonicalDeterminantRequest

variable {prepared : Prepared paired}
  {boundary : BoundaryPreparation preparation first second boundaryTarget radius floor}

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Build the original cycle-row cache and its exact shared threshold.

The per-term target uses the retained genus, and the threshold includes the requested minimum and both maxima over those
actual cached rows. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : BoundaryPreparation preparation first second boundaryTarget radius floor)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    CanonicalDeterminantRequest prepared boundary target minimum :=
  let rows := Vector.DependentVector.ofFn (fun cycle : Fin genus =>
    CanonicalDeterminantRow.build prepared boundary cycle (Budget.Aggregate.perTerm target genus)
      (Budget.Aggregate.perTerm_positive positive genus) minimum)
  let threshold := max minimum (max (rows.maximum fun _ row => row.numericalIndex)
    (rows.maximum fun _ row => row.periodStage))
  ⟨positive, rows, threshold, by rfl⟩

/-- The retained common threshold is at least the original requested minimum. -/
theorem minimum_le (data : CanonicalDeterminantRequest prepared boundary target minimum) : minimum ≤ data.threshold :=
  (Nat.Order.le_max_left _ _).trans_eq data.threshold_eq.symm

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original resplit-word determinant meets the retained strict period-determinant target.

Both cache index and period stage must exceed the common threshold; the exact genus-weighted row allowance pays the
finite determinant sum. -/
theorem accurate (data : CanonicalDeterminantRequest prepared boundary target minimum)
    (numericalIndex : Nat) (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics boundary.domains
      numericalIndex)
    (left : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) boundary.lifted.mesh)
    (right : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second) boundary.lifted.mesh)
    (later : data.threshold ≤ numericalIndex) (stage : Nat) (after : data.threshold ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Meshes.Newton.LocalPairedPeriodComparison.resplitWordDeterminant prepared (current
      :=
      boundary.lifted)
      (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) boundary.periodGeometry)
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh left.values)
        (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation boundary.lifted.mesh right.values) -
      Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.determinant prepared first second stage) < target :=
        by
  have numericalBound : data.rows.maximum (fun _ row => row.numericalIndex) ≤ data.threshold :=
    ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)).trans_eq data.threshold_eq.symm
  have periodBound : data.rows.maximum (fun _ row => row.periodStage) ≤ data.threshold :=
    ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)).trans_eq data.threshold_eq.symm
  have each (cycle : Fin genus) := (data.rows.get cycle).accurate numericalIndex cache left right
    (((data.rows.get_le_maximum (fun _ row => row.numericalIndex) cycle).trans numericalBound).trans later)
    stage (((data.rows.get_le_maximum (fun _ row => row.periodStage) cycle).trans periodBound).trans after)
  change Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _) < target
  rw [← FiniteSum.Fin.sumFin_sub]
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le _ (Budget.Aggregate.perTerm target genus) each
  have countBound := Budget.Aggregate.count_mul_perTerm_lt data.positive genus
  exact estimate.trans_lt ((show (genus : Fraction.Rational)^2 * Budget.Aggregate.perTerm target genus =
    (genus : Fraction.Rational) * ((genus : Fraction.Rational) * Budget.Aggregate.perTerm target genus) by
      ring1).trans_lt countBound)

end CanonicalDeterminantRequest
end Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest
