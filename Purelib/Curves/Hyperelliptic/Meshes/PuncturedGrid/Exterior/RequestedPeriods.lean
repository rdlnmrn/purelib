module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodGaps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! The existing requested odd exterior acquisition already chooses an
allowance that pays its period as well as its energy comparison. These
estimates reuse that acquisition, its root packets and its shared samples. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance
  (surfaceCoefficient correctionCoefficient)

/-- The retained energy allowance also pays the original segment count in the closing-period estimate. -/
theorem period_coefficient_le (parents count : Nat) {slope : Normalization.InverseRootPolynomial.Coordinate}
  (nonnegative : 0 ≤ slope) :
    2 * (1 + (count : Normalization.InverseRootPolynomial.Coordinate) * (count :
      Normalization.InverseRootPolynomial.Coordinate)) ≤
      surfaceCoefficient
      parents count slope := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  have parentsNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 656)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (parents : Normalization.InverseRootPolynomial.Coordinate))
  have fourthNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 256)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2) nonnegative)
      (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 3))
  have secondNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct (count : Normalization.InverseRootPolynomial.Coordinate))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 64) nonnegative)
      (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 62))
  exact (add_nonneg (add_nonneg (add_nonneg (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 5790) parentsNonnegative)
    fourthNonnegative) secondNonnegative).trans_eq (by
        unfold ExteriorEnergyAllowance.surfaceCoefficient ExteriorEnergyAllowance.correctionCoefficient;
        ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation
namespace RequestedOddEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
  (sourceMaximum_nonnegative)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation
  (RequestedOddEnergy)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance
  (period_coefficient_le)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {component :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential}
  {target energyTarget : Coordinate} {floor depthFloor energyFloor :
    Nat}

/-- No cap-total premise or new accuracy request is supplied. The actual original source period is below the
acquisition's requested tolerance. -/
theorem period_small (result : AllSurfacePreparation.RequestedOddEnergy prepared component target energyTarget floor
  depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) : Data.Gaussian.Norm.Basic.normSq
      result.acquired.evaluated.original.integral < target := by
  have joined : result.acquired.roots.allowance ≤ result.budget.allowance := by
    rw [result.acquired.roots.allowance_eq]
    exact Fraction.Order.Basic.min_le_left _ _
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (le_refl result.budget.allowance) (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joined
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le result.request.count))
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le result.request.count)))))
    (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have coefficient : 2 * (1 + (result.request.count : Normalization.InverseRootPolynomial.Coordinate) *
    (result.request.count : Normalization.InverseRootPolynomial.Coordinate)) ≤ result.budget.coefficient := by
    rw [result.request.count_eq, result.budget.coefficient_eq]
    exact
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.period_coefficient_le _
      _ (AllSurfacePreparation.sourceMaximum_nonnegative _)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient result.budget.positive.le
  have small := result.acquired.source_period_bound branch
  have bound : 2 * (result.budget.allowance + (result.request.count : Normalization.InverseRootPolynomial.Coordinate) *
      ((result.request.count : Normalization.InverseRootPolynomial.Coordinate) * result.acquired.roots.allowance)) ≤
      (2 * (1 + (result.request.count : Normalization.InverseRootPolynomial.Coordinate) * (result.request.count :
        Normalization.InverseRootPolynomial.Coordinate))) * result.budget.allowance := by
    exact (by ring1 : 2 * (result.budget.allowance + (result.request.count :
      Normalization.InverseRootPolynomial.Coordinate) *
      ((result.request.count : Normalization.InverseRootPolynomial.Coordinate) * result.acquired.roots.allowance)) =
      2 * (result.budget.allowance + ((result.request.count : Normalization.InverseRootPolynomial.Coordinate) *
        (result.request.count : Normalization.InverseRootPolynomial.Coordinate)) *
        result.acquired.roots.allowance)).trans_le (scaled.trans_eq (by ring1))
  exact (small.trans_le (bound.trans paid)).trans result.budget.paid

/-- The period bound belongs to the same actual triangle-source increments as the existing exterior area and energy
comparisons. -/
theorem triangle_period_small
    (result : AllSurfacePreparation.RequestedOddEnergy prepared component target energyTarget floor depthFloor
      energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (readings : TrianglePrimitiveReadings.TriangleReadings
      result.acquired.shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (result.request.entries.map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values))) < target :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (result.acquired.evaluated.original.triangle_integral
    readings)).symm.trans_lt (result.period_small branch)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy
