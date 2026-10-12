module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerTotal
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-! A positive finite budget pays the complete actual corner replacement. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Riemann.Periods

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests (CornerGrids)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests (Samples)

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin)

set_option genInjectivity false in
/-- All corner replacement requests share these retained magnitude references, scalar grids, and one certified
numerical-stage threshold. -/
structure CornerRequest (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (i j : Fin genus) (target :
  Fraction.Rational) where
  /-- The retained magnitude bank for the first standard differential. -/ firstMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i)
  /-- The retained magnitude bank for the second standard differential. -/ secondMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j)
  /-- The shared scalar tolerance for all actual corner replacements. -/ tolerance : Fraction.Rational
  /-- The retained corner tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- Sixteen times the shared tolerance is at most one. -/ small : 16 * tolerance ≤ 1
  /-- The complete count and magnitude weight times the tolerance fits the requested target. -/ paid : 8192 *
    (faces.regulars.length : Fraction.Rational)^4 *
    (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * tolerance ≤ target
  /-- The retained scalar corner grids sharing the original face preflights. -/ grids :
    CrossingCornerRequests.CornerGrids fixed tolerance
  /-- The common numerical stage paying both magnitude banks and every corner grid. -/ index : Nat
  /-- The first magnitude threshold is at most the retained common stage. -/ first_le : firstMagnitude.index ≤ index
  /-- The second magnitude threshold is at most the retained common stage. -/ second_le : secondMagnitude.index ≤ index
  /-- The corner-grid threshold is at most the retained common stage. -/ grids_le : grids.index ≤ index

constructive_injectivity CornerRequest

namespace CornerRequest

/-- Choose a positive shared corner tolerance and cache all grids at one paid numerical stage. -/
@[expose] def build (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (i j : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j target := by
  let first := FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential i)
  let second := FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential j)
  let weight := 8192 * (faces.regulars.length : Fraction.Rational)^4 * (4 * (first.bound + second.bound) + 1)
  have nonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 8192) (Nat.zero_le _))
      (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg first.nonnegative
      second.nonnegative)) (by decide))
  let tolerance := min (Weighted.allowance target weight) (1 / 16)
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min
    (Weighted.allowance_positive positive nonnegative)
    (Fraction.Order.Field.div_pos_direct (by decide) (by decide +kernel))
  have small : 16 * tolerance ≤ 1 := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Basic.min_le_right (Weighted.allowance target weight) (1 / 16))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
    apply bound.trans_eq
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  have paid : weight * tolerance ≤ target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left _ _)
      nonnegative).trans
      (Weighted.mul_allowance_le positive.le nonnegative)
  let grids := CornerGrids.build fixed tolerance tolerancePositive
  exact ⟨first, second, tolerance, tolerancePositive, small, paid, grids,
    max (max first.index second.index) grids.index,
    (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _),
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _), Data.Nat.Order.le_max_right _ _⟩

/-- The complete actual endpoint-jump replacement fits the retained corner target at every paid stage. -/
theorem bound {retained : Matched.CrossingBank request mesh}
    {allocated : Matched.CrossingRequests (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor retained} {cache : RegularMeshes.Numerics domains stage}
    {cornerTarget : Fraction.Rational} (corner :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget.CornerRequest fixed i j cornerTarget) (later :
      corner.index ≤ stage)
    (samples : CrossingRequests.Samples allocated cache.normalize) :
    Data.Gaussian.Norm.Basic.normSq (samples.endpointJump - retained.cornerJump cache.normalize i j) ≤
      cornerTarget :=
  (samples.corner_jump_bound corner.firstMagnitude corner.secondMagnitude
    (corner.first_le.trans later) (corner.second_le.trans later) corner.grids (corner.grids_le.trans later)
    corner.positive corner.small).trans corner.paid

end CornerRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
