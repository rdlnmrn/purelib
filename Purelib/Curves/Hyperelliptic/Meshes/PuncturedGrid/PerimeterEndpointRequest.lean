module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
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
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

/-! Automatic shared requests for every actual perimeter endpoint correction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Riemann.Periods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests (CornerGrids)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointBounds (side_remainder_centered_bound)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {position : Fin base.faces.regulars.length} {sheet : Fin 2}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Basic (Canonical)

set_option genInjectivity false in
/-- The retained magnitude banks, corner grids and common stage for a perimeter endpoint correction.

Its positive tolerance pays the specified target uniformly over the original faces, sheets and sides. -/
structure PerimeterEndpointRequest (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet)
    (i j : Fin genus) (target : Fraction.Rational) where
  /-- The retained first differential's magnitude bank on the original face domains. -/ firstMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i)
  /-- The retained second differential's magnitude bank on the same face domains. -/ secondMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j)
  /-- The shared positive endpoint comparison tolerance. -/ tolerance : Fraction.Rational
  /-- The retained endpoint tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- Four times the retained tolerance is at most one. -/ small : 4 * tolerance ≤ 1
  /-- The retained magnitude-weighted endpoint allowance fits the requested target. -/ paid : 128 *
    (firstMagnitude.bound + secondMagnitude.bound + 1) * tolerance ≤ target
  /-- The actual corner comparison grids prepared with that tolerance. -/ grids : CrossingCornerRequests.CornerGrids
    fixed tolerance
  /-- The common stage paying both magnitude banks and the corner grids. -/ index : Nat
  /-- The first magnitude threshold is paid at the common stage. -/ first_le : firstMagnitude.index ≤ index
  /-- The second magnitude threshold is paid at the common stage. -/ second_le : secondMagnitude.index ≤ index
  /-- Every retained corner grid threshold is paid at the common stage. -/ grids_le : grids.index ≤ index

constructive_injectivity PerimeterEndpointRequest

namespace PerimeterEndpointRequest

/-- Prepare both original magnitude banks and corner grids with a shared paid endpoint tolerance.

The tolerance is the smaller of the weighted target allowance and one quarter, and the stage is the maximum of all
retained request thresholds. -/
@[expose] def build (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (i j : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target) :
      PerimeterEndpointRequest fixed i j target := by
  let first := FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential i)
  let second := FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential j)
  let weight := 128 * (first.bound + second.bound + 1)
  have nonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (add_nonneg (add_nonneg first.nonnegative second.nonnegative) (by decide))
  let tolerance := min (Weighted.allowance target weight) (1 / 4)
  have tolerancePositive : 0 < tolerance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min
    (Weighted.allowance_positive positive nonnegative)
    (Fraction.Order.Field.div_pos_direct (by decide) (by decide))
  have small : 4 * tolerance ≤ 1 := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right (Weighted.allowance target weight) (1 / 4))
      (by decide : (0 : Fraction.Rational) ≤ 4)
    apply bound.trans_eq
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have paid : weight * tolerance ≤ target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _)
      nonnegative).trans
      (Weighted.mul_allowance_le positive.le nonnegative)
  let grids := CornerGrids.build fixed tolerance tolerancePositive
  exact ⟨first, second, tolerance, tolerancePositive, small, paid, grids,
    max (max first.index second.index) grids.index,
    (Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_left _ _),
    (Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_left _ _),
      Purelib.Data.Nat.Order.le_max_right _ _⟩

/-- The original side-area remainder differs from its centered side area by at most the requested squared-norm target.

The comparison uses the supplied retained perimeter and centered samples at a stage paying their original endpoint
request. -/
theorem bound {endpointTarget : Fraction.Rational}
    (allocated : PerimeterEndpointRequest fixed i j
      endpointTarget) (later : allocated.index ≤ stage)
    {traces : RectangularPerimeterTraces.PerimeterTraces ((request.entries.get sheet).meshes.entries.get position)}
    (samples : RectangularCenteredPerimeter.Centered traces
      (FacePerimeters.faceValues cache.normalize i j position sheet))
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j) (side :
      GridLiftedDualSteps.GridSide) :
    Data.Gaussian.Norm.Basic.normSq (HoleAreaRemainder.sideAreaRemainder perimeters position sheet side -
      SideCenteredRemainder.sideCenteredArea samples side) ≤ endpointTarget := by
  have estimate := PerimeterEndpointBounds.side_remainder_centered_bound allocated.firstMagnitude
    allocated.secondMagnitude
    (allocated.first_le.trans later) (allocated.second_le.trans later) allocated.positive allocated.small
    (allocated.grids.row sheet position i) ((allocated.grids.row_index_le sheet position i).trans
      (allocated.grids_le.trans later))
    (allocated.grids.row sheet position j) ((allocated.grids.row_index_le sheet position j).trans
      (allocated.grids_le.trans later)) samples perimeters side
  have paid : 32 * (allocated.firstMagnitude.bound + allocated.secondMagnitude.bound + 1) *
      (4 * allocated.tolerance) ≤ endpointTarget :=
    (le_of_eq (by ring1)).trans allocated.paid
  exact estimate.trans paid

end PerimeterEndpointRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
