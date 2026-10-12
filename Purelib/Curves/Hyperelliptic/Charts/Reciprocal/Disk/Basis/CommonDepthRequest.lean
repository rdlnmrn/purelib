module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement.CommonPrimitivePlans

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Choose a chart depth from the original cover before sampling. Its paid
comparison holds for every further finite refinement of the same pullbacks. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition (CommonPrimitivePlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans (Blocks)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}

open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

set_option genInjectivity false in
/-- A preselected common chart depth paying every further finite pullback refinement.

The original cover count and primitive slope determine a cached scale; a finite geometric search selects a depth above
the supplied floor. -/
structure BasisCommonDepthRequest (common : CommonCover.BasisCommonCover cover covers minimum)
    (allowance : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached squared interval-count and primitive-slope refinement coefficient. -/ scale :
    InverseRootPolynomial.Coordinate
  /-- The retained scale is exactly the refinement coefficient of the original common cover. -/ scale_eq : scale =
    (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * 16 * (BasisSourceCovers.primitiveSlope covers +
    1)^2
  /-- The retained finite dyadic depth selected before sampling. -/ depth : Nat
  /-- The depth is exactly the first quarter-radius search result below the squared allowance. -/ depth_eq : depth =
    Search.firstQuarterBelow scale floor (allowance^2)
  /-- The selected depth is no smaller than the requested original floor. -/ floor_le : floor ≤ depth
  /-- The selected geometric radius is strictly below the requested squared allowance. -/ paid :
    Geometric.Basic.quarterRadius scale depth < allowance^2

constructive_injectivity BasisCommonDepthRequest

namespace BasisCommonDepthRequest

/-- Compute the original common-cover refinement scale and select its first paid depth above the supplied floor. -/
@[expose] def build (common : CommonCover.BasisCommonCover cover covers minimum) (allowance :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < allowance) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest.BasisCommonDepthRequest common allowance
      floor := by
  let scale := (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * 16 * (BasisSourceCovers.primitiveSlope
    covers + 1)^2
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let depth := Search.firstQuarterBelow scale floor (allowance^2)
  exact ⟨scale, rfl, depth, rfl, Search.firstQuarterBelow_ge _ _ _,
    Search.firstQuarterBelow_accurate scale nonnegative floor _ (Fraction.Order.Arithmetic.pow_pos_direct positive 2)⟩

variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {polynomials :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {coarse depth polynomialFloor :
    Nat}

/-- Compare retained acquisitions at any two ordered depths beyond the preselected minimum, including a later chart
depth and prepared `extraDepth`. -/
theorem acquisition_later (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest.BasisCommonDepthRequest common allowance floor)
    {areaAllowance : InverseRootPolynomial.Coordinate} {request : CommonPrimitiveRequest regular
      common areaAllowance polynomialFloor}
    (before : request.Acquisition polynomials originals cells coefficients coarse)
    (after : request.Acquisition polynomials originals cells coefficients depth)
    (coarseLater : budget.depth ≤ coarse) (later : coarse ≤ depth) :
    Data.Gaussian.Norm.Basic.normSq (after.pullback.area - before.pullback.area) ≤ allowance^2 *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  obtain ⟨fine, equal⟩ : ∃ fine, depth = coarse + fine :=
    ⟨depth - coarse, (Nat.Subtraction.add_sub_of_le later).symm⟩
  subst depth
  have small : request.tolerance ≤ 1 := by rw [request.tolerance_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have bound := Blocks.pullback_refinement_area before.blocks after.blocks small
  rw [← budget.scale_eq] at bound
  have scaleNonnegative : 0 ≤ budget.scale := by
    rw [budget.scale_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have paid := (quarterRadius_antitone scaleNonnegative coarseLater).trans budget.paid.le
  have result := bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct (PreparedObservationCoercivity.coefficientNormSq coefficients)))
  rw [after.blocks.pullbackSummary.area_eq, before.blocks.pullbackSummary.area_eq,
    ← after.pullback.area_eq, ← before.pullback.area_eq] at result
  exact result

end BasisCommonDepthRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
