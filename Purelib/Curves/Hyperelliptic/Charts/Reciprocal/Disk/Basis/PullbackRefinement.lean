module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Homogeneous finite-depth comparison on the same retained pullback.
The coarse depth can be fixed before polynomial sampling. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PullbackRefinement

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (PrimitiveSample PrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample
  (Block)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

namespace BasisCommonInterval.PrimitiveSample

variable {cover : Cover data} {interval :
  BasisCommonInterval cover covers}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

variable {sample :
  PrimitiveSample
  interval regular polynomials}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {coarse fine : Nat}
  {target : Coordinate} {floor : Nat}

/-- Refinement preserves the exact endpoints without assuming path closure. -/
theorem Block.pullback_refinement_total (before : PrimitiveSample.Block sample coefficients coarse)
    (after : PrimitiveSample.Block sample coefficients (coarse + fine)) :
    after.pullback.summary.total = before.pullback.summary.total := by
  rw [after.pullback.total, before.pullback.total]

/-- Full area comparison, uniform in the further finite refinement depth. -/
theorem Block.pullback_refinement_area (before : PrimitiveSample.Block sample coefficients coarse)
    (after : PrimitiveSample.Block sample coefficients (coarse + fine))
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (after.pullback.summary.area - before.pullback.summary.area) ≤
      Geometric.Basic.quarterRadius (16 * (BasisSourceCovers.primitiveSlope covers + target)^2) coarse *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 * (interval.edge.right.parameter -
          interval.edge.left.parameter)^4 := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers) request.positive.le)) normNonnegative
  have bound := DyadicAreaRefinement.dyadicArea_refinement_bound (PrimitiveSample.pullbackPath sample coefficients)
    nonnegative
    (fun _ _ firstInside lastInside => PrimitiveSample.path_increment sample request later coefficients firstInside
      lastInside)
    coarse fine ⟨le_rfl, interval.ordered⟩ ⟨interval.ordered, le_rfl⟩ interval.ordered
  rw [← after.pullback_area, ← before.pullback_area] at bound
  exact bound.trans_eq (by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow];
      ring1)

/-- Clipping the request tolerance at one makes the depth scale independent of the chosen polynomial tolerance and
numerical index. -/
theorem Block.pullback_refinement_uniform (before : PrimitiveSample.Block sample coefficients coarse)
    (after : PrimitiveSample.Block sample coefficients (coarse + fine))
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
      (small : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (after.pullback.summary.area - before.pullback.summary.area) ≤
      Geometric.Basic.quarterRadius (16 * (BasisSourceCovers.primitiveSlope covers + 1)^2) coarse *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have scale := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (add_nonneg (BasisSourceCovers.primitiveSlope_nonnegative covers)
      request.positive.le)
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl small) 2) (by
          decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
  have quarter : Geometric.Basic.quarterRadius (16 * (BasisSourceCovers.primitiveSlope covers + target)^2) coarse ≤
      Geometric.Basic.quarterRadius (16 * (BasisSourceCovers.primitiveSlope covers + 1)^2) coarse := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scale (Fraction.Order.Arithmetic.pow_nonneg_direct
      (by decide) coarse)
  have width : interval.edge.right.parameter - interval.edge.left.parameter ≤ 1 :=
    (Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
      (show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 by decide +kernel)
  have widthPower := (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct
    interval.ordered) width 4).trans_eq (_root_.one_pow _)
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Geometric.Basic.quarterRadius_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
        (Fraction.Order.Arithmetic.sq_nonneg_direct (BasisSourceCovers.primitiveSlope covers + 1))) coarse)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (PreparedObservationCoercivity.coefficientNormSq coefficients))
  have clipped := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthPower nonnegative
  rw [Fraction.Field.mul_one_direct] at clipped
  exact
    (Block.pullback_refinement_area
    before after request later).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct quarter (Fraction.Order.Arithmetic.sq_nonneg_direct
      _))
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct interval.ordered)
        4)).trans clipped)

end BasisCommonInterval.PrimitiveSample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PullbackRefinement
