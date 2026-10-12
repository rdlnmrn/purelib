module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Integration.Path.IncrementAreaComparison
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
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Complete parent area bounds include both internal interval areas and the
polygon of interval totals, on the literal retained concatenated paths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (PrimitiveSample PrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample
  (Block)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition (CommonPrimitivePlans)

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

variable {cover : Cover data} {target :
  Coordinate} {floor : Nat}

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)

/-- The original finite coefficient vector has nonnegative squared norm sum. -/
private theorem norm_nonnegative (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : 0 ≤
  PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    InverseRootPolynomial.Coordinate)) _
    (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- Every natural power of an original common interval's nonnegative width is at most one. -/
private theorem width_le_one (interval : CommonCover.BasisCommonInterval cover covers) (power : Nat) :
    (interval.edge.right.parameter - interval.edge.left.parameter)^power ≤ 1 := by
  have width : interval.edge.right.parameter - interval.edge.left.parameter ≤ 1 :=
    (Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
      ((show (1 : Purelib.Data.Rat.Fraction.Rational) - 0 = 1 by ring1))
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct (Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct
    interval.ordered) width power).trans_eq (_root_.one_pow _)

namespace BasisCommonInterval.PrimitiveSample.Block

variable {interval : BasisCommonInterval cover
  covers} {polynomials :
  RegularBasisPolynomials cap index box}
  {sample :
    PrimitiveSample
    interval regular polynomials} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
    {depth : Nat}

/-- Bounds use only the parent data and tolerance, not an interval's dyadic depth. -/
theorem parent_bounds (block : PrimitiveSample.Block sample coefficients depth)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq block.difference ≤ target * (144 * BasisSourceCovers.primitiveSlope covers
      + 160 * target) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 ∧
    Data.Gaussian.Norm.Basic.normSq (block.source.summary.total - block.pullback.summary.total) ≤ target *
      PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq block.source.summary.total ≤ 2 * (BasisSourceCovers.primitiveSlope covers +
      target) * PreparedObservationCoercivity.coefficientNormSq coefficients ∧
    Data.Gaussian.Norm.Basic.normSq block.pullback.summary.total ≤ 2 * (BasisSourceCovers.primitiveSlope covers
      + target) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have slope := BasisSourceCovers.primitiveSlope_nonnegative covers
  have norm := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.norm_nonnegative coefficients
  have areaNonnegative : 0 ≤ target * (144 * BasisSourceCovers.primitiveSlope covers + 160 * target) *
    (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct request.positive.le
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) slope)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) request.positive.le)))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have areaPaid := (Block.area_error block request later).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.width_le_one interval 4)
    areaNonnegative)
  rw [Fraction.Field.mul_one_direct] at areaPaid
  have totalPaid := (Block.total_error block request later).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.width_le_one interval 2)
      request.positive.le) norm)
  rw [Fraction.Field.mul_one_direct] at totalPaid
  have sourcePaid := (Block.source_total_bound block).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.width_le_one interval 2) slope) norm)
  rw [Fraction.Field.mul_one_direct] at sourcePaid
  have commonNonnegative : 0 ≤ 2 * (BasisSourceCovers.primitiveSlope covers + target) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg slope request.positive.le)
  have pullbackPaid := (Block.pullback_total_bound block request later).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.width_le_one interval 2)
      commonNonnegative) norm)
  rw [Fraction.Field.mul_one_direct] at pullbackPaid
  have slopeLe : BasisSourceCovers.primitiveSlope covers ≤ 2 * (BasisSourceCovers.primitiveSlope covers + target) :=
    (show BasisSourceCovers.primitiveSlope covers = BasisSourceCovers.primitiveSlope covers + 0 by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl (add_nonneg slope
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        request.positive.le))).trans_eq (by ring1))
  exact ⟨areaPaid, totalPaid, sourcePaid.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct slopeLe
    norm), pullbackPaid⟩

end BasisCommonInterval.PrimitiveSample.Block

namespace CommonPrimitivePlans.Blocks

variable {polynomials :
  RegularBasisPolynomials cap index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- Every actual retained interval path pair has the original homogeneous area, total-discrepancy and magnitude bounds.

The common slope and coefficient bounds apply independently of the local dyadic depth. -/
theorem paths_bounded : {intervals : List (CommonCover.BasisCommonInterval cover covers)} → {plans :
  CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (blocks : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients depth plans) →
    ∀ pair ∈ blocks.paths,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤ target
        * (144 * BasisSourceCovers.primitiveSlope covers + 160 * target) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ target * PreparedObservationCoercivity.coefficientNormSq
        coefficients ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 *
        (BasisSourceCovers.primitiveSlope covers + target) * PreparedObservationCoercivity.coefficientNormSq
        coefficients ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 *
        (BasisSourceCovers.primitiveSlope covers + target) * PreparedObservationCoercivity.coefficientNormSq
        coefficients
  | _, _, .nil, _, member => False.elim (List.not_mem_nil member)
  | _, _, .cons (request := request) head later remaining, pair, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have bound :=
          BasisCommonInterval.PrimitiveSample.Block.parent_bounds
          head request later
        rw [head.difference_eq, head.source.summary.area_eq, head.pullback.summary.area_eq,
          head.source.summary.total_eq, head.pullback.summary.total_eq] at bound
        exact bound
      · exact
          paths_bounded
          remaining pair member

/-- The complete parent discrepancy is paid without deleting a joining area or assuming that any local or global path
closes. -/
theorem area_bound {intervals : List (CommonCover.BasisCommonInterval cover covers)} {plans :
  CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals}
    (blocks : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients depth plans) (nonnegative : 0
      ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (blocks.paths.map Prod.fst).flatten -
      IncrementArea.pathArea (blocks.paths.map Prod.snd).flatten) ≤
      (2 * (intervals.length : InverseRootPolynomial.Coordinate)^2 * target * (144 * BasisSourceCovers.primitiveSlope
        covers + 160 * target) +
        64 * (intervals.length : InverseRootPolynomial.Coordinate)^4 * target * (BasisSourceCovers.primitiveSlope covers
          + target)) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have norm := Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.norm_nonnegative coefficients
  have bound := IncrementAreaComparison.blocks_area_difference_bound blocks.paths
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative norm)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (BasisSourceCovers.primitiveSlope_nonnegative covers) nonnegative)) norm)
    (fun pair member =>
      (paths_bounded
      blocks pair member).1)
    (fun pair member =>
      (paths_bounded
      blocks pair member).2.1)
    (fun pair member =>
      (paths_bounded
      blocks pair member).2.2.1)
    (fun pair member =>
      (paths_bounded
      blocks pair member).2.2.2)
  rw [Blocks.paths_count blocks] at bound
  exact bound.trans_eq (by ring1)

end CommonPrimitivePlans.Blocks
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea
