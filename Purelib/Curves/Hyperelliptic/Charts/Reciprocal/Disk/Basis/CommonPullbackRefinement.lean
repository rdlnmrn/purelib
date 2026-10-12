module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PullbackRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PullbackRefinement.BasisCommonInterval.PrimitiveSample

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! The complete parent refinement comparison retains the joining polygon.
Its area cancels by exact equality of block totals at the two depths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition (CommonPrimitivePlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans (Blocks)
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

variable {cover : Cover data} {target :
  Coordinate} {floor : Nat}

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

namespace CommonPrimitivePlans.Blocks

variable {polynomials :
  RegularBasisPolynomials cap index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {coarse fine : Nat}

/-- Compare the cached totals, without reading either path again. -/
theorem pullback_refinement_total : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (before : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans) →
    (after : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans) →
    after.pullbackSummary.total = before.pullbackSummary.total
  | _, _, .nil, .nil => rfl
  | _, _, .cons before _ restBefore, .cons after _ restAfter => by
      change after.pullback.summary.total + restAfter.pullbackSummary.total =
        before.pullback.summary.total + restBefore.pullbackSummary.total
      rw [Block.pullback_refinement_total before after,
        pullback_refinement_total
        restBefore restAfter]

/-- The actual per-interval pullback area differences at the two retained depths, in original interval order. -/
private def differences : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans →
    CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans → List
      InverseRootPolynomial.Gaussian
  | _, _, .nil, .nil => []
  | _, _, .cons before _ restBefore, .cons after _ restAfter =>
      (after.pullback.summary.area - before.pullback.summary.area) ::
        differences
        restBefore restAfter

/-- The retained refinement-difference list contains exactly one entry per original common interval. -/
private theorem differences_count : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (before : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans) →
    (after : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans) →
    (differences
      before after).length = intervals.length
  | _, _, .nil, .nil => rfl
  | _, _, .cons _ _ restBefore, .cons _ _ restAfter => congrArg Nat.succ
    (differences_count
    restBefore restAfter)

/-- The actual interval area differences sum to the full original parent area difference.

Exact retained block totals cancel the original joining polygon at the two depths. -/
private theorem differences_sum : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (before : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans) →
    (after : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans) →
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (differences
      before after) = after.pullbackSummary.area - before.pullbackSummary.area
  | _, _, .nil, .nil => by change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | _, _, .cons before _ restBefore, .cons after _ restAfter => by
      change (after.pullback.summary.area - before.pullback.summary.area) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (differences
        restBefore restAfter) =
        (after.pullback.summary.area + restAfter.pullbackSummary.area +
          BoundaryRibbon.area after.pullback.summary.total restAfter.pullbackSummary.total) -
        (before.pullback.summary.area + restBefore.pullbackSummary.area +
          BoundaryRibbon.area before.pullback.summary.total restBefore.pullbackSummary.total)
      rw
        [differences_sum
        restBefore restAfter, Block.pullback_refinement_total before after,

          pullback_refinement_total
          restBefore restAfter]
      ring1

/-- Every actual retained interval difference satisfies the original uniform homogeneous refinement bound when its
target is at most one. -/
private theorem differences_bounded (small : target ≤ 1) : {intervals : List (CommonCover.BasisCommonInterval cover
  covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (before : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans) →
    (after : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans) →
    ∀ value ∈
      differences
      before after, Data.Gaussian.Norm.Basic.normSq value ≤
      Geometric.Basic.quarterRadius (16 * (BasisSourceCovers.primitiveSlope covers + 1)^2) coarse *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2
  | _, _, .nil, .nil, _, member => False.elim (List.not_mem_nil member)
  | _, _, .cons (request := request) before later restBefore, .cons after _ restAfter, value, member => by
      rcases List.Membership.mem_cons.mp member with same | member
      · subst value
        exact Block.pullback_refinement_uniform before after request later small
      · exact
          differences_bounded
          small restBefore restAfter value member

/-- The bound is independent of the later polynomial-dependent fine depth. -/
theorem pullback_refinement_area {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals}
    (before : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients coarse plans)
    (after : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients (coarse + fine) plans) (small
      : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (after.pullbackSummary.area - before.pullbackSummary.area) ≤
      Geometric.Basic.quarterRadius ((intervals.length : InverseRootPolynomial.Coordinate)^2 * 16 *
        (BasisSourceCovers.primitiveSlope covers + 1)^2) coarse *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (differences
    before after) _
    (differences_bounded
    small before after)
  rw
    [differences_sum,
    differences_count]
    at bound
  exact bound.trans_eq (by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow];
      ring1)

end CommonPrimitivePlans.Blocks
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPullbackRefinement
