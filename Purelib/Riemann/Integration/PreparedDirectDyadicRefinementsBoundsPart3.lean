module

import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

/-!
# Direct dyadic refinement estimates, part 3

The bounds retain the original prepared child lists and cached scalar estimates.
They compare those same finite refinements at their displayed requests.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Data.List

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedEdgeRecasting
  (Owner Endpoint StepRequest CenteredEdge directRequest recastCenteredEdge recastPreparedEdge
    recastCenteredEdge_segment recastCenteredEdge_request recastCenteredEdge_left
    recastPreparedEdge_self CompatibleConstantPathRefinement)
open Purelib.Geometry.Rational (Box)

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
private abbrev Gaussian := Basic.Canonical

namespace CenteredPathChain

section
open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
section
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
/-- A checked dyadic path satisfies the weighted-allowance bound computed from its actual cached root diameters.

The exact canonical centered parent list is obtained from the retained safe segment preparations, whose bounds add in
original path order. -/
theorem ofCheckedDyadic_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      (Basic.PathModel.mk
        ((ofCheckedDyadic curve differential sheet checked).parents.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth checked.prepared := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, preparedPathTotalWeightedBound, List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathTotalWeightedBound]
      change
        (Basic.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth
              remaining.prepared
      rw [Map.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        ih

/-- An executed checked dyadic path satisfies the actual-cache weighted-allowance bound.

The directly constructed centered state retains every executed subdivision; its segment allowances are bounded using
those same cached root diameters. -/
theorem ofExecutedCheckedDyadic_preparedTotalWeightedAllowance_le
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      (Basic.PathModel.mk
        ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth checked.prepared := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathTotalWeightedBound, List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathTotalWeightedBound]
      change
        (Basic.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth
              remaining.prepared
      rw [Map.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        ih

end

open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A checked dyadic path satisfies the squared-integral sum bound computed from its actual cached root diameters.

The proof sums the bounds for the exact integral samples of the retained safe complete-segment preparations. -/
theorem ofCheckedDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        PreparedClearPathModels.PreparedPath.CheckedDyadic depth
          rootDiameter rootDiameterPositive path owner),
      Norm.Sum.Basic.gaussianNormSqSum
          ((ofCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth checked.prepared := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, preparedPathIntegralNormSqSumBound, List.map_nil,
        Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofSafeDyadic head
          headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofCheckedDyadic curve differential sheet remaining
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathIntegralNormSqSumBound]
      change
        Norm.Sum.Basic.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth
              remaining.prepared
      rw [Map.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        ih

/-- An executed checked dyadic path satisfies the actual-cache squared-integral sum bound.

Each head uses its retained executed subdivision and actual root-diameter maximum before the bound is added to that of
the original prepared tail. -/
theorem ofExecutedCheckedDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter} :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (checked :
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic
          depth rootDiameter rootDiameterPositive path owner),
      Norm.Sum.Basic.gaussianNormSqSum
          ((ofExecutedCheckedDyadic curve differential sheet checked).parents.map
            fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth checked.prepared := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathIntegralNormSqSumBound, List.map_nil,
        Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        preparedPathIntegralNormSqSumBound]
      change
        Norm.Sum.Basic.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth
              remaining.prepared
      rw [Map.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        ih

end

end CenteredPathChain

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
