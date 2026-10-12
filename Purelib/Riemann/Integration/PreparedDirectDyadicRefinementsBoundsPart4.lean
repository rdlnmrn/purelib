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
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic

/-!
# Direct dyadic refinement estimates, part 4

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
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- A prepared path with the stated dyadic request lists satisfies the requested-diameter weighted-allowance bound.

The request equalities identify each original segment's dyadic count and movement bounds without rerunning the retained
preparation. -/
theorem ofPreparedPath_totalWeightedAllowance_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        (Basic.PathModel.mk
          ((ofPreparedPath curve differential sheet prepared).parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner =>
      intro _generated
      simp only [ofPreparedPath, dyadicPathTotalWeightedBound, List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      intro generated
      change preparedHead.subdivision.requests =
          PreparedSheetContinuation.Subdivision.dyadicRequests depth
            PreparedClearPathModels.zeroEndpoint
              PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathTotalWeightedBound]
      change
        (Basic.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          completeDyadicTotalWeightedBound differential head rootDiameter
              depth +
            dyadicPathTotalWeightedBound differential rootDiameter depth tail
      rw [Map.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completePreparedSegment_totalWeightedAllowance_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            preparedHead generated.1)
        (ih generated.2)

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
/-- A prepared path with the stated dyadic requests satisfies the requested-diameter natural-ceiling squared-integral
bound.

Each original segment's actual integral samples are bounded from its request equality, then by the corresponding ceiling
estimate, before adding along the original path. -/
theorem ofPreparedPath_integralNormSqSum_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        Norm.Sum.Basic.gaussianNormSqSum
            ((ofPreparedPath curve differential sheet prepared).parents.map
              fun parent => parent.model.integralSample) <=
          dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner =>
      intro _generated
      simp only [ofPreparedPath, dyadicPathIntegralNormSqCeilBound,
        List.map_nil, Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      intro generated
      change preparedHead.subdivision.requests =
          PreparedSheetContinuation.Subdivision.dyadicRequests depth
            PreparedClearPathModels.zeroEndpoint
              PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        dyadicPathIntegralNormSqCeilBound]
      change
        Norm.Sum.Basic.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completeDyadicIntegralNormSqCeilBound differential head rootDiameter
              depth +
            dyadicPathIntegralNormSqCeilBound differential rootDiameter depth
              tail
      rw [Map.map_append, gaussianNormSqSum_append]
      exact add_le_add
        ((completePreparedSegment_integralNormSqSum_le curve differential head
          headWithin owner sheet depth rootDiameter rootDiameterPositive
            preparedHead generated.1).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        (ih generated.2)

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- A prepared path with the stated dyadic requests satisfies the weighted bound using its actual cached root diameters.

Request equalities supply geometry and counts; the root-error estimates use the exact original prepared segment caches.
-/
theorem ofPreparedPath_preparedTotalWeightedAllowance_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        (Basic.PathModel.mk
          ((ofPreparedPath curve differential sheet prepared).parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          preparedPathTotalWeightedBound differential depth prepared := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner =>
      intro _generated
      simp only [ofPreparedPath, preparedPathTotalWeightedBound, List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      intro generated
      change preparedHead.subdivision.requests =
          PreparedSheetContinuation.Subdivision.dyadicRequests depth
            PreparedClearPathModels.zeroEndpoint
              PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathTotalWeightedBound]
      change
        (Basic.PathModel.mk
          ((preparedHead.centeredEdges curve differential sheet ++
            tailState.parents).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
          completePreparedDyadicTotalWeightedBound differential head headWithin
              owner preparedHead depth +
            preparedPathTotalWeightedBound differential depth preparedTail
      rw [Map.map_append, totalWeightedAllowance_append]
      exact add_le_add
        (completePreparedSegment_preparedTotalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive preparedHead generated.1)
        (ih generated.2)

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
/-- A prepared path with the stated dyadic requests satisfies the actual-cache squared-integral sum bound.

The original centered parent list is retained, with each segment's root-error contribution determined by its own cached
diameter maximum. -/
theorem ofPreparedPath_preparedIntegralNormSqSum_le_of_allRequestsDyadic
    {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive prepared ->
        Norm.Sum.Basic.gaussianNormSqSum
            ((ofPreparedPath curve differential sheet prepared).parents.map
              fun parent => parent.model.integralSample) <=
          preparedPathIntegralNormSqSumBound differential depth prepared := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner =>
      intro _generated
      simp only [ofPreparedPath, preparedPathIntegralNormSqSumBound,
        List.map_nil, Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      intro generated
      change preparedHead.subdivision.requests =
          PreparedSheetContinuation.Subdivision.dyadicRequests depth
            PreparedClearPathModels.zeroEndpoint
              PreparedClearPathModels.oneEndpoint rootDiameter
                rootDiameterPositive ∧
        PreparedClearPathModels.PreparedPath.AllRequestsDyadic depth
          rootDiameter rootDiameterPositive preparedTail at generated
      let tailState := ofPreparedPath curve differential sheet preparedTail
      simp only [ofPreparedPath, dataOfCompleteSegment_parents,
        preparedPathIntegralNormSqSumBound]
      change
        Norm.Sum.Basic.gaussianNormSqSum
            ((preparedHead.centeredEdges curve differential sheet ++
              tailState.parents).map
                fun parent => parent.model.integralSample) <=
          completePreparedDyadicIntegralNormSqSumBound differential head
              headWithin owner preparedHead depth +
            preparedPathIntegralNormSqSumBound differential depth preparedTail
      rw [Map.map_append, gaussianNormSqSum_append]
      exact add_le_add
        (completePreparedSegment_preparedIntegralNormSqSum_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive preparedHead generated.1)
        (ih generated.2)

end

end CenteredPathChain

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
