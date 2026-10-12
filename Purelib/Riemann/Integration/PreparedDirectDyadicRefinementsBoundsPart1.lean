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
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Direct dyadic refinement estimates, part 1

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
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- A successful prepared dyadic path satisfies the squared-integral sum bound computed from its actual cached root
diameters.

The original success equation determines every retained segment preparation and centered parent; the proof adds the
corresponding complete-segment bounds in path order. -/
theorem ofTryDyadic_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : PreparedClearPathModels.PreparedPath path owner}
      (success :
        PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      Norm.Sum.Basic.gaussianNormSqSum
          ((ofTryDyadic curve differential sheet depth rootDiameter
            rootDiameterPositive path within owner success).parents.map
              fun parent => parent.model.integralSample) <=
        preparedPathIntegralNormSqSumBound differential depth prepared := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within owner _prepared success
      simp only
        [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        preparedPathIntegralNormSqSumBound, List.map_nil,
        Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail ih =>
      intro within owner _prepared success
      rw [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            preparedPathIntegralNormSqSumBound]
          rw [dataOfCompleteSegment_parents]
          change
            Norm.Sum.Basic.gaussianNormSqSum
                ((preparedHead.centeredEdges curve differential sheet ++
                  tailCentered.parents).map
                    fun parent => parent.model.integralSample) <=
              completePreparedDyadicIntegralNormSqSumBound differential head
                  within.head owner preparedHead depth +
                preparedPathIntegralNormSqSumBound differential depth
                  preparedTail
          rw [Map.map_append, gaussianNormSqSum_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_preparedIntegralNormSqSum_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ih within.tail preparedHead.finishOwner tailSuccess)

open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
/-- A successful prepared dyadic path satisfies the weighted-allowance bound computed from its actual cached root
diameters.

The original path's centered parents are split at the retained segment boundaries, so their weighted allowance is the
sum of the same complete-segment contributions. -/
theorem ofTryDyadic_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : PreparedClearPathModels.PreparedPath path owner}
      (success :
        PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      (Basic.PathModel.mk
        ((ofTryDyadic curve differential sheet depth rootDiameter
          rootDiameterPositive path within owner success).parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
        preparedPathTotalWeightedBound differential depth prepared := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within owner _prepared success
      simp only
        [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        preparedPathTotalWeightedBound,
        Basic.PathModel.totalWeightedAllowance,
        List.map_nil, List.foldr_nil]
      exact le_rfl
  | cons head tail ih =>
      intro within owner _prepared success
      rw [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            preparedPathTotalWeightedBound]
          rw [dataOfCompleteSegment_parents]
          change
            (Basic.PathModel.mk
              ((preparedHead.centeredEdges curve differential sheet ++
                tailCentered.parents).map
                  PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
              completePreparedDyadicTotalWeightedBound differential head
                  within.head owner preparedHead depth +
                preparedPathTotalWeightedBound differential depth preparedTail
          rw [Map.map_append, totalWeightedAllowance_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_preparedTotalWeightedAllowance_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ih within.tail preparedHead.finishOwner tailSuccess)

/-- A successful prepared dyadic path satisfies the total weighted bound at the requested root diameter and depth.

The success equation identifies the original centered parent list; each segment uses the same requested numerical
parameters and the exact original finish owner passed to its tail. -/
theorem ofTryDyadic_totalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (depth : Nat) (rootDiameter : Fraction.Rational)
    (rootDiameterPositive : 0 < rootDiameter) :
    forall {ambient : Box} {start finish : Basic.Canonical}
      (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient)
      (owner : Owner (curve.polynomial.eval start))
      {prepared : PreparedClearPathModels.PreparedPath path owner}
      (success :
        PreparedClearPathModels.PreparedPath.tryDyadic path within
            owner depth rootDiameter rootDiameterPositive = some prepared),
      (Basic.PathModel.mk
        ((ofTryDyadic curve differential sheet depth rootDiameter
          rootDiameterPositive path within owner success).parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
        dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within owner _prepared success
      simp only
        [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath, dyadicPathTotalWeightedBound,
        Basic.PathModel.totalWeightedAllowance,
        List.map_nil, List.foldr_nil]
      exact le_rfl
  | cons head tail ih =>
      intro within owner _prepared success
      rw [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      split at success
      next => contradiction
      next subdivision headSuccess =>
        simp only at success
        split at success
        next => contradiction
        next preparedTail tailSuccess =>
          have preparedEqual := Option.some.inj success
          subst _prepared
          let preparedHead :=
            PreparedClearPathModels.CompleteSegment.ofTryDyadic
              head within.head owner depth rootDiameter rootDiameterPositive
                headSuccess
          let tailCentered := ofPreparedPath curve differential sheet
            preparedTail
          simp only [ofTryDyadic, ofPreparedPath,
            dyadicPathTotalWeightedBound]
          rw [dataOfCompleteSegment_parents]
          change
            (Basic.PathModel.mk
              ((preparedHead.centeredEdges curve differential sheet ++
                tailCentered.parents).map
                  PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
              completeDyadicTotalWeightedBound differential head rootDiameter
                  depth +
                dyadicPathTotalWeightedBound differential rootDiameter depth
                  tail
          rw [Map.map_append, totalWeightedAllowance_append]
          exact add_le_add
            (completeSegmentOfTryDyadic_totalWeightedAllowance_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess)
            (ih within.tail preparedHead.finishOwner tailSuccess)

/-- A checked dyadic path satisfies the requested-diameter total weighted-allowance bound.

The retained mesh-safety evidence supplies the original complete prepared segments, whose bounds add along the exact
centered parent list. -/
theorem ofCheckedDyadic_totalWeightedAllowance_le {genus : Nat}
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
        dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dyadicPathTotalWeightedBound, List.map_nil,
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
        (completeSegmentOfTryDyadic_totalWeightedAllowance_le curve
          differential head headWithin owner sheet depth rootDiameter
            rootDiameterPositive _)
        ih

end

end CenteredPathChain

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
