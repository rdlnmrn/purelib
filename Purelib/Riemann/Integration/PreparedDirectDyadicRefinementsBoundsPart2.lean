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
import Mathlib.Order.Basic

/-!
# Direct dyadic refinement estimates, part 2

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
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- An executed checked dyadic path satisfies the requested-diameter total weighted-allowance bound.

The proof follows the original executed subdivisions and combines their complete-segment bounds on the exact retained
centered parent list. -/
theorem ofExecutedCheckedDyadic_totalWeightedAllowance_le {genus : Nat}
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
        dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofExecutedCheckedDyadic, dyadicPathTotalWeightedBound,
        List.map_nil,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic, dyadicPathTotalWeightedBound]
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

open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- A successful dyadic path preparation satisfies the summed natural-ceiling squared-integral estimate at the requested
diameter.

Each retained segment's actual integral samples first satisfy its requested-diameter bound, which is then bounded by its
natural-ceiling residual estimate before summing along the original path. -/
theorem ofTryDyadic_integralNormSqSum_le {genus : Nat}
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
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  intro ambient start finish path
  induction path with
  | nil point =>
      intro _within owner _prepared success
      simp only
        [PreparedClearPathModels.PreparedPath.tryDyadic] at success
      have preparedEqual := Option.some.inj success
      subst _prepared
      simp only [ofTryDyadic, ofPreparedPath,
        dyadicPathIntegralNormSqCeilBound, List.map_nil,
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
            dyadicPathIntegralNormSqCeilBound]
          rw [dataOfCompleteSegment_parents]
          change
            Norm.Sum.Basic.gaussianNormSqSum
                ((preparedHead.centeredEdges curve differential sheet ++
                  tailCentered.parents).map
                    fun parent => parent.model.integralSample) <=
              completeDyadicIntegralNormSqCeilBound differential head
                  rootDiameter depth +
                dyadicPathIntegralNormSqCeilBound differential rootDiameter
                  depth tail
          rw [Map.map_append, gaussianNormSqSum_append]
          exact add_le_add
            ((completeSegmentOfTryDyadic_integralNormSqSum_le curve
              differential head within.head owner sheet depth rootDiameter
                rootDiameterPositive headSuccess).trans
              (completeDyadicIntegralNormSqSumBound_le_ceilBound differential
                head rootDiameterPositive.le depth))
            (ih within.tail preparedHead.finishOwner tailSuccess)

/-- A checked dyadic path satisfies the requested-diameter natural-ceiling bound for the sum of squared integral
samples.

The exact centered parents are read from the retained safe segment preparations; the bound adds their complete-segment
estimates in original path order. -/
theorem ofCheckedDyadic_integralNormSqSum_le {genus : Nat}
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
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofCheckedDyadic,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared,
        ofPreparedPath, dyadicPathIntegralNormSqCeilBound, List.map_nil,
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
        ((completeSegmentOfTryDyadic_integralNormSqSum_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            _).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        ih

/-- An executed checked dyadic path satisfies the requested-diameter natural-ceiling squared-integral bound.

The directly constructed centered parents use the original executed segment subdivisions and finish owners, whose
individual bounds add along the path. -/
theorem ofExecutedCheckedDyadic_integralNormSqSum_le {genus : Nat}
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
        dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofExecutedCheckedDyadic, dyadicPathIntegralNormSqCeilBound,
        List.map_nil, Norm.Sum.Basic.gaussianNormSqSum]
      exact le_rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      let preparedHead :=
        PreparedClearPathModels.CompleteSegment.ofExecutedDyadic
          head headWithin owner depth rootDiameter rootDiameterPositive headSafe
      let tailState := ofExecutedCheckedDyadic curve differential sheet
        remaining
      simp only [ofExecutedCheckedDyadic, dyadicPathIntegralNormSqCeilBound]
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
        ((completeSegmentOfTryDyadic_integralNormSqSum_le curve differential
          head headWithin owner sheet depth rootDiameter rootDiameterPositive
            _).trans
          (completeDyadicIntegralNormSqSumBound_le_ceilBound differential head
            rootDiameterPositive.le depth))
        ih

end

end CenteredPathChain

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
