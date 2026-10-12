module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsBoundsPart1
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsBoundsPart2
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsBoundsPart3
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsBoundsPart4
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic

/-!
# Prepared direct dyadic refinements

Checked path banks determine the original centered parents, preflight estimates
and indexed refinement certificates. The facade collects those retained
constructions and their bounds without replacing their caches.
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
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The executed checked centered parent count equals the original retained preparation's step count. -/
@[simp] theorem ofExecutedCheckedDyadic_parents_length {genus : Nat}
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
      (ofExecutedCheckedDyadic curve differential sheet checked).parents.length =
        checked.prepared.stepCount := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      simp only [ofExecutedCheckedDyadic,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        PreparedClearPathModels.PreparedPath.stepCount]
      rfl
  | cons head tail owner headWithin headSafe remaining ih =>
      simp only [ofExecutedCheckedDyadic, Append.length_append,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared,
        PreparedClearPathModels.PreparedPath.stepCount]
      rw [completeSegment_centeredEdges_length curve differential sheet _,
        ih]

/-- Recasting checked canonical parents to their original differential preserves their exact list. -/
theorem ofCheckedDyadic_recast_self {genus : Nat}
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
      (ofCheckedDyadic curve differential sheet checked).parents.map
          (recastCenteredEdge differential) =
        (ofCheckedDyadic curve differential sheet checked).parents := by
  intro ambient start finish path owner checked
  unfold ofCheckedDyadic
  exact ofPreparedPath_recast_self curve differential sheet checked.prepared

/-- Recasting executed checked canonical parents to their original differential preserves their exact list. -/
theorem ofExecutedCheckedDyadic_recast_self {genus : Nat}
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
      (ofExecutedCheckedDyadic curve differential sheet checked).parents.map
          (recastCenteredEdge differential) =
        (ofExecutedCheckedDyadic curve differential sheet checked).parents := by
  intro ambient start finish path owner checked
  induction checked with
  | nil point owner =>
      exact Eq.refl _
  | cons head tail owner headWithin headSafe remaining ih =>
      simp only [ofExecutedCheckedDyadic, Map.map_append]
      rw [completeSegment_centeredEdges_recast_self curve differential sheet _,
        ih]

/-- Read a proper centered chain from the original dyadic bank, preserving its retained form of preparation evidence.

Safe, successful, executed-certified and request-certified banks use their own original preparation and endpoint owners
to construct the exact centered parent list. -/
@[expose] def ofDyadicBank {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    CheckedDyadicCenteredState curve differential sheet start finish := by
  cases bank with
  | safe checked => exact ofCheckedDyadic curve differential sheet checked
  | executed within prepared success =>
      exact ofTryDyadic curve differential sheet depth rootDiameter
        rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic curve differential sheet checked
  | certified certificate =>
      let data := ofPreparedPath curve differential sheet certificate.prepared
      exact
        { parents := data.parents
          proper := ofPreparedPath_allParentsProper_of_allEdgesProper curve
            differential sheet certificate.prepared
              certificate.prepared_allEdgesProper
          chain := data.chain }

end

section
open Purelib.Polynomial
open Purelib.Riemann.Integration
open Purelib.Riemann.Paths
/-- The dyadic bank's real integral lower reading equals that of its exact centered parents. -/
theorem ofDyadicBank_integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    bank.integralRealLower curve differential sheet =
      PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
        (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      exact ofPreparedPath_integralRealLower curve differential sheet
        checked.prepared
  | executed within prepared success =>
      exact ofPreparedPath_integralRealLower curve differential sheet prepared
  | executedCertified checked =>
      change checked.prepared.integralRealLower curve differential sheet =
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
          (ofExecutedCheckedDyadic curve differential sheet checked).parents
      rw [ofExecutedCheckedDyadic_parents_eq_ofPreparedPath curve differential
        sheet checked]
      exact ofPreparedPath_integralRealLower curve differential sheet
        checked.prepared
  | certified certificate =>
      exact ofPreparedPath_integralRealLower curve differential sheet
        certificate.prepared

/-- The dyadic bank's prepared directional integral lower reading equals that of its exact centered parents. -/
theorem ofDyadicBank_directionalIntegralLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) (direction : Basic.Canonical)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    bank.prepared.directionalIntegralLower curve differential sheet direction =
      PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
        direction (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction checked.prepared
  | executed within prepared success =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction prepared
  | executedCertified checked =>
      change checked.prepared.directionalIntegralLower curve differential sheet
          direction =
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
          direction
            (ofExecutedCheckedDyadic curve differential sheet checked).parents
      rw [ofExecutedCheckedDyadic_parents_eq_ofPreparedPath curve differential
        sheet checked]
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction checked.prepared
  | certified certificate =>
      exact ofPreparedPath_directionalIntegralLower curve differential sheet
        direction certificate.prepared

end

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Every dyadic-bank evidence form gives the requested-diameter total weighted-allowance bound for its exact centered
parents. -/
theorem ofDyadicBank_totalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (Basic.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      dyadicPathTotalWeightedBound differential rootDiameter depth path := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_totalWeightedAllowance_le curve differential sheet
        checked
  | executed within prepared success =>
      exact ofTryDyadic_totalWeightedAllowance_le curve differential sheet
        depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_totalWeightedAllowance_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank]
      exact
        ofPreparedPath_totalWeightedAllowance_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

section
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Every dyadic-bank evidence form gives the requested-diameter natural-ceiling squared-integral sum bound. -/
theorem ofDyadicBank_integralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    Norm.Sum.Basic.gaussianNormSqSum
        ((ofDyadicBank curve differential sheet bank).parents.map
          fun parent => parent.model.integralSample) <=
      dyadicPathIntegralNormSqCeilBound differential rootDiameter depth path := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_integralNormSqSum_le curve differential sheet
        checked
  | executed within prepared success =>
      exact ofTryDyadic_integralNormSqSum_le curve differential sheet depth
        rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_integralNormSqSum_le curve differential
        sheet checked
  | certified certificate =>
      simp only [ofDyadicBank]
      exact
        ofPreparedPath_integralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- Read the weighted bound using actual cached root diameters from the bank's original preparation. -/
@[expose] def dyadicBankPreparedTotalWeightedBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Fraction.Rational :=
  match bank with
  | .safe checked =>
      preparedPathTotalWeightedBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathTotalWeightedBound differential depth prepared
  | .executedCertified checked =>
      preparedPathTotalWeightedBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathTotalWeightedBound differential depth certificate.prepared

/-- Read the upward dyadic rounded actual-cache weighted estimate of the original bank preparation. -/
@[expose] def dyadicBankPreparedTotalWeightedDyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Fraction.Rational :=
  match bank with
  | .safe checked =>
      preparedPathTotalWeightedDyadicBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathTotalWeightedDyadicBound differential depth prepared
  | .executedCertified checked =>
      preparedPathTotalWeightedDyadicBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathTotalWeightedDyadicBound differential depth
        certificate.prepared

/-- The bank's upward dyadic rounded estimate dominates its actual-cache weighted bound. -/
theorem dyadicBankPreparedTotalWeightedBound_le_dyadicBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedTotalWeightedBound differential bank <=
      dyadicBankPreparedTotalWeightedDyadicBound differential bank := by
  cases bank <;>
    exact preparedPathTotalWeightedBound_le_dyadicBound differential depth _

/-- Read the actual-cache squared-integral sum bound of the bank's original preparation. -/
@[expose] def dyadicBankPreparedIntegralNormSqSumBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Fraction.Rational :=
  match bank with
  | .safe checked =>
      preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathIntegralNormSqSumBound differential depth prepared
  | .executedCertified checked =>
      preparedPathIntegralNormSqSumBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathIntegralNormSqSumBound differential depth
        certificate.prepared

/-- Read the summed natural-ceiling actual-cache squared-integral estimate of the original bank preparation. -/
@[expose] def dyadicBankPreparedIntegralNormSqCeilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) : Fraction.Rational :=
  match bank with
  | .safe checked =>
      preparedPathIntegralNormSqCeilBound differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathIntegralNormSqCeilBound differential depth prepared
  | .executedCertified checked =>
      preparedPathIntegralNormSqCeilBound differential depth checked.prepared
  | .certified certificate =>
      preparedPathIntegralNormSqCeilBound differential depth
        certificate.prepared

/-- The natural-ceiling estimate dominates the bank's actual-cache squared-integral sum bound. -/
theorem dyadicBankPreparedIntegralNormSqSumBound_le_ceilBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedIntegralNormSqSumBound differential bank <=
      dyadicBankPreparedIntegralNormSqCeilBound differential bank := by
  cases bank <;>
    exact preparedPathIntegralNormSqSumBound_le_ceilBound differential depth _

/-- Compute both shared preflight estimates from the bank's original retained preparation.

Each evidence form retains its original prepared path, and the shared computation uses its actual segment cache
diameters. -/
@[expose] def dyadicBankPreparedPreflightBounds {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    PreparedPathPreflightBounds :=
  match bank with
  | .safe checked =>
      preparedPathPreflightBounds differential depth checked.prepared
  | .executed _within prepared _success =>
      preparedPathPreflightBounds differential depth prepared
  | .executedCertified checked =>
      preparedPathPreflightBounds differential depth checked.prepared
  | .certified certificate =>
      preparedPathPreflightBounds differential depth certificate.prepared

/-- The bank preflight weighted projection is its summed upward dyadic rounded weighted estimate. -/
@[simp] theorem dyadicBankPreparedPreflightBounds_totalWeighted {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (dyadicBankPreparedPreflightBounds differential bank).totalWeighted =
      dyadicBankPreparedTotalWeightedDyadicBound differential bank := by
  cases bank <;>
    (rewrite [dyadicBankPreparedPreflightBounds,
      dyadicBankPreparedTotalWeightedDyadicBound,
      preparedPathPreflightBounds_totalWeighted]
     exact Eq.refl _)

/-- The bank's preflight weighted projection bounds its actual-cache weighted expression. -/
theorem dyadicBankPreparedTotalWeightedBound_le_preflight {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedTotalWeightedBound differential bank <=
      (dyadicBankPreparedPreflightBounds differential bank).totalWeighted := by
  rw [dyadicBankPreparedPreflightBounds_totalWeighted]
  exact dyadicBankPreparedTotalWeightedBound_le_dyadicBound differential bank

/-- The bank preflight squared-integral projection is its summed natural-ceiling estimate. -/
@[simp] theorem dyadicBankPreparedPreflightBounds_integralNormSqSum
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (dyadicBankPreparedPreflightBounds differential bank).integralNormSqSum =
      dyadicBankPreparedIntegralNormSqCeilBound differential bank := by
  cases bank <;>
    (rewrite [dyadicBankPreparedPreflightBounds,
      dyadicBankPreparedIntegralNormSqCeilBound,
      preparedPathPreflightBounds_integralNormSqSum]
     exact Eq.refl _)

/-- The bank's preflight squared-integral projection bounds its actual-cache squared-integral expression. -/
theorem dyadicBankPreparedIntegralNormSqSumBound_le_preflight
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    dyadicBankPreparedIntegralNormSqSumBound differential bank <=
      (dyadicBankPreparedPreflightBounds differential bank).integralNormSqSum := by
  rw [dyadicBankPreparedPreflightBounds_integralNormSqSum]
  exact dyadicBankPreparedIntegralNormSqSumBound_le_ceilBound differential bank

end

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The exact centered parents of the original bank satisfy its actual-cache weighted bound. -/
theorem ofDyadicBank_preparedTotalWeightedAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (Basic.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance <=
      dyadicBankPreparedTotalWeightedBound differential bank := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_preparedTotalWeightedAllowance_le curve
        differential sheet checked
  | executed within prepared success =>
      exact ofTryDyadic_preparedTotalWeightedAllowance_le curve differential
        sheet depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_preparedTotalWeightedAllowance_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank, dyadicBankPreparedTotalWeightedBound]
      exact
        ofPreparedPath_preparedTotalWeightedAllowance_le_of_allRequestsDyadic
          curve differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

section
open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- The exact integral samples of the original bank's centered parents satisfy its actual-cache squared-integral sum
bound. -/
theorem ofDyadicBank_preparedIntegralNormSqSum_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    Norm.Sum.Basic.gaussianNormSqSum
        ((ofDyadicBank curve differential sheet bank).parents.map
          fun parent => parent.model.integralSample) <=
      dyadicBankPreparedIntegralNormSqSumBound differential bank := by
  cases bank with
  | safe checked =>
      exact ofCheckedDyadic_preparedIntegralNormSqSum_le curve differential
        sheet checked
  | executed within prepared success =>
      exact ofTryDyadic_preparedIntegralNormSqSum_le curve differential sheet
        depth rootDiameter rootDiameterPositive path within owner success
  | executedCertified checked =>
      exact ofExecutedCheckedDyadic_preparedIntegralNormSqSum_le curve
        differential sheet checked
  | certified certificate =>
      simp only [ofDyadicBank, dyadicBankPreparedIntegralNormSqSumBound]
      exact
        ofPreparedPath_preparedIntegralNormSqSum_le_of_allRequestsDyadic curve
          differential sheet depth rootDiameter rootDiameterPositive
            certificate.prepared certificate.generated

/-- The bank's exact centered parent count is the dyadic count times the original path segment count. -/
@[simp] theorem ofDyadicBank_parents_length {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (ofDyadicBank curve differential sheet bank).parents.length =
      2 ^ depth * path.segmentCount := by
  cases bank with
  | safe checked =>
      simp only [ofDyadicBank]
      rw [ofCheckedDyadic_parents_length,
        PreparedClearPathModels.PreparedPath.CheckedDyadic.prepared_stepCount]
  | executed within prepared success =>
      change (ofPreparedPath curve differential sheet prepared).parents.length =
        2 ^ depth * path.segmentCount
      rw [ofPreparedPath_parents_length,
        PreparedClearPathModels.PreparedPath.tryDyadic_stepCount
          path within owner depth rootDiameter rootDiameterPositive success]
  | executedCertified checked =>
      simp only [ofDyadicBank]
      rw [ofExecutedCheckedDyadic_parents_length,
        PreparedClearPathModels.PreparedPath.ExecutedCheckedDyadic.prepared_stepCount]
  | certified certificate =>
      change
        (ofPreparedPath curve differential sheet
          certificate.prepared).parents.length = _
      rw [ofPreparedPath_parents_length, certificate.prepared_stepCount]

end

open Purelib.Polynomial in
/-- The requested-diameter path weighted bound multiplied by the exact dyadic cell count across all original segments.
-/
@[expose] def dyadicPathAggregateBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    (rootDiameter : Fraction.Rational) (depth : Nat)
    {ambient : Box} {start finish : Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish) : Fraction.Rational :=
  ((2 ^ depth * path.segmentCount : Nat) : Fraction.Rational) *
    dyadicPathTotalWeightedBound differential rootDiameter depth path

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The original bank's centered model aggregate allowance satisfies the requested-diameter path aggregate bound. -/
theorem ofDyadicBank_aggregateAllowance_le {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (Basic.PathModel.mk
      ((ofDyadicBank curve differential sheet bank).parents.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      dyadicPathAggregateBound differential rootDiameter depth path := by
  unfold Basic.PathModel.aggregateAllowance
    dyadicPathAggregateBound
  rw [Map.length_map, ofDyadicBank_parents_length]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (ofDyadicBank_totalWeightedAllowance_le curve differential sheet bank)
    (acceptedCoordinateNatCast_nonnegative _)

open Purelib.Polynomial
open Purelib.Riemann.Paths
/-- Recasting the bank's canonical centered parents to their original differential preserves their exact list. -/
theorem ofDyadicBank_recast_self {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (bank : PreparedClearPathModels.PreparedPath.DyadicBank depth
      rootDiameter rootDiameterPositive path owner) :
    (ofDyadicBank curve differential sheet bank).parents.map
        (recastCenteredEdge differential) =
      (ofDyadicBank curve differential sheet bank).parents := by
  cases bank with
  | safe checked =>
      simp only [ofDyadicBank]
      exact ofCheckedDyadic_recast_self curve differential sheet checked
  | executed within prepared success =>
      change (ofPreparedPath curve differential sheet prepared).parents.map
          (recastCenteredEdge differential) =
        (ofPreparedPath curve differential sheet prepared).parents
      exact ofPreparedPath_recast_self curve differential sheet prepared
  | executedCertified checked =>
      simp only [ofDyadicBank]
      exact ofExecutedCheckedDyadic_recast_self curve differential sheet
        checked
  | certified certificate =>
      change
        (ofPreparedPath curve differential sheet certificate.prepared).parents.map
            (recastCenteredEdge differential) =
          (ofPreparedPath curve differential sheet certificate.prepared).parents
      exact ofPreparedPath_recast_self curve differential sheet
        certificate.prepared

/-- Package the original checked dyadic centered chain and its properness as a direct refinement state. -/
@[expose] def stateOfCheckedDyadic {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (sheet : Fin 2) {depth : Nat} {rootDiameter : Fraction.Rational}
    {rootDiameterPositive : 0 < rootDiameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)}
    (checked :
      PreparedClearPathModels.PreparedPath.CheckedDyadic depth
        rootDiameter rootDiameterPositive path owner) :
    DirectRefinementState curve differential :=
  let state := ofCheckedDyadic curve differential sheet checked
  state.chain.toDirectRefinementState state.proper

end

end CenteredPathChain

namespace DirectBlockRefinement

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Geometry.Path.Gaussian in
/-- Concatenate the lifted paths retained by the direct parent blocks along the original centered chain.

The result keeps the original lifted endpoint indices and uses each block's retained path in original parent order. -/
@[expose] def refinedPath {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (_blocks : DirectBlockRefinement parents)
      (_chain : CenteredPathChain parents (start := start) (finish := finish)),
      Lifted.Basic.LiftedPath 2 start finish
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain =>
      block.lifted.append (refinedPath tailBlocks tailChain)

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Riemann.Integration in
/-- Concatenate the retained block certificates on their exact refined lifted path.

The certified cells are the model projection of the exact concatenated child list, with no replacement of the parent
blocks. -/
@[expose] def refinedCertificates {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (blocks : DirectBlockRefinement parents)
      (chain : CenteredPathChain parents (start := start) (finish := finish)),
      Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve differential
        (blocks.children.map
          PreparedSubdivisionModelCore.CenteredEdge.model)
        (blocks.refinedPath chain)
  | [], _, _, .nil, .nil point => .nil point
  | _ :: _, _, _, .cons block tailBlocks, .cons _ tailChain => by
      simpa only [children, Map.map_append, refinedPath] using
        Curves.Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates.append block.lifted
          block.certificates
          (refinedCertificates tailBlocks tailChain)

end DirectBlockRefinement

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Construct a direct child block for each original proper parent at the requested positive root diameter.

Each parent chooses its own sufficient depth; the dependent list retains the original parent order and each block's root
and displacement certificates. -/
@[expose] def directBlockRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) ->
    PreparedDyadicRefinements.AllParentsProper parents ->
      DirectBlockRefinement parents
  | [], _proper => .nil
  | parent :: remaining, proper =>
      .cons
        (directParentBlock parent proper.1 rootDiameter rootDiameterPositive)
        (directBlockRefinement rootDiameter rootDiameterPositive remaining
          proper.2)

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- The exact child list and its centered-edge refinement from the original parents.

The dependent refinement retains the original root comparisons and displacement equalities for these children. -/
structure DirectRefinementResult {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parents : List (CenteredEdge curve differential)) where
  /-- The exact ordered centered children retained by the direct refinement. -/ children : List (CenteredEdge curve
    differential)
  /-- The centered-edge refinement relating these children to the original parent list. -/ refinement :
    PreparedSubdivisionModelCore.CenteredEdgeRefinement
    parents children

constructive_injectivity DirectRefinementResult

namespace DirectRefinementResult

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann.Integration in
/-- Read the compatible constant-path refinement between the original parent models and exact retained child models. -/
@[expose] def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    (result : DirectRefinementResult parents) :
    CompatibleConstantPathRefinement
      (parents.map PreparedSubdivisionModelCore.CenteredEdge.model)
      (result.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model) :=
  result.refinement.toCompatible

end DirectRefinementResult

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
/-- Construct the direct parent blocks and retain their exact concatenated children and centered-edge refinement. -/
@[expose] def directRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (rootDiameter : Fraction.Rational) (rootDiameterPositive : 0 < rootDiameter) :
    (parents : List (CenteredEdge curve differential)) ->
    PreparedDyadicRefinements.AllParentsProper parents ->
      DirectRefinementResult parents
  | parents, proper =>
      let blocks := directBlockRefinement rootDiameter rootDiameterPositive
        parents proper
      { children := blocks.children
        refinement := blocks.toCenteredEdgeRefinement }

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
