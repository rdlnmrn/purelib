module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

import Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace
public import Purelib.Riemann.Paths.PreparedTraceClearance
public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

@[expose] public section

/-!
# Automatic common budgets for prepared square-root traces

The segment's positive polynomial clearance gives a root-norm lower bound
uniform over every owner and every displayed root reading on that segment.
Choose the root-box diameter and radicand variation from that common bound,
then compute one dyadic depth that also pays the ordinary prepared-continuation
clearance floor.  No successful search or caller-selected refinement is needed.
-/

namespace Purelib.Riemann.Paths

open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerApproximation)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)

namespace PreparedTraceBudget

/-- The original rational Gaussian box carrier. -/
abbrev Box := Purelib.Geometry.Rational.Box

end PreparedTraceBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- Cached root-reading and movement budgets for an original prepared segment interval.

The retained clearance cover supplies a positive root-norm lower bound. Exact equations keep the root diameter, movement
allowance, prepared clearance floor, original variation and chosen dyadic depth with its strict leaf bound. -/
structure PreparedTraceBudget {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : PreparedTraceBudget.Box}
    {start finish : Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint) where
  /-- The retained exact trace-clearance cache for the original segment. -/ clearance :
    PreparedTraceClearance segment
  /-- The cache equals the original trace-clearance builder on that segment. -/ clearance_eq : clearance =
    PreparedTraceClearance.build segment
  /-- The retained positive uniform squared-norm lower bound for original root readings. -/ lower : Fraction.Rational
  /-- The lower bound is the exact maximum of the capped segment and cached coordinate-clearance bounds. -/ lower_eq :
    lower = max (min 1 (segment.clearanceBound / 4))
    (min 1 (clearance.cover.coordinateFloor / 2))
  /-- The retained root-reading lower bound is strictly positive. -/ lower_positive : 0 < lower
  /-- The retained positive original root-diameter request. -/ rootDiameter : Fraction.Rational
  /-- The diameter equals the retained lower bound divided by 1024. -/ rootDiameter_eq : rootDiameter = lower / 1024
  /-- The retained root-diameter request is strictly positive. -/ rootDiameter_positive : 0 < rootDiameter
  /-- The retained positive allowance on original parameter movement. -/ movementBudget : Fraction.Rational
  /-- The movement allowance equals the retained lower bound squared divided by 1024. -/ movementBudget_eq :
    movementBudget = lower ^ 2 / 1024
  /-- The retained movement allowance is strictly positive. -/ movementBudget_positive : 0 < movementBudget
  /-- The cached uniform prepared clearance floor at the exact retained diameter. -/ clearanceFloor : Fraction.Rational
  /-- The cache equals the original segment's prepared-clearance floor construction. -/ clearanceFloor_eq :
    clearanceFloor =
    PreparedSheetContinuation.uniformPreparedClearanceFloor segment rootDiameter
  /-- The retained uniform prepared-clearance floor is strictly positive. -/ clearanceFloor_positive : 0 <
    clearanceFloor
  /-- The cached original segment variation between the exact retained endpoint parameters. -/ variation :
    Fraction.Rational
  /-- The cache equals the original variation-bound formula at those endpoints. -/ variation_eq : variation =
    ClearSheetContinuation.variationBound segment left.parameter right.parameter
  /-- The retained dyadic depth selected to meet both original clearance and movement targets. -/ depth : Nat
  /-- The cached original geometric variation at the retained depth. -/ leafVariation : Fraction.Rational
  /-- The cache equals the original variation's exact quarter-radius schedule at that depth. -/ leafVariation_eq :
    leafVariation = Geometric.Basic.quarterRadius variation depth
  /-- The retained leaf variation is strictly below both original clearance and movement bounds. -/ leafSmall :
    leafVariation < min clearanceFloor movementBudget

constructive_injectivity PreparedTraceBudget

namespace PreparedTraceBudget

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish} {left right : Endpoint}

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Cache the original trace clearance and choose a dyadic depth paying both prepared clearance and root movement
budgets.

The positive lower bound combines the original segment and cached coordinate clearances; its exact diameter and squared
movement targets determine the retained geometric search. -/
def build (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (left right : Endpoint) :
    PreparedTraceBudget segment left right := by
  let clearance := PreparedTraceClearance.build segment
  let lower : Fraction.Rational := max (min 1 (segment.clearanceBound / 4))
    (min 1 (clearance.cover.coordinateFloor / 2))
  have lowerPositive : 0 < lower := (Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct segment.clearanceBound_positive (by decide))).trans_le
      (Fraction.Order.Basic.le_max_left _ _)
  let rootDiameter : Fraction.Rational := lower / 1024
  have diameterPositive : 0 < rootDiameter := Fraction.Order.Field.div_pos_direct lowerPositive (by decide +kernel)
  let movement : Fraction.Rational := lower ^ 2 / 1024
  have movementPositive : 0 < movement := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct lowerPositive 2) (by decide +kernel)
  let clearanceFloor := PreparedSheetContinuation.uniformPreparedClearanceFloor segment rootDiameter
  have clearancePositive : 0 < clearanceFloor :=
    PreparedSheetContinuation.uniformPreparedClearanceFloor_positive segment diameterPositive
  let variation := ClearSheetContinuation.variationBound segment left.parameter right.parameter
  let target := min clearanceFloor movement
  let depth := Geometric.Search.firstQuarterBelow variation 0 target
  exact
    { clearance := clearance
      clearance_eq := rfl
      lower := lower
      lower_eq := rfl
      lower_positive := lowerPositive
      rootDiameter := rootDiameter
      rootDiameter_eq := rfl
      rootDiameter_positive := diameterPositive
      movementBudget := movement
      movementBudget_eq := rfl
      movementBudget_positive := movementPositive
      clearanceFloor := clearanceFloor
      clearanceFloor_eq := rfl
      clearanceFloor_positive := clearancePositive
      variation := variation
      variation_eq := rfl
      depth := depth
      leafVariation := Geometric.Basic.quarterRadius variation depth
      leafVariation_eq := rfl
      leafSmall := Geometric.Search.firstQuarterBelow_accurate variation
        (ClearSheetContinuation.variationBound_nonneg segment _ _) 0 target
        (Fraction.Order.Basic.lt_min clearancePositive movementPositive) }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Every sample of an original root owner along the retained segment satisfies the cached trace lower bound.

The original segment and cached coordinate clearances supply the two capped lower bounds. The same owner reading
satisfies both through its retained square-root certificate and the exact polynomial evaluation along the segment. -/
theorem root_lower (budget : PreparedTraceBudget segment left right)
    (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) (index : Nat) :
    budget.lower ≤ normSq ((ownerApproximation owner).sample index) := by
  have parameterLower := segment.clearanceBound_le_eval_normSq
    (segment.pointAt_onCertifiedLine parameter inside)
  rw [Norm.Basic.normSq_eq_canonical] at parameterLower
  have quarterLower : segment.clearanceBound / 4 ≤ normSq (polynomial.eval (segment.pointAt parameter)) / 4 := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (4 : Fraction.Rational) ≠ 0)]
    exact parameterLower
  apply le_trans _ (CertifiedSquareRoot.sample_norm_lower owner.parameterNonzero owner.track index)
  rw [budget.lower_eq]
  apply Fraction.Order.Basic.max_le
  · apply le_trans _ (Fraction.Order.Basic.le_max_left _ _)
    exact Fraction.Order.Basic.le_min (Fraction.Order.Basic.min_le_left _ _) ((Fraction.Order.Basic.min_le_right _
      _).trans quarterLower)
  · apply le_trans _ (Fraction.Order.Basic.le_max_right _ _)
    apply (Fraction.Order.Basic.min_le_right _ _).trans
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 2)).mpr
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (2 : Fraction.Rational) ≠ 0)]
    exact budget.clearance.coordinate_le parameter inside

open Purelib.Riemann.Branches in
open Purelib.Data.Rat in
/-- The retained depth and root diameter certify the original ordered dyadic mesh as safe for its starting owner. -/
theorem meshSafe (budget : PreparedTraceBudget segment left right)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (ordered : left.parameter ≤ right.parameter) :
    PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment left right owner
      budget.depth budget.rootDiameter budget.rootDiameter_positive := by
  apply PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_variation_lt_predictedClearanceFloor
    segment left right owner budget.depth budget.rootDiameter budget.rootDiameter_positive ordered
  have small := budget.leafSmall.trans_le (Fraction.Order.Basic.min_le_left budget.clearanceFloor budget.movementBudget)
  rw [budget.leafVariation_eq, budget.variation_eq, budget.clearanceFloor_eq] at small
  exact small.trans_le
    (PreparedSheetContinuation.Subdivision.uniformPreparedClearanceFloor_le_dyadicPredicted
      segment left right owner budget.depth budget.rootDiameter budget.rootDiameter_positive)

section
open Purelib.Riemann.Branches
/-- Construct the original checked dyadic subdivision using the retained depth, diameter and mesh-safety certificate. -/
def prepare (budget : PreparedTraceBudget segment left right) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (ordered : left.parameter ≤ right.parameter) :
    PreparedSheetContinuation.Subdivision segment within left owner :=
  PreparedSheetContinuation.Subdivision.checkedDyadic segment within left right owner
    budget.depth budget.rootDiameter budget.rootDiameter_positive (budget.meshSafe owner ordered)

/-- Each retained request stays within the original root-diameter and source-to-endpoint variation budgets, in exact
request order. -/
def RequestsFit (budget : PreparedTraceBudget segment left right) :
    Endpoint → List PreparedSheetContinuation.StepRequest → Prop
  | _, [] => True
  | current, request :: remaining =>
      request.rootDiameter ≤ budget.rootDiameter ∧
        ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter ≤ budget.movementBudget ∧
        RequestsFit budget request.endpoint remaining

end

open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- A retained endpoint variation bound and diameter bound certify every original request made at that same diameter. -/
private theorem requestsAtDiameter_fit (budget : PreparedTraceBudget segment left right)
    {diameter bound : Fraction.Rational} (positive : 0 < diameter) (small : diameter ≤ budget.rootDiameter)
    (boundLe : bound ≤ budget.movementBudget) :
    ∀ (current : Endpoint) (endpoints : List Endpoint),
      ClearSheetContinuation.Subdivision.EdgeVariationBound segment bound current endpoints →
      budget.RequestsFit current
        (PreparedSheetContinuation.Subdivision.requestsAtDiameter
          diameter positive endpoints)
  | _, [], _ => trivial
  | _current, endpoint :: remaining, bounds =>
      ⟨small, bounds.2.1.trans boundLe,
        requestsAtDiameter_fit budget positive small boundLe endpoint remaining bounds.2.2⟩

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- Original dyadic requests fit the retained trace budget when their diameter and geometric variation satisfy the
supplied bounds. -/
theorem dyadicRequests_fit_of_variation (budget : PreparedTraceBudget segment left right)
    (ordered : left.parameter ≤ right.parameter) (depth : Nat) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (small : diameter ≤ budget.rootDiameter)
    (movement : Geometric.Basic.quarterRadius budget.variation depth ≤ budget.movementBudget) :
    budget.RequestsFit left
      (PreparedSheetContinuation.Subdivision.dyadicRequests depth left right diameter positive) := by
  rw [budget.variation_eq] at movement
  exact requestsAtDiameter_fit budget positive small movement left _
    (ClearSheetContinuation.Subdivision.dyadicTargets_edgeVariationBound segment depth left right ordered)

open Purelib.Riemann.Branches in
open Purelib.Data.Rat in
/-- The retained budget's exact chosen dyadic requests satisfy both original diameter and movement allowances. -/
theorem dyadicRequests_fit (budget : PreparedTraceBudget segment left right)
    (ordered : left.parameter ≤ right.parameter) :
    budget.RequestsFit left
      (PreparedSheetContinuation.Subdivision.dyadicRequests budget.depth left right
        budget.rootDiameter budget.rootDiameter_positive) := by
  exact budget.dyadicRequests_fit_of_variation ordered budget.depth budget.rootDiameter
    budget.rootDiameter_positive le_rfl (by
      rw [← budget.leafVariation_eq]
      exact budget.leafSmall.le.trans (Fraction.Order.Basic.min_le_right _ _))

open Purelib.Riemann.Branches in
/-- Every request of the retained checked subdivision satisfies the original trace budget.

The exact successful dyadic preparation equation identifies its stored request list with the original budgeted dyadic
requests. -/
theorem prepare_fit (budget : PreparedTraceBudget segment left right) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (ordered : left.parameter ≤ right.parameter) :
    budget.RequestsFit left (budget.prepare within owner ordered).requests := by
  have success := PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
    segment within left right owner budget.depth budget.rootDiameter budget.rootDiameter_positive
    (budget.meshSafe owner ordered)
  have requests := PreparedSheetContinuation.Subdivision.tryDyadic_requests
    segment within left right owner budget.depth budget.rootDiameter budget.rootDiameter_positive success
  change budget.RequestsFit left (budget.prepare within owner ordered).requests
  unfold prepare
  rw [requests]
  exact budget.dyadicRequests_fit ordered

end PreparedTraceBudget

end Purelib.Riemann.Paths
