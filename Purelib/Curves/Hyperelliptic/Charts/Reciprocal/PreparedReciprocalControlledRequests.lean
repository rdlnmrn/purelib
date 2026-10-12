module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
open Purelib.Riemann.Readings.UniformPreparedRequests

/-!
# One source bank for reciprocal and actual prepared integral comparisons

Select an index paying the local prepared integral, its polynomial floor,
the requested face index, and the complete reciprocal-cover error. Both
interfaces then consume the very same source coefficient and primitive.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests

open Purelib.Riemann.Readings
open Purelib.Riemann.Integration
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.UniformPreparedRequests (PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (localCoefficient coefficientMaximum)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest DualIndex ControlledSumRequest
  IndicesAbove)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent} {data :
    Data patch count}

set_option genInjectivity false in
/-- The source and reciprocal requests sharing one original source primitive and linked refinement stages.

The retained increment equality and two-stage model shift identify the exact cache consumed by both interfaces. -/
structure CoupledLocalRequest (cover : UniformReciprocalCover.Cover data) (sourceTarget reciprocalTarget
  coefficientTarget : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained controlled source-integral request on the original parent. -/ source :
    PreparedControlledPrimitiveRequests.ControlledLocalRequest parent count sourceTarget coefficientTarget minimum
  /-- The retained full reciprocal-cover request sharing the original source primitive. -/ reciprocal : Cover.Request
    cover reciprocalTarget
  /-- The two retained request interfaces use exactly the same original source increment or sum. -/ source_eq :
    LocalRequest.increment source.localRequest = reciprocal.sourceIncrement
  /-- The controlled source model stage is exactly two above the retained reciprocal stage. -/ index_eq :
    source.localRequest.request.index = 2 + reciprocal.index

constructive_injectivity CoupledLocalRequest

set_option genInjectivity false in
/-- Cache the numerical selection before materializing a polynomial bank. A whole side can select one common later stage
from these finite plans. -/
structure CoupledLocalPlan (data : UniformReciprocalModels.Data patch count) (sourceTarget reciprocalTarget
  coefficientTarget : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The requested original source error target is strictly positive. -/ source_positive : 0 < sourceTarget
  /-- The cached finite squared-norm bound for the original differential numerator. -/ numeratorBound :
    InverseRootPolynomial.Coordinate
  /-- The numerator ceiling is the original polynomial's finite bound on the retained patch neighborhood. -/
    numeratorBound_eq : numeratorBound = Dense.Gaussian.Bounds.Box.denseEvalNormBound
    (PreparedPrimitiveSamples.differentialNumerator differential) (patch.neighborhood count).box
  /-- The cached differential numerator ceiling is nonnegative. -/ numerator_nonnegative : 0 ≤ numeratorBound
  /-- The cached original prepared-integral root error scale. -/ localScale : InverseRootPolynomial.Coordinate
  /-- The local scale uses the same retained neighborhood, numerator ceiling and original parent movement. -/
    localScale_eq : localScale = PreparedPrimitiveRequests.rootScale (patch.neighborhood count) numeratorBound
    (PreparedPrimitiveRequests.movement parent)
  /-- The original prepared-integral error scale is nonnegative. -/ local_nonnegative : 0 ≤ localScale
  /-- The cached error scale for the retained source coefficient. -/ coefficientScale : InverseRootPolynomial.Coordinate
  /-- The coefficient scale is four times the original numerator ceiling and inverse error scale. -/ coefficientScale_eq
    : coefficientScale = 4 * numeratorBound * (patch.neighborhood count).inverseErrorScale
  /-- The cached source coefficient error scale is nonnegative. -/ coefficient_nonnegative : 0 ≤ coefficientScale
  /-- The retained common polynomial stage selected before materializing the cache. -/ index : Nat
  /-- The selected common stage respects the supplied original minimum. -/ minimum_le : minimum ≤ index
  /-- The selected source stage pays the local prepared-integral error allocation. -/ local_accurate :
    Geometric.Basic.quarterRadius localScale (2 + index) < (sourceTarget / 8) / 3
  /-- Every retained source coefficient error lies below the supplied common target. -/ coefficient_accurate :
    Geometric.Basic.quarterRadius coefficientScale (2 + index) < coefficientTarget
  /-- The selected common stage pays the complete original reciprocal-cover error. -/ reciprocal_accurate :
    Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index < reciprocalTarget

constructive_injectivity CoupledLocalPlan

namespace CoupledLocalPlan

/-- Select numerical floors paying the source, coefficient and full reciprocal-cover targets before materializing any
polynomial cache. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) (sourceTarget reciprocalTarget coefficientTarget :
  InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (minimum : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan data
      sourceTarget reciprocalTarget coefficientTarget minimum := by
  let neighborhood := patch.neighborhood count
  let numerator := PreparedPrimitiveSamples.differentialNumerator differential
  let numeratorBound := Dense.Gaussian.Bounds.Box.denseEvalNormBound numerator neighborhood.box
  have numeratorNonnegative := (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg numerator neighborhood.box).1
  let localScale := PreparedPrimitiveRequests.rootScale neighborhood numeratorBound (PreparedPrimitiveRequests.movement
    parent)
  let coefficientScale := 4 * numeratorBound * neighborhood.inverseErrorScale
  have localNonnegative : 0 ≤ localScale := PreparedPrimitiveRequests.rootScale_nonnegative neighborhood
    numeratorNonnegative
    (PreparedPrimitiveRequests.movement_nonnegative parent)
  have coefficientNonnegative : 0 ≤ coefficientScale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) numeratorNonnegative)
      neighborhood.inverseErrorScale_positive.le
  have localPositive : 0 < sourceTarget / 8 := Fraction.Order.Field.div_pos_direct sourcePositive (by decide)
  let selected := DualIndex.acquire localScale coefficientScale ((sourceTarget / 8) / 3) coefficientTarget
    localNonnegative
    (Fraction.Order.Field.div_pos_direct localPositive (by decide)) coefficientPositive minimum
  let reciprocalIndex := Search.firstQuarterBelow (UniformReciprocalPrimitives.Data.errorScale data) 0 reciprocalTarget
  let index := max selected.index reciprocalIndex
  have sourceLater : selected.index ≤ 2 + index := (Data.Nat.Order.le_max_left _ _).trans (Nat.le_add_left _ _)
  exact ⟨sourcePositive, numeratorBound, rfl, numeratorNonnegative, localScale, rfl, localNonnegative,
    coefficientScale, rfl, coefficientNonnegative, index, selected.index_ge.trans (Data.Nat.Order.le_max_left _ _),
    (quarterRadius_antitone localNonnegative sourceLater).trans_lt selected.first_accurate,
    (quarterRadius_antitone coefficientNonnegative sourceLater).trans_lt selected.second_accurate,
    (quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)
      (Data.Nat.Order.le_max_right _ _)).trans_lt
      (Search.firstQuarterBelow_accurate _ (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) 0 _
        reciprocalPositive)⟩

variable {sourceTarget reciprocalTarget coefficientTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- The actual prepared integral consumes an already retained source model; no replacement coefficient, primitive, or
reciprocal cell bank is built. -/
@[expose] def sourceRequest (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan data sourceTarget
  reciprocalTarget coefficientTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {index : Nat} (source : UniformReciprocalPrimitives.SourcePrimitive data index) (later : plan.index ≤ index) :
    PreparedControlledPrimitiveRequests.ControlledLocalRequest parent count sourceTarget coefficientTarget minimum := by
  let neighborhood := patch.neighborhood count
  have sourceLater : 2 + plan.index ≤ 2 + index := Nat.add_le_add_left later 2
  have localAccurate := (quarterRadius_antitone plan.local_nonnegative sourceLater).trans_lt
    plan.local_accurate
  rw [plan.localScale_eq] at localAccurate
  have numeratorLe : ∀ point, neighborhood.box.Contains point →
      Data.Gaussian.Norm.Basic.normSq ((PreparedPrimitiveSamples.differentialNumerator differential).eval
        point) ≤ plan.numeratorBound := by
    intro point inside
    rw [plan.numeratorBound_eq]
    exact Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ inside
  let approximation := PreparedPrimitiveRequests.Request.ofModel parent neighborhood (sourceTarget / 8)
    (Fraction.Order.Field.div_pos_direct plan.source_positive (by decide)) proper
    plan.numeratorBound plan.numerator_nonnegative (fun point inside => by
      have scalar := numeratorLe point inside
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar) (2 + index) source.asPrepared localAccurate
  let localRequest : UniformPreparedRequests.LocalRequest parent count sourceTarget := ⟨patch, neighborhood, rfl,
    approximation, data.finishInside⟩
  have coefficientEq : PreparedPrimitiveChargeBounds.localCoefficient localRequest = Geometric.Basic.quarterRadius
    plan.coefficientScale (2 + index) := by
    change 4 * plan.numeratorBound * Geometric.Basic.quarterRadius neighborhood.inverseErrorScale (2 + index) = _
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow, plan.coefficientScale_eq]
    ring1
  exact ⟨localRequest, coefficientEq.trans_lt ((quarterRadius_antitone plan.coefficient_nonnegative
    sourceLater).trans_lt plan.coefficient_accurate),
    plan.minimum_le.trans (later.trans (Nat.le_add_left _ _))⟩

/-- The controlled source request retains exactly the supplied cached primitive polynomial. -/
theorem sourceRequest_primitive (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan data sourceTarget
  reciprocalTarget coefficientTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {index : Nat} (source : UniformReciprocalPrimitives.SourcePrimitive data index) (later : plan.index ≤ index) :
    (plan.sourceRequest proper source later).localRequest.request.model.primitive.value = source.primitive.value := by
  dsimp only
    [sourceRequest,
    PreparedPrimitiveRequests.Request.ofModel]
  rfl

/-- Both interfaces consume the supplied cached source at the shared stage. -/
@[expose] def evaluate (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan data sourceTarget
  reciprocalTarget coefficientTarget minimum) (cover : UniformReciprocalCover.Cover data)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {index : Nat} (source : UniformReciprocalPrimitives.SourcePrimitive data index) (later : plan.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalRequest cover sourceTarget
      reciprocalTarget coefficientTarget minimum := by
  let controlled := plan.sourceRequest proper source later
  exact ⟨controlled, Cover.Request.ofSource cover source reciprocalTarget
    ((quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) later).trans_lt
      plan.reciprocal_accurate), rfl, rfl⟩

/-- Evaluating a retained plan uses exactly the supplied original source refinement stage. -/
theorem evaluate_index (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan data sourceTarget
  reciprocalTarget coefficientTarget minimum) (cover : UniformReciprocalCover.Cover data)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    {index : Nat} (source : UniformReciprocalPrimitives.SourcePrimitive data index) (later : plan.index ≤ index) :
    (plan.evaluate cover proper source later).reciprocal.index = index := rfl

end CoupledLocalPlan

namespace CoupledLocalRequest

/-- Select a coupled numerical plan, build its source primitive once, and feed that same cache to both request
interfaces. -/
@[expose] def build (cover : UniformReciprocalCover.Cover data) (sourceTarget reciprocalTarget coefficientTarget :
  InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalRequest cover sourceTarget
      reciprocalTarget coefficientTarget minimum :=
  let plan := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalPlan.build data
    sourceTarget reciprocalTarget coefficientTarget sourcePositive reciprocalPositive coefficientPositive minimum
  plan.evaluate cover proper (SourcePrimitive.build data plan.index) le_rfl

end CoupledLocalRequest

set_option genInjectivity false in
/-- Coupled source and reciprocal requests indexed by the original parent-cover spine.

Every head retains its own cover and shared primitive identity, with a uniform minimum stage and separate error targets.
-/
inductive CoupledParents (sourceTarget reciprocalTarget coefficientTarget : InverseRootPolynomial.Coordinate) (minimum :
  Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
      UniformReciprocalCover.ParentCovers parents → Type 2
  /-- The empty original parent-cover spine has no coupled requests. -/ | nil :
    CoupledParents sourceTarget
    reciprocalTarget coefficientTarget minimum .nil
  /-- Retain the original head cover's coupled request and the matching original tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus} {cover : UniformReciprocalCover.Cover data} {tail : UniformReciprocalCover.ParentCovers remaining}
      (head : CoupledLocalRequest cover
        sourceTarget reciprocalTarget coefficientTarget minimum)
      (rest : CoupledParents
        sourceTarget reciprocalTarget coefficientTarget minimum tail) :
        CoupledParents sourceTarget
          reciprocalTarget coefficientTarget minimum (.cons patch data cover tail)

constructive_injectivity CoupledParents

namespace CoupledParents

variable {sourceTarget reciprocalTarget coefficientTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Build coupled requests along the original proper parent-cover spine with separate paid targets. -/
@[expose] def build (sourceTarget reciprocalTarget coefficientTarget : InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (coefficientPositive : 0 <
      coefficientTarget)
    (minimum : Nat) : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → (covers :
      UniformReciprocalCover.ParentCovers parents) →
    PreparedDyadicRefinements.AllParentsProper parents →
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers
  | _, .nil, _ => .nil
  | _, .cons _ _ cover tail, proper =>
      .cons (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledLocalRequest.build cover
        _ _ _ sourcePositive reciprocalPositive coefficientPositive proper.1 minimum)
        (build _ _ _
          sourcePositive reciprocalPositive coefficientPositive minimum tail proper.2)

/-- Read the original controlled source request from each retained coupled parent occurrence. -/
@[expose] def source : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers → UniformPreparedRequests.RequestedParents genus sourceTarget
      parents
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.source.localRequest tail.source

/-- Read the reciprocal-cover request from each retained coupled parent occurrence. -/
@[expose] def reciprocal : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers → ParentCovers.Requests reciprocalTarget covers
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head.reciprocal tail.reciprocal

/-- Every retained source coefficient error lies below the supplied common target. -/
theorem coefficient_accurate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers) (positive : 0 < coefficientTarget) :
    PreparedPrimitiveChargeBounds.coefficientMaximum requests.source < coefficientTarget := by
  induction requests with
  | nil => exact positive
  | cons head tail ih => exact Fraction.Order.Basic.max_lt head.source.coefficient_accurate ih

/-- Every retained controlled source index respects the original common minimum. -/
theorem indices_ge {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers) :
    PreparedControlledPrimitiveRequests.IndicesAbove minimum requests.source := by
  induction requests with
  | nil => trivial
  | cons head tail ih => exact ⟨head.source.index_ge, ih⟩

/-- The original controlled source increments equal the reciprocal requests' retained source-value list. -/
theorem source_increments {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents sourceTarget
      reciprocalTarget coefficientTarget minimum covers) :
    requests.source.increments = requests.reciprocal.sourceValues := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      change LocalRequest.increment head.source.localRequest :: tail.source.increments = head.reciprocal.sourceIncrement
        :: tail.reciprocal.sourceValues
      rw [head.source_eq, ih]

end CoupledParents

set_option genInjectivity false in
/-- Both interfaces expose exactly the same cached source primitive sum. The source request retains actual compatible
prepared refinement blocks, its controlled polynomial floor, and the caller's mesh-wide minimum index. -/
structure CoupledRequest {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (sourceTarget reciprocalTarget : InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained aggregate controlled source request with its original compatible refinement. -/ source :
    PreparedControlledPrimitiveRequests.ControlledSumRequest parents genus sourceTarget
  /-- The retained controlled request uses exactly the supplied original minimum index. -/ minimum_eq :
    source.minimumIndex = minimum
  /-- The retained aggregate reciprocal request on the exact original parent covers. -/ reciprocal :
    ParentCovers.Request covers reciprocalTarget
  /-- The two retained request interfaces use exactly the same original source increment or sum. -/ source_eq :
    source.primitiveSum = reciprocal.sourceIntegral

constructive_injectivity CoupledRequest

namespace CoupledRequest

/-- Assemble aggregate source and reciprocal requests from the same retained coupled parent requests and exact shared
primitive sum. -/
@[expose] def ofRequests {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (sourceTarget reciprocalTarget : InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (minimum : Nat)
    (coupled : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents
      (Aggregate.perTerm sourceTarget parents.length)
      (Aggregate.perTerm reciprocalTarget parents.length)
      ((sourceTarget / 2) / (PreparedRefinementMovement.movementMass parents + 1)) minimum covers) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledRequest covers sourceTarget
      reciprocalTarget minimum := by
  let mass := PreparedRefinementMovement.movementMass parents
  let coefficientTarget := (sourceTarget / 2) / (mass + 1)
  have coefficientPositive : 0 < coefficientTarget := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct sourcePositive (by decide))
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative
      parents) (by decide))
  let reciprocalLocal := Aggregate.perTerm reciprocalTarget parents.length
  let source : PreparedControlledPrimitiveRequests.ControlledSumRequest parents genus sourceTarget :=
    { toPrimitiveSumRequest := PrimitiveSumRequest.ofRequests parents sourceTarget sourcePositive coupled.source
      mass := mass
      mass_eq := rfl
      coefficientTarget := coefficientTarget
      coefficientTarget_eq := rfl
      coefficient_accurate := coupled.coefficient_accurate coefficientPositive
      minimumIndex := minimum
      indices_ge := coupled.indices_ge }
  have sourceEq : source.primitiveSum = Data.Gaussian.Norm.Sum.Basic.gaussianSum coupled.reciprocal.sourceValues :=
    by
    rw [source.primitiveSum_eq, source.increments_eq]
    exact congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum coupled.source_increments
  let reciprocal : ParentCovers.Request covers reciprocalTarget :=
    { localTarget := reciprocalLocal
      localTarget_eq := rfl
      requests := coupled.reciprocal
      sourceIntegral := source.primitiveSum
      sourceIntegral_eq := sourceEq
      reciprocalIntegral := Data.Gaussian.Norm.Sum.Basic.gaussianSum coupled.reciprocal.reciprocalValues
      reciprocalIntegral_eq := rfl
      error := (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length :
        InverseRootPolynomial.Coordinate) * reciprocalLocal)
      error_eq := rfl
      error_lt := Aggregate.count_mul_perTerm_lt reciprocalPositive _
      close := by
        rw [sourceEq, ← coupled.reciprocal.errors_sum]
        have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le coupled.reciprocal.errors _
          coupled.reciprocal.errors_bounded
        rw [coupled.reciprocal.errors_length] at estimate
        exact estimate }
  exact ⟨source, rfl, reciprocal, rfl⟩

/-- Pay the finite parent and movement budgets and assemble requests sharing the exact original source primitive sum. -/
@[expose] def build {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (covers :
  UniformReciprocalCover.ParentCovers parents)
    (proper : PreparedDyadicRefinements.AllParentsProper parents) (sourceTarget reciprocalTarget :
      InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledRequest covers sourceTarget
      reciprocalTarget minimum :=
  ofRequests covers
    sourceTarget reciprocalTarget sourcePositive reciprocalPositive minimum
    (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledParents.build _ _ _
      (Aggregate.perTerm_positive sourcePositive _)
      (Aggregate.perTerm_positive reciprocalPositive _)
      (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct sourcePositive (by decide))
        (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative
          parents) (by decide))) minimum covers proper)

/-- The reciprocal sum approximates the actual prepared integrator on the same retained compatible refinement, with both
independent requests paid. -/
theorem integral_error {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
    {sourceTarget reciprocalTarget : InverseRootPolynomial.Coordinate} {minimum : Nat}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests.CoupledRequest covers
      sourceTarget reciprocalTarget minimum) :
    Data.Gaussian.Norm.Basic.normSq (request.source.integralSample - request.reciprocal.reciprocalIntegral) < 2
      * (sourceTarget + reciprocalTarget) := by
  have sourceError := request.source.toPrimitiveSumRequest.accurate
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at sourceError
  have reciprocalError := request.reciprocal.close.trans_lt request.reciprocal.error_lt
  rw [← request.source_eq] at reciprocalError
  have identity : request.source.integralSample - request.reciprocal.reciprocalIntegral =
      -(request.source.primitiveSum - request.source.integralSample) +
        (request.source.primitiveSum - request.reciprocal.reciprocalIntegral) := by ring1
  rw [identity]
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two (-(request.source.primitiveSum -
    request.source.integralSample))
    (request.source.primitiveSum - request.reciprocal.reciprocalIntegral)
  rw [Data.Gaussian.Norm.Basic.normSq_neg] at estimate
  exact estimate.trans_lt (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
    (Fraction.Order.Arithmetic.add_lt_add_direct sourceError reciprocalError))

end CoupledRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
