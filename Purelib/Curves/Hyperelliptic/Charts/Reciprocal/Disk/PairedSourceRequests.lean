module
import Purelib.Data.List.Map
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
public import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Topology.Polygon.Stokes

section

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore

open Purelib.Riemann.Readings

public section

/-! Assemble the retained paired primitives into the controlled source sums
consumed by shared-face comparisons. Endpoint increments are read from the
existing summaries rather than evaluating the primitive polynomials again. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest ControlledSumRequest
  IndicesAbove)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry Evaluation)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility

/-- The original controlled source-sum request retaining exact supplied primitive-sum and stage-floor readbacks. -/
@[expose] def CertifiedSourceSum {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) (target :
      InverseRootPolynomial.Coordinate) (minimum : Nat) (value : InverseRootPolynomial.Gaussian) :=
  { result : PreparedControlledPrimitiveRequests.ControlledSumRequest parents genus target // result.primitiveSum =
    value ∧ result.minimumIndex = minimum }

/-- Assemble the supplied controlled local requests into their exact ordered parent request spine.

Each original source occurrence retains its own supplied local request and
the same ordered tail, with the original parent map and allowance unchanged. -/
@[expose] def locals {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {α : Type u} (parent : α → PreparedSubdivisionModelCore.CenteredEdge curve differential) {allowance :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    (get : (value : α) → PreparedControlledPrimitiveRequests.ControlledLocalRequest (parent value) genus allowance
      allowance minimum) :
    (values : List α) → UniformPreparedRequests.RequestedParents genus allowance (values.map parent)
  | [] => .nil
  | head :: tail => .cons (get head).localRequest
    (locals parent get tail)

/-- The actual assembled local coefficient maximum is below the common positive allowance.

Every retained local coefficient is below the positive common allowance.
The maximum follows the same finite request spine and preserves that strict bound. -/
theorem locals_coefficient {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {α : Type u} (parent : α → PreparedSubdivisionModelCore.CenteredEdge curve differential) {allowance :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    (get : (value : α) → PreparedControlledPrimitiveRequests.ControlledLocalRequest (parent value) genus allowance
      allowance minimum)
    (positive : 0 < allowance) (values : List α) : PreparedPrimitiveChargeBounds.coefficientMaximum
      (locals parent get values) < allowance := by
  induction values with
  | nil => exact positive
  | cons head tail ih => exact Fraction.Order.Basic.max_lt (get head).coefficient_accurate ih

/-- Every actual assembled local request meets the common minimum stage.

Each supplied request retains its bound by the common minimum stage.
The dependent tail keeps the same parent occurrences and stage floor. -/
theorem locals_indices {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {α : Type u} (parent : α → PreparedSubdivisionModelCore.CenteredEdge curve differential) {allowance :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    (get : (value : α) → PreparedControlledPrimitiveRequests.ControlledLocalRequest (parent value) genus allowance
      allowance minimum)
    (values : List α) : PreparedControlledPrimitiveRequests.IndicesAbove minimum
      (locals parent get values) := by
  induction values with
  | nil => trivial
  | cons head tail ih => exact ⟨(get head).index_ge, ih⟩

/-- The actual assembled increment list equals the supplied increment readbacks in order.

The supplied pointwise equations identify the retained head increment.
Scalar list congruence transports the unchanged ordered tail readback. -/
theorem locals_increments {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {α : Type u} (parent : α → PreparedSubdivisionModelCore.CenteredEdge curve differential) {allowance :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    (get : (value : α) → PreparedControlledPrimitiveRequests.ControlledLocalRequest (parent value) genus allowance
      allowance minimum)
    (increment : α → InverseRootPolynomial.Gaussian) (readback : ∀ value, LocalRequest.increment (get
      value).localRequest = increment value)
    (values : List α) : (locals parent get
      values).increments = values.map increment := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg₂ List.cons (readback head) ih

/-- Assemble the original controlled source requests and cached increments into a paid whole-parent sum.

The exact parent list, movement mass and minimum stage are retained, with separate count and coefficient payments. -/
@[expose] def certifySourceSum {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    {α : Type u} (parent : α → PreparedSubdivisionModelCore.CenteredEdge curve differential) {allowance target :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    (get : (value : α) → PreparedControlledPrimitiveRequests.ControlledLocalRequest (parent value) genus allowance
      allowance minimum)
    (increment : α → InverseRootPolynomial.Gaussian) (readback : ∀ value, LocalRequest.increment (get
      value).localRequest = increment value)
    (values : List α) {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (parentsEq :
      values.map parent = parents)
    (positive : 0 < allowance) (targetPositive : 0 < target)
    (localPaid : allowance ≤ Aggregate.perTerm target parents.length)
    (mass : InverseRootPolynomial.Coordinate) (massEq : mass = PreparedRefinementMovement.movementMass parents)
    (coefficientPaid : allowance ≤ (target / 2) / (mass + 1)) :
    CertifiedSourceSum parents target minimum
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map increment)) := by
  cases parentsEq
  let retained := locals parent get values
  let requests := retained.weaken localPaid
  let blocks := requests.blocks
  let increments := values.map increment
  let path := PathModel.mk (blocks.children.map CenteredEdge.model)
  exact ⟨{
    target_positive := targetPositive
    localTarget := Aggregate.perTerm target (values.map parent).length
    localTarget_eq := rfl
    localTarget_positive := Aggregate.perTerm_positive targetPositive _
    requests := requests
    blocks := blocks
    blocks_eq := rfl
    increments := increments
    increments_eq := ((retained.weaken_increments localPaid).trans
      (locals_increments parent get increment readback
        values)).symm
    primitiveSum := Data.Gaussian.Norm.Sum.Basic.gaussianSum increments
    primitiveSum_eq := rfl
    integralSample := path.tailIntegralSample
    integralSample_eq := path.integralSample_eq_tailIntegralSample.symm
    mass := mass
    mass_eq := massEq
    coefficientTarget := (target / 2) / (mass + 1)
    coefficientTarget_eq := rfl
    coefficient_accurate := (retained.weaken_coefficientMaximum localPaid).trans_lt
      ((locals_coefficient parent get positive
        values).trans_le coefficientPaid)
    minimumIndex := minimum
    indices_ge := retained.weaken_indices localPaid
      (locals_indices parent get values) }, rfl, rfl⟩

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Request regular other parents
    target minimum}

/-- The original count-paid paired parent request has a strictly positive whole target. -/
theorem target_positive (request : PairedParentRequest.Request regular other parents target minimum) : 0 < target :=
  (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
      request.positive.le)).trans_lt request.paid

/-- The retained common allowance satisfies the original parent-count allocation of the whole target. -/
theorem local_paid (request : PairedParentRequest.Request regular other parents target minimum) :
    request.allowance ≤ Aggregate.perTerm target parents.length := by
  rw [request.allowance_eq]
  exact (Fraction.Order.Basic.min_le_right ..).trans (Fraction.Order.Basic.min_le_left ..)

/-- The actual evaluated paired entries project to exactly the original parent spine. -/
theorem Evaluation.source_parents (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample fine) :
    evaluated.retained.map (fun entry => entry.plan.parent) = parents := by
  have equal := (congrArg (List.map Plan.parent) evaluated.plans_eq).trans request.parents_eq
  simpa only [Data.List.Map.map_map, Function.comp_def] using equal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests
/-- The original differential's complete source request reuses both the retained primitives and their cached endpoint
increments. -/
@[expose] def Evaluation.sourceRequest (evaluated : PairedParentRequest.Request.Evaluation request sample otherSample
  fine) :
    CertifiedSourceSum parents target minimum
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
        entry.certified.compared.firstSummary.totalValue.left))) :=
  certifySourceSum (genus := genus) (curve := curve)
    (differential := differential)
    (α := PairedParentRequest.Request.Entry request sample otherSample fine) (allowance := request.allowance) (target :=
      target) (minimum := minimum)
    (fun entry => entry.plan.parent) (fun entry => entry.source)
    (fun entry => entry.certified.compared.firstSummary.totalValue.left) Entry.source_increment
    evaluated.retained (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents
      evaluated) request.positive (target_positive request)
      (local_paid request)
    request.sourceMass request.sourceMass_eq request.source_paid

/-- The recast differential uses the identical parent geometry and mass. -/
@[expose] def Evaluation.otherSourceRequest (evaluated : PairedParentRequest.Request.Evaluation request sample
  otherSample fine) :
    CertifiedSourceSum (parents.map
      (PreparedEdgeRecasting.recastCenteredEdge other)) target minimum
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry =>
        entry.certified.compared.firstSummary.totalValue.right))) := by
  have parentEq : evaluated.retained.map (fun entry => PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent)
    =
      parents.map (PreparedEdgeRecasting.recastCenteredEdge other) := by
    have equal := congrArg (List.map (PreparedEdgeRecasting.recastCenteredEdge other))
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests.Evaluation.source_parents evaluated)
    simpa only [Data.List.Map.map_map, Function.comp_def] using equal
  exact certifySourceSum (genus := genus) (curve :=
    curve) (differential := other)
    (α := PairedParentRequest.Request.Entry request sample otherSample fine) (allowance := request.allowance) (target :=
      target) (minimum := minimum)
    (fun entry => PreparedEdgeRecasting.recastCenteredEdge other entry.plan.parent) (fun entry => entry.otherSource)
    (fun entry => entry.certified.compared.firstSummary.totalValue.right) Entry.otherSource_increment
    evaluated.retained parentEq request.positive (target_positive request)
    ((congrArg (Aggregate.perTerm target) (Data.List.Map.length_map ..)).symm ▸
      local_paid request)
    request.sourceMass (request.sourceMass_eq.trans (PreparedRefinementMovement.movementMass_recast other parents).symm)
    request.source_paid

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedSourceRequests

end
