module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-!
# Automatic shared regular-cap comparison of the complete exterior path

The existing path request supplies all source sampling and the finite parent
budget. Every regular-cap parent is sampled at one sufficient shared stage.
The result retains the original controlled integrator and both full paths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}

set_option genInjectivity false in
/-- A shared-stage regular-cap comparison request retaining the original controlled exterior-path integrator. -/
structure RegularRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular parents)
  (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original total-and-area comparison request for the retained parent path. -/ original :
    Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget areaTarget minimum
  /-- The retained regular-cap plans for the original per-parent requests. -/ plans :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans original.requests
  /-- The shared sufficient cap-polynomial sample stage. -/ index : Nat
  /-- The shared stage is exactly the maximum of the original path request and regular-plan stages. -/ index_eq : index
    = max original.index plans.maximum

constructive_injectivity RegularRequest

namespace RegularRequest

/-- Prepare the original path request and all regular-cap parent plans at one sufficient shared stage. -/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular parents)
  (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget)
      (areaPositive : 0 < areaTarget)
    (minimum : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared totalTarget
      areaTarget minimum :=
  let original := Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request.build prepared totalTarget areaTarget
    totalPositive areaPositive minimum
  let plans := Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans.build regularChart original.parent_positive
    original.budget.area_positive original.requests
  ⟨original, plans, max original.index plans.maximum, rfl⟩

/-- Prepare the retained regular-cap path comparison using the original even-degree identity to establish origin order
zero. -/
@[expose] def ofEvenDegree (prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular
  parents) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget)
      (areaPositive : 0 < areaTarget)
    (minimum : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared totalTarget
      areaTarget minimum := by
  have balance := Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0 :=
    Data.Nat.Addition.add_left_cancel (balance :
    (2 * genus + 2) + Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = (2 * genus + 2) + 0)
  exact Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.build prepared chart totalTarget
    areaTarget totalPositive areaPositive minimum

variable {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular parents} {totalTarget
  areaTarget : Normalization.InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential
    index box}

set_option genInjectivity false in
/-- The original controlled source evaluation and complete regular-cap path with retained total, area and integral
bounds. -/
structure Evaluation (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared
  totalTarget areaTarget minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) where
  /-- The actual retained evaluation of the original source path comparison request. -/ original :
    Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request.Evaluation request.original sample depth readingIndex
  /-- The actual regular-cap parent results for those exact original evaluated parents. -/ parents :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results request.plans original.parents
  /-- The finite summary of the complete retained regular-cap paths. -/ cap : Path.IncrementArea.Summary
    (parents.pairs.map Prod.snd).flatten
  /-- The retained cap area equals the unsigned area of the original regular primitive paths. -/ cap_area_unsigned :
    cap.area =
    Path.IncrementArea.pathArea
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths sample.primitive.value
      depth prepared.bank).flatten
  /-- The original path and retained cap totals differ by less than one quarter of the total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (original.left.total - cap.total) < totalTarget / 4
  /-- The original path and retained cap areas differ by less than the area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (original.left.area - cap.area) < areaTarget
  /-- The retained original controlled integral sample and cap total differ by less than the total target. -/
    integral_close : Data.Gaussian.Norm.Basic.normSq (original.compared.source.integralSample - cap.total) <
    totalTarget

constructive_injectivity Evaluation

/-- Evaluate the original source and all regular-cap parents at the supplied sufficient model and reading stages. -/
@[expose] def evaluate (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared
  totalTarget areaTarget minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat)
    (later : request.index ≤ index) (readingLater : request.original.readingIndex ≤ readingIndex) :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Evaluation request sample depth readingIndex
      := by
  have indices := request.index_eq ▸ later
  let original := request.original.evaluate sample depth readingIndex ((Data.Nat.Order.le_max_left _ _).trans indices)
    readingLater
  let parents := Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans.evaluate request.plans original.parents
    ((Data.Nat.Order.le_max_right _ _).trans indices)
  have totalEq : original.left.total = parents.leftSummary.total := by
    rw [Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates.source_total_eq parents, original.left.total_eq,
      original.parents.leftSummary.total_eq]
  have areaEq : original.left.area = parents.leftSummary.area := by
    rw [Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates.source_area_eq parents, original.left.area_eq,
      original.parents.leftSummary.area_eq]
  have totalClose : Data.Gaussian.Norm.Basic.normSq (original.left.total - parents.capSummary.total) < totalTarget /
    4 := by
    rw [totalEq]
    exact (Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates.total_error parents
      request.original.parent_le_one).trans_lt request.original.total_paid
  have areaClose : Data.Gaussian.Norm.Basic.normSq (original.left.area - parents.capSummary.area) < areaTarget := by
    rw [areaEq]
    exact (Hyperelliptic.Charts.Reciprocal.Disk.RegularSideEstimates.area_error parents request.original.parent_le_one
      request.original.parent_positive.le).trans_lt request.original.area_paid
  refine ⟨original, parents, parents.capSummary,
    Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.Regular.Results.cap_area_unsigned parents
    prepared.links, totalClose, areaClose, ?_⟩
  have sourceClose : Data.Gaussian.Norm.Basic.normSq (original.compared.source.integralSample - original.left.total)
    < totalTarget / 4 := by
    rw [original.source_total, show original.compared.source.integralSample - original.compared.source.primitiveSum =
      -(original.compared.source.primitiveSum - original.compared.source.integralSample) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    have scalar := original.compared.source.toPrimitiveSumRequest.accurate
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via original.compared.source.integralSample original.left.total
    parents.capSummary.total).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct sourceClose totalClose)).trans_eq (by
      rw [show 2 * (totalTarget / 4 + totalTarget / 4) = totalTarget / 4 * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

set_option genInjectivity false in
/-- The exact shared cap-polynomial sample and original path comparison evaluated at its retained stages. -/
structure Acquisition (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared
  totalTarget areaTarget minimum) (depth : Nat) where
  /-- The original cap-polynomial sample acquired at the request's shared stage on the retained collar box. -/ sample :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential request.index collar.box
  /-- The original evaluation using that exact cap sample and retained reading index. -/ evaluated :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Evaluation request sample depth
    request.original.readingIndex

constructive_injectivity Acquisition

/-- Acquire the original cap sample once at the retained shared stage and evaluate the complete prepared path. -/
@[expose] def acquire (request : Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest prepared
  totalTarget areaTarget minimum) (depth : Nat) :
  Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest.RegularRequest.Acquisition request depth :=
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap differential request.index collar.box
  ⟨sample, request.evaluate sample depth request.original.readingIndex le_rfl le_rfl⟩

end RegularRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
