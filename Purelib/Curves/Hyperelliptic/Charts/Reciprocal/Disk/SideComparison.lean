module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

/-!
# Automatic cap comparisons on a complete retained exterior cache

One shared cap sample is compared with every original prepared parent. The
result retains the controlled source integrator and both complete area paths,
with requested total and area bounds. The output concatenates corrected
parent blocks. The connected-path request consumes these summaries and
pays the finite connectors using the retained primitive-link certificates.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive count_mul_perTerm_lt)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}

set_option genInjectivity false in
/-- A complete exterior-side comparison request indexed by the original prepared parent bank.

The retained finite parent count pays source, reciprocal, coefficient, total and full-area errors before the common
model and reading stages are selected. -/
structure Request (prepared : Path.Preparation regular parents) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original complete-side total-error target is positive. -/ positive : 0 < totalTarget
  /-- The retained complete-area budget uses the actual parent count and maximum original source slope. -/ budget :
    ReciprocalSideArea.SideAreaBudget (ParentCovers.sourceSlopeMaximum prepared.covers) parents.length areaTarget
  /-- The cached per-parent total-error target shared by all original entries. -/ parentTarget :
    InverseRootPolynomial.Coordinate
  /-- The local target is the minimum of the actual finite-count total allocation and retained area-budget allowance. -/
    parentTarget_eq : parentTarget = min (Aggregate.perTerm (totalTarget / 4) parents.length) budget.totalTarget
  /-- The cached per-parent total target is positive. -/ parent_positive : 0 < parentTarget
  /-- The retained original side requests with their exact count- and movement-dependent allocations. -/ requests :
    SideBank.Requests (Aggregate.perTerm (totalTarget / 4) parents.length) (Aggregate.perTerm (totalTarget / 4)
    parents.length)
    (((totalTarget / 4) / 2) / (PreparedRefinementMovement.movementMass parents + 1)) parentTarget budget.areaTarget
      minimum prepared.bank
  /-- The cached sufficient common polynomial stage. -/ index : Nat
  /-- The polynomial stage is exactly the retained request bank's maximum. -/ index_eq : index = requests.maximum
  /-- The cached sufficient common endpoint-reading stage. -/ readingIndex : Nat
  /-- The reading stage is exactly the original retained requests' reading maximum. -/ readingIndex_eq : readingIndex =
    requests.readingMaximum

constructive_injectivity Request

namespace Request

/-- Allocate the complete side targets over its original parents and cache all resulting source, cap and endpoint
requests. -/
@[expose] def build (prepared : Path.Preparation regular parents) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget areaTarget minimum := by
  let budget := SideAreaBudget.build (ParentCovers.sourceSlopeMaximum prepared.covers)
    (ParentCovers.sourceSlopeMaximum_nonnegative prepared.covers) parents.length areaTarget areaPositive
  have quarterPositive := Fraction.Order.Field.div_pos_direct totalPositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let parentTarget := min (Aggregate.perTerm (totalTarget / 4) parents.length) budget.totalTarget
  have parentPositive : 0 < parentTarget := Fraction.Order.Basic.lt_min (Aggregate.perTerm_positive quarterPositive _)
    budget.total_positive
  let requests := Requests.build (Aggregate.perTerm (totalTarget / 4) parents.length) (Aggregate.perTerm (totalTarget /
    4) parents.length)
    (((totalTarget / 4) / 2) / (PreparedRefinementMovement.movementMass parents + 1)) parentTarget budget.areaTarget
    (Aggregate.perTerm_positive quarterPositive _) (Aggregate.perTerm_positive quarterPositive _)
    (Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct quarterPositive (by decide))
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (PreparedRefinementMovement.movementMass_nonnegative
        parents) (by decide)))
    parentPositive budget.area_positive minimum prepared.bank
  exact ⟨totalPositive, budget, parentTarget, rfl, parentPositive, requests, requests.maximum, rfl,
    requests.readingMaximum, rfl⟩

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular parents}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum index depth
  readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The retained per-parent total target fits the original full-area budget's total allowance. -/
theorem parent_le_area (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared
  totalTarget areaTarget minimum) : request.parentTarget ≤ request.budget.totalTarget := by
  rw [request.parentTarget_eq]
  exact Fraction.Order.Basic.min_le_right _ _

/-- The retained per-parent total target is at most one. -/
theorem parent_le_one (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget
  areaTarget minimum) : request.parentTarget ≤ 1 :=
  request.parent_le_area.trans request.budget.total_le_one

/-- The squared original parent count times the retained local target fits one quarter of the complete total target. -/
theorem total_paid (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget
  areaTarget minimum) :
    (parents.length : InverseRootPolynomial.Coordinate) * ((parents.length : InverseRootPolynomial.Coordinate) *
      request.parentTarget) < totalTarget / 4 := by
  have parentLe : request.parentTarget ≤ Aggregate.perTerm (totalTarget / 4) parents.length := by
    rw [request.parentTarget_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have nonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le parents.length)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentLe nonnegative) nonnegative).trans_lt
    (Aggregate.count_mul_perTerm_lt (Fraction.Order.Field.div_pos_direct request.positive (by decide)) _)

/-- The original full-area allocation pays every internal parent area and every cross term of retained parent totals. -/
theorem area_paid (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget
  areaTarget minimum) :
    2 * ((parents.length : InverseRootPolynomial.Coordinate) ^ 2 * request.budget.areaTarget +
      16 * (parents.length : InverseRootPolynomial.Coordinate) ^ 4 * request.parentTarget * (2 *
        ((ParentCovers.sourceSlopeMaximum prepared.covers) + 1))) < areaTarget := by
  have nonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le parents.length)
  have countNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
    (Fraction.Order.Arithmetic.pow_nonneg_direct nonnegative 4)
  have slopeNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
    (add_nonneg (ParentCovers.sourceSlopeMaximum_nonnegative prepared.covers) (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.parent_le_area countNonnegative)
        slopeNonnegative))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_lt request.budget.paid

set_option genInjectivity false in
/-- The actual retained source integrator and complete source/cap paths with their paid total and area comparisons.

All parent evaluations and primitive joins remain cached, and the source total reads back the exact original controlled
request. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared totalTarget
  areaTarget minimum)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat) where
  /-- The original cached per-parent source and cap evaluations. -/ parents : SideBank.Evaluations sample depth
    readingIndex request.requests
  /-- The retained primitive-name joins between consecutive original parent endpoints. -/ links :
    SideBank.PrimitiveLinks sample prepared.bank
  /-- The original controlled coupled request assembled from these exact cached source evaluations. -/ compared :
    PreparedReciprocalControlledRequests.CoupledRequest prepared.covers (totalTarget / 4) (totalTarget / 4) minimum
  /-- The coupled request is exactly the constructor applied to the retained original source request bank. -/
    compared_eq : compared = CoupledRequest.ofRequests prepared.covers (totalTarget / 4) (totalTarget / 4)
    (Fraction.Order.Field.div_pos_direct request.positive (by decide))
    (Fraction.Order.Field.div_pos_direct request.positive (by decide)) minimum parents.originals.compared
  /-- The complete original source increment-path summary. -/ left : IncrementArea.Summary (parents.pairs.map
    Prod.fst).flatten
  /-- The complete corrected cap increment-path summary. -/ cap : IncrementArea.Summary (parents.pairs.map
    Prod.snd).flatten
  /-- The source summary total is exactly the retained controlled primitive sum. -/ source_total : left.total =
    compared.source.primitiveSum
  /-- The two actual complete path totals differ by less than one quarter of the original total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (left.total - cap.total) < totalTarget / 4
  /-- The two complete retained path areas differ by less than the original area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (left.area - cap.area) < areaTarget
  /-- The original controlled integral sample differs from the retained complete cap total by less than the original
    total target. -/ integral_close : Data.Gaussian.Norm.Basic.normSq (compared.source.integralSample -
    cap.total) < totalTarget

constructive_injectivity Evaluation

/-- Assemble the side from retained parent evaluations without resampling any source, reciprocal cell or endpoint
reading. -/
@[expose] def evaluateWithParents (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared
  totalTarget areaTarget minimum)
    (parents : SideBank.Evaluations sample depth readingIndex request.requests) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request.Evaluation request sample depth readingIndex :=
      by
  have quarterPositive := Fraction.Order.Field.div_pos_direct request.positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let compared := CoupledRequest.ofRequests prepared.covers (totalTarget / 4) (totalTarget / 4)
    quarterPositive quarterPositive minimum parents.originals.compared
  let left := parents.leftSummary
  let cap := parents.capSummary
  have sourceEq : left.total = compared.source.primitiveSum := by
    rw [compared.source.primitiveSum_eq, compared.source.increments_eq]
    exact SideEstimates.source_total parents
  have totalClose : Data.Gaussian.Norm.Basic.normSq (left.total - cap.total) < totalTarget / 4 :=
    (SideEstimates.total_error parents request.parent_le_one).trans_lt request.total_paid
  have areaClose : Data.Gaussian.Norm.Basic.normSq (left.area - cap.area) < areaTarget :=
    (SideEstimates.area_error parents request.parent_le_one request.parent_positive.le).trans_lt request.area_paid
  refine ⟨parents, Links.primitives sample prepared.links, compared, rfl, left, cap, sourceEq, totalClose, areaClose,
    ?_⟩
  have sourceClose : Data.Gaussian.Norm.Basic.normSq (compared.source.integralSample - left.total) <
    totalTarget / 4 := by
    rw [sourceEq, show compared.source.integralSample - compared.source.primitiveSum =
      -(compared.source.primitiveSum - compared.source.integralSample) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    have scalar := compared.source.toPrimitiveSumRequest.accurate
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via compared.source.integralSample left.total cap.total).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct sourceClose totalClose)).trans_eq (by
      rw [show 2 * (totalTarget / 4 + totalTarget / 4) = totalTarget / 4 * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Consume a cap sample shared with other sides, at sufficiently late polynomial and reading stages. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request prepared
  totalTarget areaTarget minimum)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison.Request.Evaluation request sample depth readingIndex :=
  request.evaluateWithParents
    (Requests.evaluate request.requests prepared.proper sample depth readingIndex (request.index_eq ▸ later)
      (request.readingIndex_eq ▸ readingLater))

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
