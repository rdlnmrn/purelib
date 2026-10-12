module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Trace
import Purelib.Riemann.Paths.PreparedTraceEdges
public import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Traces to arbitrary queries of the retained prepared edge

Use the original diameter and movement budget to trace from the cached source
owner to the actual reserve-aware query owner. No shorter prepared request is
created: its different preparation could change the owner presentation. These
traces support proof-only sheet comparison at geometric fragment endpoints.
-/

namespace Purelib.Riemann.Paths.PreparedQueryTraceEdges

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerTail)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)

open Purelib.Riemann.RootContinuation.SquareRootTrace

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint parameterAt)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Path
open Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Data in
/-- Division by 1024 preserves a rational inequality. -/
public theorem div_1024_mono {left right : Rat.Fraction.Rational} (bound : left ≤ right) : left / 1024 ≤ right / 1024
  := by
  apply (Rat.Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Rat.Fraction.Rational) < 1024)).mpr
  rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (1024 : Rat.Fraction.Rational) ≠ 0)]
  exact bound

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- The straight path to a prepared query equals the original segment at the product parameter. -/
private theorem line_to_query (parent : PreparedEdge curve differential) (fraction time : Rat.Fraction.Rational) :
    Rational.Affine.line (parent.segment.pointAt parent.left.parameter)
      (parent.segment.pointAt (parameterAt parent.left parent.request fraction) - parent.segment.pointAt
        parent.left.parameter) time =
        parent.segment.pointAt (parameterAt parent.left parent.request (time * fraction)) := by
  apply Gaussian.Basic.ext <;>
    simp only [Branches.PreparedSheetContinuation.parameterAt_eq_affine, Rational.Affine.line,
      Geometry.ClearPath.ClearSegment.pointAt,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Cast.ofCoordinate_re, Gaussian.Cast.ofCoordinate_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;> ring1

namespace PreparedTraceBudget

variable {parent : PreparedEdge curve differential} {left right : Endpoint}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
/-- Construct a moving trace from retained source and direct-query readings using the original edge budget.

The query fraction lies in the unit interval, and the original diameter and movement charges fit the trace budget. The
actual reserve-aware query owner and cached source owner remain unchanged. -/
def queryEdge (budget : PreparedTraceBudget parent.segment left right)
    (diameterSmall : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movementSmall : Branches.ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter ≤ budget.movementBudget)
    (fraction : Rat.Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    {sourceTail : OwnerTail parent.cached.preparedOwner}
    {targetTail : OwnerTail (parent.directQueryOwner fraction inside)}
    (first : OwnerTail.Reading sourceTail) (second : OwnerTail.Reading targetTail) :
    Edge curve.polynomial first.value second.value (parent.segment.pointAt parent.left.parameter)
      (parent.segment.pointAt (parameterAt parent.left parent.request fraction)) := by
  have lower : budget.lower ≤ first.norm := by
    rw [first.norm_eq, first.value_eq]
    exact budget.root_lower parent.left.parameter parent.left.inside parent.cached.preparedOwner first.index
  have firstInside := parent.cached.preparedOwner.certificate_candidate_in_initial_box
    parent.cached.preparedOwner.parameterNonzero sourceTail.state first.possible
  let target := parent.directQueryOwner fraction inside
  have secondInside := target.certificate_candidate_in_initial_box target.parameterNonzero targetTail.state
    second.possible
  have refines : target.track.initial.box.Refines parent.cached.preparedOwner.track.initial.box :=
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines _ _ _ _
  have sourceSmall : parent.cached.preparedOwner.track.initial.box.diagonalSq ≤ budget.rootDiameter := by
    rw [parent.cached.preparedOwner_eq]
    exact (Branches.PreparedSheetContinuation.prepared_diagonal_lt parent.segment parent.left parent.owner
      parent.request).le.trans diameterSmall
  have distance : normSq (second.value - first.value) ≤ first.norm / 1024 := by
    have bound := (parent.cached.preparedOwner.track.initial.box.normSq_sub_le_diagonalSq
      (refines.contains secondInside) firstInside).trans sourceSmall
    rw [budget.rootDiameter_eq] at bound
    rw [Gaussian.Norm.Basic.normSq_eq_canonical (second.value - first.value)] at bound
    exact bound.trans (div_1024_mono lower)
  let base := parent.segment.pointAt parent.left.parameter
  let finish := parent.segment.pointAt (parameterAt parent.left parent.request fraction)
  let variation := (Dense.Gaussian.Substitution.Affine.composeLine curve.polynomial base (finish - base) -
    Dense.Basic.DensePolynomial.constant (curve.polynomial.eval base)).normalize
  let data : EdgeData curve.polynomial first.value second.value base finish :=
    { rootNorm := first.norm
      rootNorm_eq := first.norm_eq
      distance := normSq (second.value - first.value)
      distance_eq := rfl
      residual := first.residualNorm
      residual_eq := first.residualNorm_eq
      variation := variation
      variation_eq := by intro time; rw [eval_normalize, eval_sub, eval_constant,
        Dense.Gaussian.Substitution.Affine.eval_composeLine]
      movementBound := budget.movementBudget
      movementBound_valid := by
        intro time timeInside
        rw [eval_normalize, eval_sub, eval_constant, Dense.Gaussian.Substitution.Affine.eval_composeLine]
        change normSq (curve.polynomial.eval (Rational.Affine.line (parent.segment.pointAt parent.left.parameter)
          (parent.segment.pointAt (parameterAt parent.left parent.request fraction) - parent.segment.pointAt
            parent.left.parameter) time) -
            curve.polynomial.eval (parent.segment.pointAt parent.left.parameter)) ≤ budget.movementBudget
        rw [line_to_query]
        have productInside : 0 ≤ time * fraction ∧ time * fraction ≤ 1 :=
          ⟨Rat.Fraction.Order.Arithmetic.mul_nonneg_direct timeInside.1 inside.1,
            (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct timeInside.2 inside.1).trans
              (by simpa only [_root_.one_mul] using inside.2)⟩
        have timeBound := Branches.PreparedSheetContinuation.parameterAt_inside
          parent.left parent.request parent.ordered (time * fraction) productInside
        have between := Branches.PreparedSheetContinuation.parameterAt_between
          parent.left parent.request parent.ordered (time * fraction) productInside
        have evaluation := Branches.ClearSheetContinuation.evaluation_variation_le parent.segment parent.within
          parent.left.parameter (parameterAt parent.left parent.request (time * fraction)) parent.left.inside timeBound
        rw [Gaussian.Norm.Basic.normSq_eq_canonical] at evaluation
        have reverse : normSq (curve.polynomial.eval (parent.segment.pointAt (parameterAt parent.left parent.request
          (time * fraction))) -
            curve.polynomial.eval (parent.segment.pointAt parent.left.parameter)) =
          normSq (curve.polynomial.eval (parent.segment.pointAt parent.left.parameter) -
            curve.polynomial.eval (parent.segment.pointAt (parameterAt parent.left parent.request (time * fraction))))
              := by
          simp only [normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
          ring1
        rw [reverse]
        exact evaluation.trans ((Branches.ClearSheetContinuation.variationBound_le_of_between
          parent.segment between.1 between.2).trans movementSmall) }
  refine ⟨data, budget.lower_positive.trans_le lower, distance, first.residual_small, ?_⟩
  change budget.movementBudget ≤ first.norm ^ 2 / 1024
  rw [budget.movementBudget_eq]
  exact div_1024_mono (Rat.Fraction.Order.Arithmetic.pow_le_pow_direct budget.lower_positive.le lower 2)

open Purelib.Riemann in
open Purelib.Data in
open Purelib.RootIsolation in
/-- Retain the original source handoff followed by the moving path to the actual query owner.

Use the same prepared edge and budget, acquire a tail of the existing direct query, and preserve both endpoint owners.
-/
def queryPath (budget : PreparedTraceBudget parent.segment left right)
    (diameterSmall : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movementSmall : Branches.ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter ≤ budget.movementBudget)
    (fraction : Rat.Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    OwnerPath curve.polynomial (parent.segment.pointAt parent.left.parameter) parent.owner
      (parent.segment.pointAt (parameterAt parent.left parent.request fraction)) (parent.directQueryOwner fraction
        inside) :=
  let sourceJoin :=
    SquareRoot.Preparation.Handoff.Trace.CachedSource.traceJoin parent.cached
  let targetTail := OwnerTail.acquire (parent.directQueryOwner fraction inside)
  let moving : OwnerLink curve.polynomial (parent.segment.pointAt parent.left.parameter)
      (parent.segment.pointAt (parameterAt parent.left parent.request fraction))
      parent.cached.preparedOwner (parent.directQueryOwner fraction inside) :=
    { leftTail := sourceJoin.rightTail
      rightTail := targetTail
      leftIndex := sourceJoin.rightTail.first
      rightIndex := targetTail.first
      left_ge := le_rfl
      right_ge := le_rfl
      realize := fun first second _ _ =>
        queryEdge budget diameterSmall movementSmall fraction inside first second }
  .cons (OwnerLink.stationary curve.polynomial (parent.segment.pointAt parent.left.parameter) sourceJoin)
    (.cons moving (.nil _ _))

open Purelib.Riemann in
open Purelib.Data in
/-- The retained query path has the original left coordinate followed by the queried coordinate. -/
theorem queryPath_vertices (budget : PreparedTraceBudget parent.segment left right)
    (diameterSmall : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movementSmall : Branches.ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter ≤ budget.movementBudget)
    (fraction : Rat.Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (queryPath budget diameterSmall movementSmall fraction inside).vertices =
      [parent.segment.pointAt parent.left.parameter, parent.segment.pointAt (parameterAt parent.left parent.request
        fraction)] := rfl

end PreparedTraceBudget

end Purelib.Riemann.Paths.PreparedQueryTraceEdges
