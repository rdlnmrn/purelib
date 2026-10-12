module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Moving trace edges from actual prepared owners

The prepared source's requested box diameter bounds every pair of source and
transported endpoint readings.  The existing segment-variation certificate
bounds the polynomial on the entire base chord.  Together with the actual
owner residual tails, these construct the finite square-root trace edge.
-/

namespace Purelib.Riemann.Paths.PreparedTraceEdges

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerTail)

open Purelib.Riemann.RootContinuation.SquareRootTrace

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Path
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest parameterAt)

/-- The original rational Gaussian box carrier. -/
public abbrev Box := Purelib.Geometry.Rational.Box

open Purelib.Data.Rat in
/-- Division by the positive rational 1024 preserves the original weak inequality. -/
public theorem div_1024_mono {left right : Fraction.Rational} (bound : left ≤ right) :
    left / 1024 ≤ right / 1024 := by
  apply (Fraction.Order.Field.div_le_iff_pos
    (by decide +kernel : (0 : Fraction.Rational) < 1024)).mpr
  rw [Fraction.Field.div_mul_cancel_of_ne _ _
    (by decide +kernel : (1024 : Fraction.Rational) ≠ 0)]
  exact bound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- The affine line between the original requested segment endpoints equals the exact prepared request parameterization.
-/
private theorem line_pointAt {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {start finish : Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (time : Fraction.Rational) :
    Affine.line (segment.pointAt current.parameter)
      (segment.pointAt request.endpoint.parameter - segment.pointAt current.parameter) time =
        segment.pointAt (parameterAt current request time) := by
  apply Basic.ext <;>
    simp only [PreparedSheetContinuation.parameterAt_eq_affine,
      Affine.line, Geometry.ClearPath.ClearSegment.pointAt, Scale.scale_re, Scale.scale_im,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re,
        Basic.mul_im] <;>
    ring1

namespace PreparedTraceBudget

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment polynomial ambient start finish} {left right : Endpoint}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Construct a certified root trace edge from the original prepared-source and transported-target readings.

The exact cached source, request and retained diameter/movement bounds place both readings in the original prepared box.
Their cached norm and residual data and the original segment variation certify the trace smallness conditions. -/
def edge (budget : PreparedTraceBudget segment left right)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (request : StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment current owner request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (safe : ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        (PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound)
    (diameterSmall : request.rootDiameter ≤ budget.rootDiameter)
    (movementSmall : ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter ≤ budget.movementBudget)
    {sourceTail : OwnerTail cached.preparedOwner}
    {targetTail : OwnerTail (PreparedSheetContinuation.transported segment within current owner request safe)}
    (first : OwnerTail.Reading sourceTail) (second : OwnerTail.Reading targetTail) :
    Edge polynomial first.value second.value
      (segment.pointAt current.parameter) (segment.pointAt request.endpoint.parameter) := by
  have lower : budget.lower ≤ first.norm := by
    rw [first.norm_eq, first.value_eq]
    exact budget.root_lower current.parameter current.inside cached.preparedOwner first.index
  have firstInside := cached.preparedOwner.certificate_candidate_in_initial_box
    cached.preparedOwner.parameterNonzero sourceTail.state first.possible
  let target := PreparedSheetContinuation.transported segment within current owner request safe
  have secondInside := target.certificate_candidate_in_initial_box target.parameterNonzero targetTail.state
    second.possible
  have targetRefines : target.track.initial.box.Refines cached.preparedOwner.track.initial.box := by
    rw [cached.preparedOwner_eq]
    exact ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines _ _ _ _
  have sourceSmall : cached.preparedOwner.track.initial.box.diagonalSq ≤ budget.rootDiameter := by
    rw [cached.preparedOwner_eq]
    exact (PreparedSheetContinuation.prepared_diagonal_lt segment current owner request).le.trans diameterSmall
  have distance : normSq (second.value - first.value) ≤ first.norm / 1024 := by
    have bound := (cached.preparedOwner.track.initial.box.normSq_sub_le_diagonalSq
      (targetRefines.contains secondInside) firstInside).trans sourceSmall
    rw [budget.rootDiameter_eq, Norm.Basic.normSq_eq_canonical] at bound
    exact bound.trans (div_1024_mono lower)
  let base := segment.pointAt current.parameter
  let finish := segment.pointAt request.endpoint.parameter
  let variation := (Substitution.Affine.composeLine polynomial base (finish - base) -
    Dense.Basic.DensePolynomial.constant (polynomial.eval base)).normalize
  let data : EdgeData polynomial first.value second.value base finish :=
    { rootNorm := first.norm
      rootNorm_eq := first.norm_eq
      distance := normSq (second.value - first.value)
      distance_eq := rfl
      residual := first.residualNorm
      residual_eq := first.residualNorm_eq
      variation := variation
      variation_eq := by
        intro time
        rw [Dense.Basic.DensePolynomial.eval_normalize, Dense.Basic.DensePolynomial.eval_sub,
          Dense.Basic.DensePolynomial.eval_constant, Substitution.Affine.eval_composeLine]
      movementBound := budget.movementBudget
      movementBound_valid := by
        intro time inside
        rw [Dense.Basic.DensePolynomial.eval_normalize, Dense.Basic.DensePolynomial.eval_sub,
          Dense.Basic.DensePolynomial.eval_constant, Substitution.Affine.eval_composeLine]
        change normSq (polynomial.eval (Affine.line (segment.pointAt current.parameter)
          (segment.pointAt request.endpoint.parameter - segment.pointAt current.parameter) time) -
            polynomial.eval (segment.pointAt current.parameter)) ≤ budget.movementBudget
        rw [line_pointAt]
        have timeInside := PreparedSheetContinuation.parameterAt_inside current request ordered time inside
        have between := PreparedSheetContinuation.parameterAt_between current request ordered time inside
        have evaluation := ClearSheetContinuation.evaluation_variation_le segment within
          current.parameter (parameterAt current request time) current.inside timeInside
        rw [Norm.Basic.normSq_eq_canonical] at evaluation
        have reverse : normSq (polynomial.eval (segment.pointAt (parameterAt current request time)) -
            polynomial.eval (segment.pointAt current.parameter)) =
          normSq (polynomial.eval (segment.pointAt current.parameter) -
            polynomial.eval (segment.pointAt (parameterAt current request time))) := by
          simp only [normSq, Basic.sub_re, Basic.sub_im]
          ring1
        rw [reverse]
        exact evaluation.trans ((ClearSheetContinuation.variationBound_le_of_between
          segment between.1 between.2).trans movementSmall) }
  refine ⟨data, budget.lower_positive.trans_le lower, distance, first.residual_small, ?_⟩
  change budget.movementBudget ≤ first.norm ^ 2 / 1024
  rw [budget.movementBudget_eq]
  exact div_1024_mono (Fraction.Order.Arithmetic.pow_le_pow_direct budget.lower_positive.le lower 2)

end PreparedTraceBudget

end Purelib.Riemann.Paths.PreparedTraceEdges
