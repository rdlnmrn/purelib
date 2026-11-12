module

public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Paths.OwnerTraceReadings.Trace
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Paid trace links in one original aligned signed box

The two supplied Owners may have different radicands. Their actual initial
boxes refine the SAME original aligned seed box, so the original uniform
root and root-sum floors apply to both retained readings. The actual
polynomial variation and two executable residual requests pay the original
trace-edge conditions internally.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Cast (natCast_eq_fromInt)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy (parameterInterval)
open Purelib.Riemann.RootContinuation.SquareRootProvenance

/-- The genuine trace request lies below the original squared-root-floor-squared residual threshold. -/
theorem traceAllowance_le (lower : Rational) : traceAllowance lower ≤ lower ^ 2 / 1024 := by
  have coefficients : (8192 : Rational)⁻¹ ≤ 1024⁻¹ := by
    change (((8192 : Nat) : Rational))⁻¹ ≤ (((1024 : Nat) : Rational))⁻¹
    rewrite [natCast_eq_fromInt 8192, natCast_eq_fromInt 1024]
    decide +kernel
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficients
    (Order.Arithmetic.sq_nonneg_direct lower)
  exact (show traceAllowance lower = lower ^ 2 * (8192 : Rational)⁻¹ from
    Field.div_eq_mul_inv_direct _ _).trans_le
      (scaled.trans_eq (Field.div_eq_mul_inv_direct _ _).symm)

/-- Construct a genuine root-trace link between two GIVEN Owners inside the SAME original signed box.

Both complete residual requests are inputs already selected before any
reading. The polynomial variation is constructed once. Every later pair of
actual readings uses the original box root-sum bound and difference-of-
squares estimate; no endpoint root comparison is assumed or computed.
-/
def inBox {referencePolynomial polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count) (start finish : Canonical)
    (left : Owner (polynomial.eval start)) (right : Owner (polynomial.eval finish))
    (leftRefines : left.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (rightRefines : right.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (leftRequest : OwnerTail.TraceRequest left patch.rootLower patch.rootLower_positive)
    (rightRequest : OwnerTail.TraceRequest right patch.rootLower patch.rootLower_positive)
    (movement : ∀ time : Rational, parameterInterval.Contains time →
      Norm.Basic.normSq (polynomial.eval (Affine.line start (finish - start) time) - polynomial.eval start) ≤
        traceAllowance patch.rootLower) :
    OwnerLink polynomial start finish left right :=
  let variation := (Substitution.Affine.composeLine polynomial start (finish - start) -
    constant (polynomial.eval start)).normalize
  { leftTail := leftRequest.tail
    rightTail := rightRequest.tail
    leftIndex := leftRequest.compared.leftIndex
    rightIndex := rightRequest.compared.leftIndex
    left_ge := leftRequest.compared.left_ge
    right_ge := rightRequest.compared.left_ge
    realize := fun first last firstLater lastLater => by
      have firstInside := leftRefines.contains
        (left.certificate_candidate_in_initial_box left.parameterNonzero leftRequest.tail.state first.possible)
      have lastInside := rightRefines.contains
        (right.certificate_candidate_in_initial_box right.parameterNonzero rightRequest.tail.state last.possible)
      have firstLower : patch.rootLower ≤ Norm.Basic.normSq first.value := by
        rewrite [Norm.Basic.normSq_eq_canonical]
        exact patch.root_lower firstInside
      have sumLower : 4 * patch.rootLower ≤ Norm.Basic.normSq (first.value + last.value) := by
        rewrite [Norm.Basic.normSq_eq_canonical]
        exact patch.root_sum_lower firstInside lastInside
      have endpoint := movement 1 ⟨by decide +kernel, Order.Basic.le_refl _⟩
      have lastPoint : Affine.line start (finish - start) (1 : Rational) = finish :=
        Affine.line_one start finish
      rewrite [lastPoint] at endpoint
      have reverseMovement := (Norm.Bounds.normSq_sub_symm
        (polynomial.eval start) (polynomial.eval finish)).trans_le endpoint
      have distance := trace_distance_le first.value last.value (polynomial.eval start) (polynomial.eval finish)
        patch.rootLower_positive firstLower sumLower
        (leftRequest.residual first firstLater).le reverseMovement (rightRequest.residual last lastLater).le
      rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at distance
      let data : EdgeData polynomial first.value last.value start finish :=
        { rootNorm := first.norm
          rootNorm_eq := first.norm_eq
          distance := Canonical.normSq (last.value - first.value)
          distance_eq := rfl
          residual := first.residualNorm
          residual_eq := first.residualNorm_eq
          variation := variation
          variation_eq := by
            intro time
            rewrite [eval_normalize, eval_sub, eval_constant, Substitution.Affine.eval_composeLine]
            rfl
          movementBound := traceAllowance patch.rootLower
          movementBound_valid := by
            intro time inside
            rewrite [eval_normalize, eval_sub, eval_constant, Substitution.Affine.eval_composeLine]
            rewrite [← Norm.Basic.normSq_eq_canonical]
            exact movement time inside }
      have lower : patch.rootLower ≤ first.norm :=
        firstLower.trans_eq ((Norm.Basic.normSq_eq_canonical first.value).trans first.norm_eq.symm)
      exact ⟨data, patch.rootLower_positive.trans_le lower,
        distance.trans_eq (congrArg (fun value : Rational => value / 1024) first.norm_eq.symm),
        first.residual_small, (traceAllowance_le patch.rootLower).trans
          (Order.Field.divide_mono
            (Order.Arithmetic.pow_le_pow_direct patch.rootLower_positive.le lower 2) (by
              change (0 : Rational) < ((1024 : Nat) : Rational)
              rewrite [natCast_eq_fromInt 1024]
              decide +kernel))⟩ }

variable {referencePolynomial polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count) (start finish : Canonical)
    (left : Owner (polynomial.eval start)) (right : Owner (polynomial.eval finish))
    (leftRefines : left.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (rightRefines : right.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (leftRequest : OwnerTail.TraceRequest left patch.rootLower patch.rootLower_positive)
    (rightRequest : OwnerTail.TraceRequest right patch.rootLower patch.rootLower_positive)
    (movement : ∀ time : Rational, parameterInterval.Contains time →
      Norm.Basic.normSq (polynomial.eval (Affine.line start (finish - start) time) - polynomial.eval start) ≤
        traceAllowance patch.rootLower)

/-- The actual box-paid link keeps the SAME original selected left residual floor. -/
theorem inBox_leftIndex :
    (inBox patch start finish left right leftRefines rightRefines leftRequest rightRequest movement).leftIndex =
      leftRequest.compared.leftIndex := by
  unfold inBox
  rfl

/-- The actual box-paid link keeps the SAME original selected right residual floor. -/
theorem inBox_rightIndex :
    (inBox patch start finish left right leftRefines rightRefines leftRequest rightRequest movement).rightIndex =
      rightRequest.compared.leftIndex := by
  unfold inBox
  rfl


end Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

end
