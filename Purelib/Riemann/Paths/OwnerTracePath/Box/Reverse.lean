module

public import Purelib.Riemann.Paths.OwnerTracePath.Box
public import Purelib.Riemann.Paths.OwnerTracePath.Reverse
import Purelib.Riemann.Paths.OwnerTraceReadings.Trace
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast.Order
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
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-! # Reverse links from the original full-interval variation payment

The reverse direction has its own actual chord movement hypothesis. The
same signed-box norm and sum bounds, two original residual requests and
complete native readings derive its Small certificate internally. Its
displacement cache is the original GIVEN checked forward cache verbatim.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootTrace
open Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy (parameterInterval)
open Purelib.Riemann.RootContinuation.SquareRootProvenance

/-- Reverse an actual box-paid link using its SAME requests/readings and genuinely paid reverse movement.

No root, request, comparison or reading producer runs. The signed sum lower
bound is applied in the reverse order. Norm/residual caches are the given
last reading's original caches, and distance is the given forward edge's
complete cache; only the reverse variation polynomial is constructed.
-/
def reverseInBox {referencePolynomial polynomial : CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood referencePolynomial count) (start finish : Canonical)
    (left : Owner (polynomial.eval start)) (right : Owner (polynomial.eval finish))
    (leftRefines : left.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (rightRefines : right.track.initial.box.Refines patch.base.seed.owner.track.initial.box)
    (leftRequest : OwnerTail.TraceRequest left patch.rootLower patch.rootLower_positive)
    (rightRequest : OwnerTail.TraceRequest right patch.rootLower patch.rootLower_positive)
    (forwardMovement : ∀ time : Rational, parameterInterval.Contains time →
      Norm.Basic.normSq (polynomial.eval (Affine.line start (finish - start) time) - polynomial.eval start) ≤
        traceAllowance patch.rootLower)
    (reverseMovement : ∀ time : Rational, parameterInterval.Contains time →
      Norm.Basic.normSq (polynomial.eval (Affine.line finish (start - finish) time) - polynomial.eval finish) ≤
        traceAllowance patch.rootLower) :
    ReverseData (inBox patch start finish left right leftRefines rightRefines
      leftRequest rightRequest forwardMovement) := by
  intro first last firstLater lastLater forward
  have firstPaid : leftRequest.compared.leftIndex ≤ first.index :=
    (inBox_leftIndex patch start finish left right leftRefines rightRefines
      leftRequest rightRequest forwardMovement).symm.trans_le firstLater
  have lastPaid : rightRequest.compared.leftIndex ≤ last.index :=
    (inBox_rightIndex patch start finish left right leftRefines rightRefines
      leftRequest rightRequest forwardMovement).symm.trans_le lastLater
  let firstReading := first.inTail leftRequest.tail (leftRequest.compared.left_ge.trans firstPaid)
  let lastReading := last.inTail rightRequest.tail (rightRequest.compared.left_ge.trans lastPaid)
  have firstInside := leftRefines.contains
    (left.certificate_candidate_in_initial_box left.parameterNonzero leftRequest.tail.state firstReading.possible)
  have lastInside := rightRefines.contains
    (right.certificate_candidate_in_initial_box right.parameterNonzero rightRequest.tail.state lastReading.possible)
  have lastLower : patch.rootLower ≤ Norm.Basic.normSq last.value := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact patch.root_lower lastInside
  have sumLower : 4 * patch.rootLower ≤ Norm.Basic.normSq (last.value + first.value) := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact patch.root_sum_lower lastInside firstInside
  have endpoint := reverseMovement 1 ⟨by decide +kernel, Order.Basic.le_refl _⟩
  have firstPoint : Affine.line finish (start - finish) (1 : Rational) = start := Affine.line_one finish start
  rewrite [firstPoint] at endpoint
  have movement := (Norm.Bounds.normSq_sub_symm (polynomial.eval finish) (polynomial.eval start)).trans_le endpoint
  have distance := trace_distance_le last.value first.value (polynomial.eval finish) (polynomial.eval start)
    patch.rootLower_positive lastLower sumLower
    (rightRequest.residual lastReading lastPaid).le movement (leftRequest.residual firstReading firstPaid).le
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at distance
  have symmetry : Canonical.normSq (last.value - first.value) = Canonical.normSq (first.value - last.value) := by
    rewrite [← Canonical.normSq_neg (first.value - last.value)]
    congr 1
    ring1
  have distanceEq := forward.data.distance_eq.trans symmetry
  let variation := (Substitution.Affine.composeLine polynomial finish (start - finish) -
    constant (polynomial.eval finish)).normalize
  let data : EdgeData polynomial last.value first.value finish start :=
    { rootNorm := last.reading.norm
      rootNorm_eq := last.reading.norm_eq
      distance := forward.data.distance
      distance_eq := distanceEq
      residual := last.reading.residualNorm
      residual_eq := last.reading.residualNorm_eq
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
        exact reverseMovement time inside }
  have lower : patch.rootLower ≤ last.reading.norm :=
    lastLower.trans_eq ((Norm.Basic.normSq_eq_canonical last.value).trans last.reading.norm_eq.symm)
  let backward : Edge polynomial last.value first.value finish start :=
    ⟨data, patch.rootLower_positive.trans_le lower,
      distanceEq.trans_le (distance.trans_eq
        (congrArg (fun value : Rational => value / 1024) last.reading.norm_eq.symm)),
      last.reading.residual_small, (traceAllowance_le patch.rootLower).trans
        (Order.Field.divide_mono
          (Order.Arithmetic.pow_le_pow_direct patch.rootLower_positive.le lower 2)
            (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by decide +kernel)))⟩
  exact ⟨backward, rfl, rfl, rfl⟩

end Purelib.Riemann.Paths.OwnerTracePath.OwnerLink

end
