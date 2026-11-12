module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Geometry.Rational.Box.Sum
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Fixed-point parameter continuation from an actual original source query

The original continued Point supplies the full cubic root owner. Its actual
contour clearance and nonzero radicand norm compute a positive parameter
increment bound. Direct transport of that owner retains its sheet box at the
same physical point; no root is re-isolated and no cofactor is replaced.

Paid source and target observations remain in the original aligned seed box.
Its whole-box root lower bound derives both candidate margins and the sum
margin internally, feeding the original scalar inverse/cubic Taylor caches.
Comparison to an independently prepared changed-parameter spatial patch is
additional evidence, not a consequence of point or sheet labels.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Clearance

variable {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (source : ContinuedNeighborhood.Point patch point)

/-- The original point's exact polynomial representation evaluates to the original scalar Legendre cubic. -/
theorem radicand_eq (parameter point : Canonical) :
    (Paths.polynomial parameter).eval point = Polynomials.curveValue parameter point := by
  rewrite [Paths.polynomial_eval]
  rfl

/-- The original contour and nonzero-radicand clearances determine one positive transport budget. -/
@[expose] def transportBudget : Rational := min source.owner.track.initial.clearance.bound source.parameterNorm

/-- Both original finite clearances make the computed transport budget positive. -/
theorem transportBudget_positive : 0 < transportBudget source :=
  Order.Basic.lt_min source.owner.track.initial.clearance.positive source.parameterNorm_positive

/-- The original affine radicand coefficient determines an admitted squared parameter-increment bound. -/
@[expose] def incrementBound : Rational :=
  min 1 (transportBudget source / (Norm.Basic.normSq (Polynomials.baseValue point) + 1))

/-- The computed same-point parameter-increment bound is strictly positive. -/
theorem incrementBound_positive : 0 < incrementBound source :=
  Order.Basic.lt_min (by decide +kernel) (Order.Field.div_pos_direct (transportBudget_positive source)
    (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Norm.Basic.normSq_nonneg _) (by decide +kernel)))

/-- The admitted increment bound also pays the original scalar unit-increment condition. -/
theorem incrementBound_le_one : incrementBound source ≤ 1 := Order.Basic.min_le_left _ _

/-- The exact same-point radicand movement pays both original contour and nonzero-parameter clearances. -/
theorem movement_lt (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ incrementBound source) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point) < transportBudget source := by
  have identity : (Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point = increment * Polynomials.baseValue point := by
    rewrite [radicand_eq, radicand_eq, Variation.radicand_step]
    ring1
  rewrite [identity, Norm.Basic.normSq_mul]
  have paid := Order.Field.mul_min_one_div_lt (Norm.Basic.normSq_nonneg (Polynomials.baseValue point))
    (transportBudget_positive source)
  have product := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct admitted
    (Norm.Basic.normSq_nonneg (Polynomials.baseValue point))
  calc
    _ ≤ incrementBound source * Norm.Basic.normSq (Polynomials.baseValue point) := product
    _ = Norm.Basic.normSq (Polynomials.baseValue point) *
        min 1 (transportBudget source / (Norm.Basic.normSq (Polynomials.baseValue point) + 1)) := by
          unfold incrementBound
          ring1
    _ < transportBudget source := paid

/-- The admitted same-point parameter perturbation preserves nonzeroness of the actual target radicand. -/
theorem target_nonzero (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ incrementBound source) :
    (Paths.polynomial (parameter + increment)).eval point ≠ 0 := by
  intro zero
  have movement := (movement_lt source increment admitted).trans_le (Order.Basic.min_le_right _ _)
  rewrite [zero, Basic.sub_zero, Norm.Basic.normSq_eq_canonical, ← source.parameterNorm_eq] at movement
  exact movement.2 (Order.Basic.le_refl _)

/-- The same admitted perturbation pays the original source owner's exact contour-clearance request. -/
theorem movement_lt_contour (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ incrementBound source) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval point -
      (Paths.polynomial (parameter + increment)).eval point) < source.owner.track.initial.clearance.bound :=
  (movement_lt source increment admitted).trans_le (Order.Basic.min_le_left _ _)

set_option genInjectivity false in
/-- An actual full-cubic target owner and cached certificate continuing the original point at the same spatial input.

The increment is paid by the original source-owner clearances. The target
initial box refines that same owner's original box; its cached certificate
is retained whole and refers to the exact changed radicand.
-/
structure Step (increment : Canonical) where
  /-- The original geometric increment request is paid. -/ admitted :
    Norm.Basic.normSq increment ≤ incrementBound source
  /-- The actual changed-radicand owner, without root re-isolation. -/ owner :
    Owner ((Paths.polynomial (parameter + increment)).eval point)
  /-- The actual target initial box refines the original source owner's initial box. -/ refines :
    owner.track.initial.box.Refines source.owner.track.initial.box
  /-- The cached complete certificate of that actual changed-radicand owner. -/ root :
    CertifiedSquareRoot.Certificate ((Paths.polynomial (parameter + increment)).eval point)
  /-- The certificate consumes that exact retained target owner. -/ root_eq :
    root = owner.certificate owner.parameterNonzero

constructive_injectivity Step

/-- Advance the actual original full-cubic point owner using its internally computed finite increment payment. -/
def advance (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ incrementBound source) :
    Step source increment :=
  let owner := ExactQuadraticOwnerClearance.directTransport source.owner (target_nonzero source increment admitted)
    (movement_lt_contour source increment admitted)
  let refines := ExactQuadraticOwnerClearance.directTransport_initial_box_refines source.owner
    (target_nonzero source increment admitted) (movement_lt_contour source increment admitted)
  let root := owner.certificate owner.parameterNonzero
  ⟨admitted, owner, refines, root, rfl⟩

namespace Step

variable {source} {increment : Canonical} (step : Step source increment)

/-- The original admitted point step pays the scalar Taylor unit-increment condition. -/
theorem unit (step : Step source increment) : Norm.Basic.normSq increment ≤ 1 :=
  step.admitted.trans (incrementBound_le_one source)

/-- Both exact original observations and their internally derived candidate/sum clearance at one actual accuracy. -/
@[expose] def Readings (accuracy : AccuracyRequest) :=
  (first : CertifiedSquareRoot.Sampling.ResidualObservation source.certificate accuracy) ×
  (last : CertifiedSquareRoot.Sampling.ResidualObservation step.root accuracy) ×
    CertifiedSquareRoot.Sampling.Clearance first last

/-- Derive all three positive margins for two already retained actual source and target observations.

The observation requests and selected states remain independent. Every
candidate stays in the original source seed box by actual owner refinement;
its whole-box root lower bound pays source, target and sum separation.
-/
def clearance {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : CertifiedSquareRoot.Sampling.ResidualObservation source.certificate firstAccuracy)
    (last : CertifiedSquareRoot.Sampling.ResidualObservation step.root lastAccuracy) :
    CertifiedSquareRoot.Sampling.Clearance first last := by
  have firstInside : ∀ {candidate : Canonical}, first.observation.Possible candidate →
      patch.base.seed.owner.track.initial.box.Contains candidate := by
    intro candidate possible
    rewrite [first.observation_eq] at possible
    exact source.candidate_inside first.state possible
  have lastInside : ∀ {candidate : Canonical}, last.observation.Possible candidate →
      patch.base.seed.owner.track.initial.box.Contains candidate := by
    intro candidate possible
    rewrite [last.observation_eq] at possible
    exact source.refines.contains (step.refines.contains
      (CertifiedSquareRoot.Sampling.candidate_in_initial_box step.owner step.root_eq possible))
  exact
    { sourceFloor := patch.rootLower
      sourcePositive := patch.rootLower_positive
      sourceLower := fun possible => by
        rewrite [Norm.Basic.normSq_eq_canonical]
        exact patch.root_lower (firstInside possible)
      targetFloor := patch.rootLower
      targetPositive := patch.rootLower_positive
      targetLower := fun possible => by
        rewrite [Norm.Basic.normSq_eq_canonical]
        exact patch.root_lower (lastInside possible)
      sumFloor := 4 * patch.rootLower
      sumPositive := Order.Arithmetic.mul_pos_direct (by decide +kernel) patch.rootLower_positive
      sumLower := fun firstPossible lastPossible => by
        rewrite [Norm.Basic.normSq_eq_canonical]
        exact patch.root_sum_lower (firstInside firstPossible) (lastInside lastPossible) }

/-- The actual point-step clearance retains its original seed-box sourceFloor, independently of request accuracy. -/
theorem clearance_sourceFloor {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : CertifiedSquareRoot.Sampling.ResidualObservation source.certificate firstAccuracy)
    (last : CertifiedSquareRoot.Sampling.ResidualObservation step.root lastAccuracy) :
    (step.clearance first last).sourceFloor = patch.rootLower := by
  unfold clearance
  rfl

/-- The actual point-step clearance retains its original seed-box targetFloor, independently of request accuracy. -/
theorem clearance_targetFloor {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : CertifiedSquareRoot.Sampling.ResidualObservation source.certificate firstAccuracy)
    (last : CertifiedSquareRoot.Sampling.ResidualObservation step.root lastAccuracy) :
    (step.clearance first last).targetFloor = patch.rootLower := by
  unfold clearance
  rfl

/-- The actual point-step clearance retains its original seed-box sumFloor, independently of request accuracy. -/
theorem clearance_sumFloor {firstAccuracy lastAccuracy : AccuracyRequest}
    (first : CertifiedSquareRoot.Sampling.ResidualObservation source.certificate firstAccuracy)
    (last : CertifiedSquareRoot.Sampling.ResidualObservation step.root lastAccuracy) :
    (step.clearance first last).sumFloor = 4 * patch.rootLower := by
  unfold clearance
  rfl

/-- Request both actual full-root observations and derive their positive same-seed-box margins internally.

Each original process is requested once. The same cached observations feed
the shared candidate clearance without another request or root selection.
-/
def request (accuracy : AccuracyRequest) : Readings step accuracy :=
  let first := CertifiedSquareRoot.Sampling.request source.certificate accuracy
  let last := CertifiedSquareRoot.Sampling.request step.root accuracy
  ⟨first, last, step.clearance first last⟩

/-- Construct the existing same-point inverse/cubic scalar Taylor banks on the actual source and transported target.

The fourth-order root-residual request is computed from the original nonzero
increment. Exact parameter casts retain the complete two observations and
clearance, including original processes, states, readings and indices.
-/
def jet (nonzero : increment ≠ 0) : Sampling.SampledJet parameter increment point
    (source.certificate.castParameter (radicand_eq parameter point))
    (step.root.castParameter (radicand_eq (parameter + increment) point)) step.unit :=
  let accuracy := Sampling.incrementRequest increment nonzero
  let readings := step.request accuracy
  let first := readings.1.castParameter (radicand_eq parameter point)
  let last := readings.2.1.castParameter (radicand_eq (parameter + increment) point)
  let clearance := readings.2.2.castParameters (radicand_eq parameter point)
    (radicand_eq (parameter + increment) point)
  Sampling.ofObservations parameter increment point _ _ accuracy rfl first last clearance step.unit

end Step

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point

end
