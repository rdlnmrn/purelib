module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Bounds
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table.Reading
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation.Rows
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Taylor banks between two retained continuations from one original query

The two absolute parameter Steps have the SAME original Point as nominal
parent. Their retained refinements put both candidate families in that
Point's original seed box. The original scalar/evaluator Taylor machinery
therefore applies at the first shifted parameter to the difference of the
two offsets, without a second local continuation or a later patch range.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter point firstOffset lastOffset : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point}

/-- The first shifted parameter plus the exact offset difference is the second shifted parameter. -/
theorem betweenParameter_eq (parameter firstOffset lastOffset : Canonical) :
    parameter + firstOffset + (lastOffset - firstOffset) = parameter + lastOffset := by ring1

/-- The second absolute continuation has the exact radicand of the first parameter plus their offset difference. -/
theorem betweenRadicand_eq (parameter point firstOffset lastOffset : Canonical) :
    (Paths.polynomial (parameter + lastOffset)).eval point =
      Polynomials.curveValue (parameter + firstOffset + (lastOffset - firstOffset)) point := by
  have same : parameter + lastOffset = parameter + firstOffset + (lastOffset - firstOffset) := by ring1
  exact (congrArg (fun value => (Paths.polynomial value).eval point) same).trans (radicand_eq _ point)

/-- Two retained absolute Steps pay the source, target and paired-sum floors of their SAME original seed box.

The observations can have independent requests and selected states. Their
own certificate factory equations and actual Step refinements prove each
candidate containment; no desired inter-step root relation is an input.
-/
def betweenClearance (first : Step source firstOffset) (last : Step source lastOffset)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root firstAccuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root lastAccuracy) :
    CertifiedSquareRoot.Sampling.Clearance firstObserved lastObserved := by
  have firstInside : ∀ {candidate : Canonical}, firstObserved.observation.Possible candidate →
      patch.base.seed.owner.track.initial.box.Contains candidate := by
    intro candidate possible
    rewrite [firstObserved.observation_eq] at possible
    exact source.refines.contains (first.refines.contains
      (CertifiedSquareRoot.Sampling.candidate_in_initial_box first.owner first.root_eq possible))
  have lastInside : ∀ {candidate : Canonical}, lastObserved.observation.Possible candidate →
      patch.base.seed.owner.track.initial.box.Contains candidate := by
    intro candidate possible
    rewrite [lastObserved.observation_eq] at possible
    exact source.refines.contains (last.refines.contains
      (CertifiedSquareRoot.Sampling.candidate_in_initial_box last.owner last.root_eq possible))
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

/-- The original paired clearance retains the SAME original seed floor as its source margin. -/
theorem betweenClearance_sourceFloor (first : Step source firstOffset) (last : Step source lastOffset)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root firstAccuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root lastAccuracy) :
    (betweenClearance first last firstObserved lastObserved).sourceFloor = patch.rootLower := by
  unfold betweenClearance
  rfl

/-- The original paired clearance retains that SAME original seed floor as its target margin. -/
theorem betweenClearance_targetFloor (first : Step source firstOffset) (last : Step source lastOffset)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root firstAccuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root lastAccuracy) :
    (betweenClearance first last firstObserved lastObserved).targetFloor = patch.rootLower := by
  unfold betweenClearance
  rfl

/-- The paired sum margin is four times the identical original seed floor. -/
theorem betweenClearance_sumFloor (first : Step source firstOffset) (last : Step source lastOffset)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root firstAccuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root lastAccuracy) :
    (betweenClearance first last firstObserved lastObserved).sumFloor = 4 * patch.rootLower := by
  unfold betweenClearance
  rfl

/-- The exact original sampled-jet type at the first shifted parameter and the difference of the two offsets.

Only original certificates are reindexed by exact radicand equalities.
The two Step owners and their common old Point remain indices; this type
alias constructs no owner, comparison, observation or scalar certificate.
-/
@[expose] def BetweenCore (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) :=
  Sampling.SampledJet (parameter + firstOffset) (lastOffset - firstOffset) point
    (first.root.castParameter (radicand_eq (parameter + firstOffset) point))
    (last.root.castParameter (betweenRadicand_eq parameter point firstOffset lastOffset)) unit

/-- Construct a genuine difference-offset Taylor core on the supplied two retained paid root observations.

The actual first and last Steps are consumed without continuation replay.
The existing inverse/cubic constructor is centered at parameter+firstOffset;
its remainder scale is the FOURTH power of lastOffset-firstOffset, not of
either absolute offset. Shared seed-box floors pay the paired denominator.
-/
@[expose] def betweenOfObservations (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    BetweenCore first last unit :=
  let clearance := betweenClearance first last firstObserved lastObserved
  Sampling.ofObservations (parameter + firstOffset) (lastOffset - firstOffset) point _ _ accuracy paid
    (firstObserved.castParameter (radicand_eq (parameter + firstOffset) point))
    (lastObserved.castParameter (betweenRadicand_eq parameter point firstOffset lastOffset))
    (clearance.castParameters (radicand_eq (parameter + firstOffset) point)
      (betweenRadicand_eq parameter point firstOffset lastOffset)) unit

/-- The between-step scalar core retains the original seed-box source floor. -/
theorem betweenOfObservations_sourceFloor (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.sourceFloor =
      patch.rootLower := by
  unfold betweenOfObservations
  rewrite [Sampling.ofObservations_clearance, CertifiedSquareRoot.Sampling.Clearance.castParameters_sourceFloor]
  exact betweenClearance_sourceFloor first last firstObserved lastObserved

/-- The between-step scalar core retains the original seed-box target floor. -/
theorem betweenOfObservations_targetFloor (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.targetFloor =
      patch.rootLower := by
  unfold betweenOfObservations
  rewrite [Sampling.ofObservations_clearance, CertifiedSquareRoot.Sampling.Clearance.castParameters_targetFloor]
  exact betweenClearance_targetFloor first last firstObserved lastObserved

/-- The between-step scalar core retains four times the original seed-box floor for paired sums. -/
theorem betweenOfObservations_sumFloor (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.sumFloor =
      4 * patch.rootLower := by
  unfold betweenOfObservations
  rewrite [Sampling.ofObservations_clearance, CertifiedSquareRoot.Sampling.Clearance.castParameters_sumFloor]
  exact betweenClearance_sumFloor first last firstObserved lastObserved

/-- The whole supplied source observation is retained after its exact radicand-index transport. -/
theorem betweenOfObservations_sourceSample (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).sourceSample =
      firstObserved.castParameter (radicand_eq (parameter + firstOffset) point) := by
  unfold betweenOfObservations
  exact Sampling.ofObservations_sourceSample _ _ _ _ _ _ _ _ _ _ _

/-- The whole supplied target observation retains its own state, request and selected comparison indices. -/
theorem betweenOfObservations_targetSample (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy) :
    (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).targetSample =
      lastObserved.castParameter (betweenRadicand_eq parameter point firstOffset lastOffset) := by
  unfold betweenOfObservations
  exact Sampling.ofObservations_targetSample _ _ _ _ _ _ _ _ _ _ _

section Bounds

variable (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1)
    (accuracy : AccuracyRequest) (paid : accuracy.tolerance = Norm.Basic.normSq (lastOffset - firstOffset) ^ 2)
    (firstObserved : CertifiedSquareRoot.Sampling.ResidualObservation first.root accuracy)
    (lastObserved : CertifiedSquareRoot.Sampling.ResidualObservation last.root accuracy)
    (arithmetic : Arithmetic.Observations
      (betweenOfObservations first last unit accuracy paid firstObserved lastObserved))

/-- Actual value arithmetic readings at the two shifted parameters have the SAME original-box factor ceiling.

The scalar identity changes only numerical coefficient-table readouts.
Both actual parameter-indexed differentials and both observation owners
remain distinct. No factor field is replaced by this stronger inequality.
-/
theorem between_value_factor_le (coordinate : Fin 2) (inside : patch.box.Contains point) :
    (arithmetic.valueCertificate coordinate).factor ≤ Joint.valueCeiling patch 0 coordinate := by
  have original := arithmetic.value_factor_le coordinate inside
  have ceiling : Arithmetic.valueCeiling (parameter + firstOffset) (lastOffset - firstOffset) coordinate patch.box
      (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.sourceFloor
      (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.targetFloor
      (betweenOfObservations first last unit accuracy paid firstObserved lastObserved).clearance.sumFloor =
      Joint.valueCeiling patch 0 coordinate := by
    rewrite [betweenOfObservations_sourceFloor, betweenOfObservations_targetFloor, betweenOfObservations_sumFloor]
    exact Arithmetic.valueCeiling_parameters (parameter + firstOffset) (lastOffset - firstOffset)
      parameter 0 coordinate patch.box patch.rootLower patch.rootLower (4 * patch.rootLower)
  exact original.trans_eq ceiling

/-- Actual first arithmetic readings retain their original inverse/cubic caches and original-box factor ceiling. -/
theorem between_first_factor_le (coordinate : Fin 2) (inside : patch.box.Contains point) :
    (arithmetic.firstCertificate coordinate).factor ≤ Joint.firstCeiling patch 0 coordinate := by
  let core := betweenOfObservations first last unit accuracy paid firstObserved lastObserved
  have firstFloor : patch.rootLower ≤ Norm.Basic.normSq core.sourceSample.reading :=
    (betweenOfObservations_sourceFloor first last unit accuracy paid firstObserved lastObserved).symm.trans_le
      core.clearance.source_normSq_lower
  have lastFloor : patch.rootLower ≤ Norm.Basic.normSq core.targetSample.reading :=
    (betweenOfObservations_targetFloor first last unit accuracy paid firstObserved lastObserved).symm.trans_le
      core.clearance.target_normSq_lower
  have firstInverse : (Joint.inverseBox patch).Contains core.sourceSample.reading⁻¹ :=
    Geometry.Rational.Box.Square.Centered.normBox_contains
      (Order.Field.inv_pos_direct patch.rootLower_positive).le
      (Norm.Reciprocal.normSq_le patch.rootLower_positive firstFloor)
  have lastInverse : (Joint.inverseBox patch).Contains core.targetSample.reading⁻¹ :=
    Geometry.Rational.Box.Square.Centered.normBox_contains
      (Order.Field.inv_pos_direct patch.rootLower_positive).le
      (Norm.Reciprocal.normSq_le patch.rootLower_positive lastFloor)
  have original := arithmetic.first_factor_le coordinate inside firstInverse lastInverse
  have ceiling : Arithmetic.firstCeiling (parameter + firstOffset) (lastOffset - firstOffset) coordinate
      patch.box (Joint.inverseBox patch) core.clearance.sourceFloor core.clearance.targetFloor
        core.clearance.sumFloor = Joint.firstCeiling patch 0 coordinate := by
    dsimp only [core]
    rewrite [betweenOfObservations_sourceFloor, betweenOfObservations_targetFloor, betweenOfObservations_sumFloor]
    exact Arithmetic.firstCeiling_parameters (parameter + firstOffset) (lastOffset - firstOffset)
      parameter 0 coordinate patch.box (Joint.inverseBox patch) patch.rootLower patch.rootLower (4 * patch.rootLower)
  exact original.trans_eq ceiling

/-- Genuinely new spatially paid value readings satisfy a local fourth-order remainder in the OFFSET DIFFERENCE.

The original Reobservations certificate and factor are unchanged. The
original-box ceiling is a proved bound on that SAME actual certificate,
not a desired remainder payment or an old reading assigned a new request.
-/
theorem between_value_remainder_le {spatial : AccuracyRequest}
    (observed : Arithmetic.Reobservations arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    Canonical.normSq ((observed.targetValue.get coordinate).requested.reading -
      (observed.sourceValue.get coordinate).requested.reading -
      (lastOffset - firstOffset) * (observed.sourceFirst.get coordinate).requested.reading) ≤
      Joint.valueCeiling patch 0 coordinate * Canonical.normSq (lastOffset - firstOffset) ^ 2 :=
  (observed.value_remainder_le coordinate).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((observed.valueCertificate_factor_eq coordinate).trans_le
        (between_value_factor_le first last unit accuracy paid firstObserved lastObserved arithmetic
          coordinate inside)) (Order.Arithmetic.sq_nonneg_direct _))

/-- The new first-row bank uses its actual independent source-second slope with the same local fourth-order scale. -/
theorem between_first_remainder_le {spatial : AccuracyRequest}
    (observed : Arithmetic.Reobservations arithmetic spatial) (coordinate : Fin 2)
    (inside : patch.box.Contains point) :
    Canonical.normSq ((observed.targetFirst.get coordinate).requested.reading -
      (observed.sourceFirst.get coordinate).requested.reading -
      (lastOffset - firstOffset) * (observed.sourceSecond.get coordinate).requested.reading) ≤
      Joint.firstCeiling patch 0 coordinate * Canonical.normSq (lastOffset - firstOffset) ^ 2 :=
  (observed.first_remainder_le coordinate).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      ((observed.firstCertificate_factor_eq coordinate).trans_le
        (between_first_factor_le first last unit accuracy paid firstObserved lastObserved arithmetic
          coordinate inside)) (Order.Arithmetic.sq_nonneg_direct _))

end Bounds

/-- Select the three SAME actual Readings, transporting only the target's exactly equal parameter index.

All root states, observations, requests, evaluator caches and displayed
witnesses remain original. The source-first reading remains shared between
the value slope and first base. No reading is observed or reobserved here.
-/
@[expose] def betweenNumerics (first : Step source firstOffset) (last : Step source lastOffset)
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1} {core : BetweenCore first last unit}
    {arithmetic : Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Arithmetic.Reobservations arithmetic spatial) (order coordinate : Fin 2) :=
  let numerics := paid.rowNumerics order coordinate
  (numerics.1, Specification.Table.castReadingParameter (betweenParameter_eq parameter firstOffset lastOffset)
    (Specification.Table.baseIndex order coordinate) numerics.2.1, numerics.2.2)

/-- The selected between-step base is the SAME original new source reading. -/
theorem betweenNumerics_base (first : Step source firstOffset) (last : Step source lastOffset)
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1} {core : BetweenCore first last unit}
    {arithmetic : Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Arithmetic.Reobservations arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).base = (betweenNumerics first last paid order coordinate).1.reading :=
  paid.rowCertificate_base order coordinate

/-- The selected output is the SAME independent target witness after exact parameter transport. -/
theorem betweenNumerics_output (first : Step source firstOffset) (last : Step source lastOffset)
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1} {core : BetweenCore first last unit}
    {arithmetic : Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Arithmetic.Reobservations arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).output =
      (betweenNumerics first last paid order coordinate).2.1.reading :=
  (paid.rowCertificate_output order coordinate).trans
    (Specification.Table.castReadingParameter_reading (betweenParameter_eq parameter firstOffset lastOffset)
      (Specification.Table.baseIndex order coordinate) (paid.rowNumerics order coordinate).2.1).symm

/-- The selected slope is the identical independent source derivative reading. -/
theorem betweenNumerics_slope (first : Step source firstOffset) (last : Step source lastOffset)
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1} {core : BetweenCore first last unit}
    {arithmetic : Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Arithmetic.Reobservations arithmetic spatial) (order coordinate : Fin 2) :
    (paid.rowCertificate order coordinate).slope = (betweenNumerics first last paid order coordinate).2.2.reading :=
  paid.rowCertificate_slope order coordinate

namespace BetweenRequest

/-- The complete original five-field result of the two-root local-difference request factory.

Both paid JointRequests, the exact scalar core, the complete arithmetic
factory and its independently paid Reobservations remain in their original
dependent-pair order. This exact type alias constructs no new cache.
-/
@[expose] def Result (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest) :=
  (firstRequest : CertifiedSquareRoot.Sampling.JointRequest first.root
    (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) spatial) ×
  (lastRequest : CertifiedSquareRoot.Sampling.JointRequest last.root
    (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) spatial) ×
  (core : { value : BetweenCore first last unit // value = betweenOfObservations first last unit
    (Sampling.incrementRequest (lastOffset - firstOffset) nonzero) rfl firstRequest.2.val lastRequest.2.val }) ×
  (arithmetic : { value : Arithmetic.Observations core.val // value = Arithmetic.request core.val }) ×
  Arithmetic.Reobservations arithmetic.val spatial

end BetweenRequest

/-- Request both independent residual/spread payments and the actual difference-offset arithmetic bank once.

Both original JointRequests, the exact original scalar core and the whole
arithmetic factory equality remain stored. The final original Reobservations
bank pays spatial.minimum(increment-fourth) on these SAME scalar roots.
No absolute Step, query, patch, target programme or previous reading executes
again, and no later-patch strip admission is assumed.
-/
def requestBetween (first : Step source firstOffset) (last : Step source lastOffset)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest) :
    BetweenRequest.Result first last unit nonzero spatial :=
  let accuracy := Sampling.incrementRequest (lastOffset - firstOffset) nonzero
  let firstRequest := CertifiedSquareRoot.Sampling.requestJoint first.root accuracy spatial
  let lastRequest := CertifiedSquareRoot.Sampling.requestJoint last.root accuracy spatial
  let core := betweenOfObservations first last unit accuracy rfl firstRequest.2.val lastRequest.2.val
  let arithmetic := Arithmetic.request core
  let paid := Arithmetic.Reobservations.build arithmetic spatial
  ⟨firstRequest, lastRequest, ⟨core, rfl⟩, ⟨arithmetic, rfl⟩, paid⟩

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end
