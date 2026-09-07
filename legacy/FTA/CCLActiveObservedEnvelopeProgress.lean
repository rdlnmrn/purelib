import FTA.CCLActiveObservedEnvelope
import FTA.CCLActiveCylinderProgress
import FTA.CCLFiniteTaggedEnvelope

/-!
# Total active progress to a shrinking tagged envelope

The active controller either reaches a phase-local canonical cylinder bound or
completes enough decoder blocks for the persistent observation bound.  Both
routes are total finite computations.  The winding box is refined independently
and contributes its own displayed rational error.
-/

namespace FTA
namespace CCLActiveObservedEnvelopeProgress

open CCL
open FTA.CCLActiveCylinderProgress
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLActiveObservedEnvelope
open FTA.CCLClearanceExclusion
open FTA.CCLCompletedBlockContraction
open FTA.CCLFiniteTaggedEnvelope
open FTA.CCLObservedChordalEnvelope
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The rational error displayed by either honest phase-local certificate. -/
def phaseCertificateErrorSq
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ} :
    ReachedMetricCertificate state epsilon → ℚ
  | .tagged envelope _ _ _ => envelope.radiusSq
  | .initialLow coupling _ _ _ => coupling.errorSq

theorem phaseCertificateErrorSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : State p ambient} {epsilon : ℚ}
    (certificate : ReachedMetricCertificate state epsilon) :
    phaseCertificateErrorSq certificate ≤
      2 * (state.core.numerical.box.diagonalSq + epsilon) := by
  cases certificate with
  | tagged envelope boxEq wordEq errorLe => exact errorLe
  | initialLow coupling boxEq wordEq errorLe => exact errorLe

/-- A total positive request either finds an exact rational root or returns
one of the two constructive shrinking-envelope certificates. -/
inductive TotalEnvelopeResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) (target : ℚ) where
  | zero (root : p.eval 0 = 0) : TotalEnvelopeResult current target
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      TotalEnvelopeResult current target
  | phaseCertified
      (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (certificate : ReachedMetricCertificate state target)
      (boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2)
      (coupledAccurate : phaseCertificateErrorSq certificate ≤
        2 * (target ^ 2 + target)) :
      TotalEnvelopeResult current target
  | observed
      (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (envelope : CoupledObservationEnvelope)
      (box_eq : envelope.box = state.core.numerical.box)
      (word_eq : envelope.tag.word = state.core.word)
      (boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2)
      (cylinderAccurate : envelope.cylinderRadiusSq ≤ target)
      (coupledAccurate : envelope.radiusSq ≤
        2 * (target ^ 2 + target)) :
      TotalEnvelopeResult current target

/-- One extra requested block makes the exhaustion branch visibly nonempty,
even when the geometric depth itself is zero. -/
def requestedObservationBlocks (target : ℚ) : ℕ :=
  observationBlockDepth target + 1

/-- Total controller-level shrinking-envelope request.  Phase-local radial
contraction may finish early; otherwise the exact completed-history growth
certificate supplies enough blocks for the observation schedule. -/
def request
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    TotalEnvelopeResult current target := by
  let accurate := machine.refine current target targetPositive
  let run := advanceBlocksOrCertificate machine accurate target targetPositive
    (requestedObservationBlocks target)
  match run with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete contains =>
      exact .terminal point root nonzero completeWord complete
        ((machine.refine_refines current target targetPositive).box.contains
          contains)
  | .certified state stateRefines certificate =>
      have refinesCurrent : StateRefines state current :=
        stateRefines.trans
          (machine.refine_refines current target targetPositive)
      have boxMonotone : state.core.numerical.box.diagonalSq ≤
          accurate.core.numerical.box.diagonalSq :=
        RatBox.diagonalSq_le_of_refines stateRefines.box
      have boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2 :=
        boxMonotone.trans
          (machine.refine_accurate current target targetPositive)
      have certificateBound := phaseCertificateErrorSq_le certificate
      exact .phaseCertified state refinesCurrent certificate boxAccurate (by
        linarith)
  | .blocksAdvanced final finalRefines historyGrowth =>
      have refinesCurrent : StateRefines final current :=
        finalRefines.trans
          (machine.refine_refines current target targetPositive)
      have blocksPositive : 0 < (parserBlocks final.core.word).length := by
        rw [parserBlocks_length]
        dsimp only [accurate, requestedObservationBlocks] at historyGrowth
        omega
      have enoughBlocks : observationBlockDepth target ≤
          (parserBlocks final.core.word).length := by
        rw [parserBlocks_length]
        dsimp only [accurate, requestedObservationBlocks] at historyGrowth
        omega
      cases blocksEq : parserBlocks final.core.word with
      | nil =>
          simp only [blocksEq, List.length_nil, lt_self_iff_false] at blocksPositive
      | cons first remaining =>
          let reached := CCLActiveObservedEnvelope.reachedEnvelope machine final
            target targetPositive first remaining blocksEq (by
              simpa only [blocksEq, List.length_cons] using enoughBlocks)
          exact .observed reached.state (reached.refines.trans refinesCurrent)
            reached.envelope reached.box_eq reached.word_eq reached.boxAccurate
              reached.cylinderAccurate reached.coupledAccurate

/-- Common-interface form of the total result.  The exact-root variants are
unchanged; every nonterminal branch now exposes one `FiniteTaggedEnvelope`. -/
inductive FiniteEnvelopeResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) (target : ℚ) where
  | zero (root : p.eval 0 = 0) : FiniteEnvelopeResult current target
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      FiniteEnvelopeResult current target
  | nonterminal
      (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (envelope : FiniteTaggedEnvelope)
      (box_eq : envelope.box = state.core.numerical.box)
      (word_eq : envelope.tag.word = state.core.word)
      (boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2)
      (errorAccurate : envelope.errorSq ≤ 2 * (target ^ 2 + target)) :
      FiniteEnvelopeResult current target

/-- Eliminate the phase-local/observed implementation distinction while
retaining each constructor's honest numerical center. -/
def requestFinite
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    FiniteEnvelopeResult current target :=
  match request machine current target targetPositive with
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete contains =>
      .terminal point root nonzero completeWord complete contains
  | .phaseCertified state refines certificate boxAccurate coupledAccurate =>
      match certificate with
      | .tagged envelope boxEq wordEq _errorLe =>
          .nonterminal state refines (FiniteTaggedEnvelope.ofCanonical envelope)
            boxEq wordEq boxAccurate coupledAccurate
      | .initialLow coupling boxEq wordEq _errorLe =>
          .nonterminal state refines (FiniteTaggedEnvelope.ofInitialLow coupling)
            boxEq wordEq boxAccurate coupledAccurate
  | .observed state refines envelope boxEq wordEq boxAccurate
      _cylinderAccurate coupledAccurate =>
      .nonterminal state refines (FiniteTaggedEnvelope.ofObserved envelope)
        boxEq wordEq boxAccurate coupledAccurate

end CCLActiveObservedEnvelopeProgress
end FTA
