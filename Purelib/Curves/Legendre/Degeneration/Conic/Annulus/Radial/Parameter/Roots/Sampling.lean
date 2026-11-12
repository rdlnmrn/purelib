module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
import Purelib.Data.Gaussian.Norm.Separation.Product
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Sum
import Purelib.Approximation.Gaussian.Process.Coherence.Sampling
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Paid observations of the original fixed-point cubic roots

The original source comparison pays the discrepancy between its factored
input and the supplied preparation. Separate semantic stages pay the spread
of the identical original cofactor at the two actual paired factor states.
The exact normalized source and retained signed target window then give a
positive sum floor for every pair of full cubic readings. Both residual
observations and the original comparison state are cached without replacing
their root processes or preparing the source again.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {original : UnitVertex}
variable {unit : Owner ((unitPolynomial site).eval (sourcePoint site parameter original).base)}
variable {source : Lift (sourcePoint site parameter original) unit}
variable {anchor : Anchor source} {increment : Canonical}
variable {step : Step anchor increment} {sourcePrepared : Division.Prepared source.value}

/-- The original cofactor floor times the retained normalized signed-window radius square. -/
@[expose] def sumFloor (anchor : Anchor source) : Fraction.Rational :=
  source.unitRoot.apart.certificate.lowerSq * anchor.seed.separation.radius ^ 2

/-- The intrinsic full-product sum floor is strictly positive. -/
theorem sumFloor_positive (anchor : Anchor source) : 0 < sumFloor anchor :=
  Arithmetic.mul_pos_direct source.unitRoot.apart.certificate.positive
    (Arithmetic.pow_pos_direct anchor.seed.separation.positive 2)

/-- The paid allowance at either actual original cofactor state. -/
@[expose] def cofactorTolerance (source : Lift (sourcePoint site parameter original) unit) : Fraction.Rational :=
  source.unitRoot.apart.certificate.lowerSq / 80

/-- The cofactor allowance request has a strictly positive intrinsic tolerance. -/
theorem cofactorTolerance_positive (source : Lift (sourcePoint site parameter original) unit) :
    0 < cofactorTolerance source :=
  Fraction.Order.Field.div_pos_direct source.unitRoot.apart.certificate.positive
    (Fraction.Cast.Order.natCast_pos_direct (n := 80) (by decide +kernel))

/-- The original source product's allowance pays its actual cofactor factor with the exact source ordinate. -/
@[expose] def sourceTolerance (source : Lift (sourcePoint site parameter original) unit) : Fraction.Rational :=
  (4 * Norm.Basic.normSq (sourcePoint site parameter original).ordinate) * cofactorTolerance source

/-- The exact regular source ordinate makes the original product allowance tolerance positive. -/
theorem sourceTolerance_positive (anchor : Anchor source) : 0 < sourceTolerance source :=
  Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (by decide +kernel)
      (Norm.Basic.normSq_pos (parallel_ordinate_ne_zero site parameter original anchor.regular)))
    (cofactorTolerance_positive source)

/-- The actual normalized target centre bound pays its original cofactor factor's allowance. -/
@[expose] def targetTolerance (step : Step anchor increment) : Fraction.Rational :=
  (4 * step.root.value.name.process.centerBound) * cofactorTolerance source

/-- Original target apartness gives a positive computed full-product allowance request. -/
theorem targetTolerance_positive (step : Step anchor increment) : 0 < targetTolerance step :=
  Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (by decide +kernel)
      (CertifiedSquareRoot.Certificate.centerBound_positive step.root)) (cofactorTolerance_positive source)

/-- The finite original source-product sampling stage paying its cofactor allowance. -/
@[expose] def sourceMinimum (source : Lift (sourcePoint site parameter original) unit) : Nat :=
  CertifiedSquareRoot.Sampling.allowanceMinimum source.value (sourceTolerance source)

/-- The finite actual full-target-root stage paying its retained cofactor allowance. -/
@[expose] def targetMinimum (roots : Roots step sourcePrepared) : Nat :=
  CertifiedSquareRoot.Sampling.allowanceMinimum roots.targetRoot.value (targetTolerance step)

/-- The finite radius stage paying the source preparation's candidate spread. -/
@[expose] def spreadMinimum (anchor : Anchor source) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 (sumFloor anchor / 256)

/-- The discrepancy tolerance used by the existing original-to-prepared source comparison. -/
@[expose] def comparisonTolerance (anchor : Anchor source) : Fraction.Rational := sumFloor anchor / 64

/-- The original source-preparation comparison request is positive. -/
theorem comparisonTolerance_positive (anchor : Anchor source) : 0 < comparisonTolerance anchor :=
  Fraction.Order.Field.div_pos_direct (sumFloor_positive anchor)
    (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide +kernel))

set_option genInjectivity false in
/-- Two actual full-root residual observations and their retained original source-comparison cache.

The original source input state comes from the comparison with the exact
supplied preparation. The full source observation is chosen after that
comparison's right index; the target is chosen after its computed semantic
stage. Their actual process states, observations and comparison are retained.
-/
structure Pair (roots : Roots step sourcePrepared) (sourceAccuracy targetAccuracy : AccuracyRequest) where
  /-- The original input is compared with the identical cached full source certificate. -/
  comparison : Comparison (Name.Sampling.approximation source.value.name)
    (Name.Sampling.approximation roots.sourceRoot.value.name) (sourceMinimum source) (spreadMinimum anchor)
      (comparisonTolerance anchor)
  /-- The comparison is produced by the retained operational equivalence at the computed starts and tolerance. -/
  comparison_eq : comparison = roots.source_agrees.compare (sourceMinimum source) (spreadMinimum anchor)
    (comparisonTolerance anchor) (comparisonTolerance_positive anchor)
  /-- The cached original source state is the one selected by the retained comparison. -/
  originalState : source.value.name.process.State
  /-- The original state is read from the unchanged input process at the actual selected comparison index. -/
  originalState_eq : originalState = Process.Sampling.stateAt source.value.name.process source.value.name.state
    comparison.leftIndex
  /-- The actual observation of that same original input state. -/
  originalObservation : Approximation.Observation Canonical (fun first last => Norm.Basic.normSq (first - last))
  /-- The original observation retains its exact process state and possibility predicate. -/
  originalObservation_eq : originalObservation = source.value.name.process.observation originalState
  /-- The actual full source certificate observation paying the original residual request. -/
  source : CertifiedSquareRoot.Sampling.ResidualObservation roots.sourceRoot sourceAccuracy
  /-- Its retained state is selected after the existing comparison has paid source preparation agreement. -/
  source_stage : comparison.rightIndex ≤ source.comparison.leftIndex
  /-- The actual full target certificate observation paying the original residual request. -/
  target : CertifiedSquareRoot.Sampling.ResidualObservation roots.targetRoot targetAccuracy
  /-- Its retained state is selected after the computed target product allowance stage. -/
  target_stage : targetMinimum roots ≤ target.comparison.leftIndex

constructive_injectivity Pair

/-- Request the two original full-root observations using internally computed comparison and semantic stages. -/
def request (roots : Roots step sourcePrepared) (sourceAccuracy targetAccuracy : AccuracyRequest) :
    Pair roots sourceAccuracy targetAccuracy := by
  let comparison := roots.source_agrees.compare (sourceMinimum source) (spreadMinimum anchor)
    (comparisonTolerance anchor) (comparisonTolerance_positive anchor)
  let originalState := Process.Sampling.stateAt source.value.name.process source.value.name.state comparison.leftIndex
  let originalObservation := source.value.name.process.observation originalState
  let sourceObservation := CertifiedSquareRoot.Sampling.requestAfter roots.sourceRoot
    sourceAccuracy comparison.rightIndex
  let targetObservation := CertifiedSquareRoot.Sampling.requestAfter roots.targetRoot
    targetAccuracy (targetMinimum roots)
  exact
    { comparison := comparison
      comparison_eq := rfl
      originalState := originalState
      originalState_eq := rfl
      originalObservation := originalObservation
      originalObservation_eq := rfl
      source := sourceObservation.val
      source_stage := sourceObservation.property
      target := targetObservation.val
      target_stage := targetObservation.property }

namespace Pair

variable {roots : Roots step sourcePrepared} {sourceAccuracy targetAccuracy : AccuracyRequest}

/-- Read the actual retained witness of the original product-side comparison state. -/
@[expose] def originalReading (pair : Pair roots sourceAccuracy targetAccuracy) : Canonical :=
  pair.originalObservation.witness

/-- The original reading is possible at the unchanged original source process state. -/
theorem original_reading_possible (pair : Pair roots sourceAccuracy targetAccuracy) :
    source.value.name.process.Possible pair.originalState pair.originalReading := by
  have possible : pair.originalObservation.Possible pair.originalReading := pair.originalObservation.witness_possible
  rewrite [pair.originalObservation_eq] at possible
  exact possible

/-- The cached original witness reads the identical sample chosen by the retained comparison. -/
theorem original_reading_eq (pair : Pair roots sourceAccuracy targetAccuracy) :
    pair.originalReading = Process.Sampling.witnessAt source.value.name.process source.value.name.state
      pair.comparison.leftIndex := by
  unfold originalReading
  rewrite [pair.originalObservation_eq, pair.originalState_eq]
  rfl

/-- The actual full source observation spread is below the original comparison tolerance. -/
theorem source_spread_lt (pair : Pair roots sourceAccuracy targetAccuracy) :
    pair.source.observation.spread < comparisonTolerance anchor := by
  have after : spreadMinimum anchor ≤ pair.source.comparison.leftIndex :=
    pair.comparison.right_ge.trans pair.source_stage
  have radiusPositive : 0 < sumFloor anchor / 256 :=
    Fraction.Order.Field.div_pos_direct (sumFloor_positive anchor)
      (Fraction.Cast.Order.natCast_pos_direct (n := 256) (by decide +kernel))
  have minimum := Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0
    (sumFloor anchor / 256) radiusPositive
  have radius := (Process.Sampling.stateAt_accurate roots.sourceRoot.value.name.process
    roots.sourceRoot.value.name.state pair.source.comparison.leftIndex).trans_le
      (Geometric.Basic.quarterRadius_antitone (by decide +kernel : (0 : Fraction.Rational) ≤ 1) after)
      |>.trans minimum
  rewrite [pair.source.observation_eq, pair.source.state_eq]
  change 4 * _ < comparisonTolerance anchor
  have paid : 4 * (sumFloor anchor / 256) = comparisonTolerance anchor := by
    apply Fraction.Field.mul_right_cancel_of_ne (c := (256 : Fraction.Rational)) (by decide +kernel)
    change (4 * (sumFloor anchor / 256)) * 256 = (sumFloor anchor / 64) * 256
    calc
      _ = 4 * ((sumFloor anchor / 256) * 256) := by ring1
      _ = 4 * sumFloor anchor := by
        rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (256 : Fraction.Rational) ≠ 0)]
        rfl
      _ = ((sumFloor anchor / 64) * 64) * 4 := by
        rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (64 : Fraction.Rational) ≠ 0)]
        ring1
      _ = _ := by ring1
  exact (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel) radius).trans_eq paid

/-- The retained original source sample and actual full prepared source witness pay their comparison tolerance. -/
theorem source_reading_close (pair : Pair roots sourceAccuracy targetAccuracy) :
    Norm.Basic.normSq (pair.originalReading - pair.source.reading) < comparisonTolerance anchor := by
  have close := pair.comparison.close (Nat.le_refl pair.comparison.leftIndex) pair.source_stage
  rewrite [pair.original_reading_eq]
  have reading : pair.source.reading = Process.Sampling.witnessAt roots.sourceRoot.value.name.process
      roots.sourceRoot.value.name.state pair.source.comparison.leftIndex := by
    change pair.source.observation.witness = _
    rewrite [pair.source.observation_eq, pair.source.state_eq]
    rfl
  rewrite [reading]
  exact close

/-- Every possible prepared source reading remains within the paid full-product discrepancy budget. -/
theorem source_candidate_close (pair : Pair roots sourceAccuracy targetAccuracy) {candidate : Canonical}
    (possible : pair.source.observation.Possible candidate) :
    Norm.Basic.normSq (candidate - pair.originalReading) ≤ sumFloor anchor / 16 := by
  have cache : pair.source.observation = roots.sourceRoot.value.name.process.observation
      (Process.Sampling.stateAt roots.sourceRoot.value.name.process roots.sourceRoot.value.name.state
        pair.source.comparison.leftIndex) := by
    rewrite [pair.source.observation_eq, pair.source.state_eq]
    rfl
  have distance := pair.comparison.candidate_right_distance_le (Nat.le_refl pair.comparison.leftIndex)
    pair.source_stage pair.source.observation cache possible
  change Norm.Basic.normSq (candidate - Process.Sampling.witnessAt source.value.name.process source.value.name.state
    pair.comparison.leftIndex) ≤ 2 * (pair.source.observation.spread + comparisonTolerance anchor) at distance
  rewrite [← pair.original_reading_eq] at distance
  calc
    _ ≤ 2 * (pair.source.observation.spread + comparisonTolerance anchor) := distance
    _ ≤ 2 * (comparisonTolerance anchor + comparisonTolerance anchor) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct pair.source_spread_lt.le
          (Fraction.Order.Basic.le_refl _)) (by decide +kernel)
    _ = sumFloor anchor / 16 := by
      apply Fraction.Field.mul_right_cancel_of_ne (c := (64 : Fraction.Rational)) (by decide +kernel)
      change (2 * (sumFloor anchor / 64 + sumFloor anchor / 64)) * 64 = (sumFloor anchor / 16) * 64
      calc
        _ = 4 * ((sumFloor anchor / 64) * 64) := by ring1
        _ = 4 * sumFloor anchor := by
          rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (64 : Fraction.Rational) ≠ 0)]
          rfl
        _ = ((sumFloor anchor / 16) * 16) * 4 := by
          rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (16 : Fraction.Rational) ≠ 0)]
          ring1
        _ = _ := by ring1

/-- The original source product-side state pays the cofactor allowance without inspecting the supplied preparation. -/
theorem source_cofactor_allowance_lt (pair : Pair roots sourceAccuracy targetAccuracy) :
    source.unitRoot.value.coherent.allowance (Roots.sourceProductState pair.originalState).1 <
      cofactorTolerance source := by
  have allowance := CertifiedSquareRoot.Sampling.allowance_lt_after source.value (sourceTolerance source)
    (sourceTolerance_positive anchor) pair.comparison.left_ge
  rewrite [← pair.originalState_eq] at allowance
  have lower := Roots.source_cofactor_allowance_le pair.originalState
  have paid := lower.trans_lt allowance
  let factor := 4 * Norm.Basic.normSq (sourcePoint site parameter original).ordinate
  let originalAllowance := source.unitRoot.value.coherent.allowance (Roots.sourceProductState pair.originalState).1
  have positive : 0 < factor :=
    Arithmetic.mul_pos_direct (by decide +kernel)
      (Norm.Basic.normSq_pos (parallel_ordinate_ne_zero site parameter original anchor.regular))
  change factor * originalAllowance < factor * cofactorTolerance source at paid
  have commuted := (Fraction.Field.mul_comm originalAllowance factor).trans_lt
    (paid.trans_eq (Fraction.Field.mul_comm factor (cofactorTolerance source)))
  exact Arithmetic.lt_of_mul_lt_mul_right_direct
    (a := originalAllowance) (b := cofactorTolerance source) (c := factor) commuted positive

/-- The actual full target observation state pays the allowance of its retained original cofactor state. -/
theorem target_cofactor_allowance_lt (pair : Pair roots sourceAccuracy targetAccuracy) :
    source.unitRoot.value.coherent.allowance (roots.targetProductState pair.target.state).1 <
      cofactorTolerance source := by
  have allowance := CertifiedSquareRoot.Sampling.allowance_lt_after roots.targetRoot.value (targetTolerance step)
    (targetTolerance_positive step) pair.target_stage
  rewrite [← pair.target.state_eq] at allowance
  have paid := (roots.target_cofactor_allowance_le pair.target.state).trans_lt allowance
  let factor := 4 * step.root.value.name.process.centerBound
  let originalAllowance := source.unitRoot.value.coherent.allowance (roots.targetProductState pair.target.state).1
  have positive : 0 < factor :=
    Arithmetic.mul_pos_direct (by decide +kernel)
      (CertifiedSquareRoot.Certificate.centerBound_positive step.root)
  change factor * originalAllowance < factor * cofactorTolerance source at paid
  have commuted := (Fraction.Field.mul_comm originalAllowance factor).trans_lt
    (paid.trans_eq (Fraction.Field.mul_comm factor (cofactorTolerance source)))
  exact Arithmetic.lt_of_mul_lt_mul_right_direct
    (a := originalAllowance) (b := cofactorTolerance source) (c := factor) commuted positive

/-- Actual original cofactor candidates from the cached source and target factor states satisfy the paid spread. -/
theorem cofactor_close (pair : Pair roots sourceAccuracy targetAccuracy) {first last : Canonical}
    (firstPossible : source.unitRoot.value.name.process.Possible
      (Roots.sourceProductState pair.originalState).1 first)
    (lastPossible : source.unitRoot.value.name.process.Possible (roots.targetProductState pair.target.state).1 last) :
    Norm.Basic.normSq (first - last) ≤ source.unitRoot.apart.certificate.lowerSq / 10 := by
  calc
    _ ≤ 4 * (source.unitRoot.value.coherent.allowance (Roots.sourceProductState pair.originalState).1 +
        source.unitRoot.value.coherent.allowance (roots.targetProductState pair.target.state).1) :=
      source.unitRoot.value.coherent.possible_close firstPossible lastPossible
    _ ≤ 4 * (cofactorTolerance source + cofactorTolerance source) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct pair.source_cofactor_allowance_lt.le
          pair.target_cofactor_allowance_lt.le) (by decide +kernel)
    _ = source.unitRoot.apart.certificate.lowerSq / 10 := by
      let floor := source.unitRoot.apart.certificate.lowerSq
      apply Fraction.Field.mul_right_cancel_of_ne (c := (80 : Fraction.Rational)) (by decide +kernel)
      change (4 * (floor / 80 + floor / 80)) * 80 = (floor / 10) * 80
      calc
        _ = 8 * ((floor / 80) * 80) := by ring1
        _ = 8 * floor := by
          rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (80 : Fraction.Rational) ≠ 0)]
          rfl
        _ = ((floor / 10) * 10) * 8 := by
          rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (10 : Fraction.Rational) ≠ 0)]
          ring1
        _ = _ := by ring1

/-- Every target full-root reading has a separated sum with the actual original source product witness. -/
theorem original_sum_normSq_lower (pair : Pair roots sourceAccuracy targetAccuracy) {target : Canonical}
    (possible : pair.target.observation.Possible target) :
    sumFloor anchor ≤ Norm.Basic.normSq (pair.originalReading + target) := by
  have targetPossible := possible
  rewrite [pair.target.observation_eq] at targetPossible
  rcases Roots.source_candidate_factors pair.original_reading_possible with
    ⟨first, firstPossible, firstEq⟩
  rcases roots.target_candidate_factors targetPossible with ⟨last, ordinate, lastPossible, ordinatePossible, lastEq⟩
  rewrite [firstEq, lastEq]
  exact Norm.Bounds.cofactor_sum_lower first last (sourcePoint site parameter original).ordinate ordinate
    source.unitRoot.apart.certificate.positive.le
    (Arithmetic.pow_nonneg_direct anchor.seed.separation.positive.le 2)
    (source.unitRoot.apart.certificate.lower _ (source.unitRoot.value.name.process.possible_inside firstPossible))
    (anchor.seed.separation.center_sum_normSq_lower (step.target_candidate_inside ordinatePossible))
    (step.candidate_normSq_upper ordinatePossible) (pair.cofactor_close firstPossible lastPossible)

/-- All admitted full source and target readings share a positive original-owner signed sum floor.

The internally paid comparison transfers the original product witness to
every reading of the exact supplied preparation. Original cofactor coherence
and the retained normalized seed window pay the product sum before that
transfer. No final signed comparison or success premise is supplied by callers.
-/
theorem sum_normSq_lower (pair : Pair roots sourceAccuracy targetAccuracy) {first last : Canonical}
    (firstPossible : pair.source.observation.Possible first) (lastPossible : pair.target.observation.Possible last) :
    sumFloor anchor / 4 ≤ Norm.Basic.normSq (first + last) :=
  Norm.Bounds.prepared_sum_lower pair.originalReading first last (sumFloor_positive anchor).le
    (pair.original_sum_normSq_lower lastPossible) (pair.source_candidate_close firstPossible)

/-- The two actual full-root witnesses retain the same internally paid signed sum floor. -/
theorem reading_sum_normSq_lower (pair : Pair roots sourceAccuracy targetAccuracy) :
    sumFloor anchor / 4 ≤ Norm.Basic.normSq (pair.source.reading + pair.target.reading) :=
  pair.sum_normSq_lower pair.source.observation.witness_possible pair.target.observation.witness_possible

/-- The actual prepared-observation sum floor is strictly positive at the retained regular source. -/
theorem sumFloor_positive (_pair : Pair roots sourceAccuracy targetAccuracy) : 0 < sumFloor anchor / 4 :=
  Fraction.Order.Field.div_pos_direct (Sampling.sumFloor_positive anchor) (by decide +kernel)

end Pair

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Roots.Sampling
