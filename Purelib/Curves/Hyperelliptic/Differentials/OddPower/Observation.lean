module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Bounds
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original arithmetic observations of odd-power differentials

Each coefficient retains its original arithmetic process. A new starting
state places its reciprocal occurrences at a cached sheet observation;
arithmetic refinement may then choose different readings for those
occurrences. The existing rebase comparison relates the original and new
starts. Actual arithmetic readings are bounded against the displayed scalar
anchor using the cached sheet spread and original denominator clearance.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

/-- A cached finite Gaussian observation with its original squared-distance predicate. -/
abbrev RootObservation := Approximation.Observation Canonical
  (fun first last => Norm.Basic.normSq (first - last))

/-- Initialize the original differential process with every reciprocal occurrence at the retained sheet state. -/
@[expose] def initialState (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State) :
    (differential.value point sheet apart).name.process.State :=
  ((), Power.stateFrom (Arithmetic.reciprocalChannel sheet apart) ((), state) differential.denominatorExponent)

/-- The original differential's scalar coefficient on the unchanged retained sheet witness. -/
@[expose] def scalarReading (differential : OddPowerDifferential radicand) (point : Canonical)
    (observation : RootObservation) : Canonical :=
  (differential.scale * differential.numerator.eval point) * observation.witness⁻¹ ^ differential.denominatorExponent

/-- The computed coefficient sensitivity using the original denominator margin and independent finite factors. -/
@[expose] def sensitivity (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) : Fraction.Rational :=
  Norm.Basic.normSq (differential.scale * differential.numerator.eval point) *
    Norm.Power.differenceFactor apart.certificate.lowerSq⁻¹ differential.denominatorExponent *
      (apart.certificate.lowerSq⁻¹ * apart.certificate.lowerSq⁻¹)

/-- The computed arithmetic coefficient sensitivity is nonnegative. -/
theorem sensitivity_nonnegative (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    0 ≤ sensitivity differential point sheet apart := by
  have inverseNonnegative := (Fraction.Order.Field.inv_pos_direct apart.certificate.positive).le
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Norm.Power.differenceFactor_nonnegative inverseNonnegative _))
    (Order.Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative)

/-- The cached observed sheet witness is possible at its exact retained original process state. -/
private theorem root_possible (sheet : CoherentNamed) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state) :
    sheet.name.process.Possible state observation.witness := by
  have possible : observation.Possible observation.witness := observation.witness_possible
  -- Retain the witness expression while transporting only the possibility predicate.
  have predicate : observation.Possible observation.witness =
      (sheet.name.process.observation state).Possible observation.witness :=
    congrArg (fun retained : RootObservation => retained.Possible observation.witness) cache_eq
  have observedPossible : (sheet.name.process.observation state).Possible observation.witness :=
    Eq.mp predicate possible
  exact observedPossible

/-- Every original sheet candidate is nonzero by the retained whole-ball denominator margin. -/
private theorem root_nonzero (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    {state : sheet.name.process.State} {candidate : Canonical}
    (possible : sheet.name.process.Possible state candidate) : candidate ≠ 0 := by
  have lower := apart.certificate.lower state (sheet.name.process.possible_inside possible)
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt apart.certificate.positive) lower

/-- An actual reciprocal factor retains the original sheet margin as its squared-magnitude upper bound. -/
private theorem reciprocal_bound (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    {state : sheet.name.process.State} {candidate : Canonical}
    (possible : sheet.name.process.Possible state candidate) :
    Norm.Basic.normSq candidate⁻¹ ≤ apart.certificate.lowerSq⁻¹ := by
  have lower := apart.certificate.lower state (sheet.name.process.possible_inside possible)
  rewrite [Gaussian.Field.inv_eq, Gaussian.Field.normSq_inv _ (root_nonzero sheet apart possible)]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct apart.certificate.positive lower

/-- Every reciprocal factor possible at the initialized original process state meets the retained upper bound. -/
private theorem reciprocal_possible_bound (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (state : sheet.name.process.State) {candidate : Canonical}
    (possible : (Arithmetic.reciprocalChannel sheet apart).name.process.Possible ((), state) candidate) :
    Norm.Basic.normSq candidate ≤ apart.certificate.lowerSq⁻¹ := by
  rcases possible with ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  change numerator = 1 at numeratorPossible
  rewrite [numeratorPossible]
  change Norm.Basic.normSq ((1 : Canonical) * denominator⁻¹) ≤ apart.certificate.lowerSq⁻¹
  rewrite [Gaussian.Basic.one_mul]
  exact reciprocal_bound sheet apart denominatorPossible

/-- An independently refined reciprocal factor is close to the unchanged scalar witness at the paid spread. -/
private theorem reciprocal_possible_distance (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (state : sheet.name.process.State) (observation : RootObservation)
    (cache_eq : observation = sheet.name.process.observation state) {candidate : Canonical}
    (possible : (Arithmetic.reciprocalChannel sheet apart).name.process.Possible ((), state) candidate) :
    Norm.Basic.normSq (candidate - observation.witness⁻¹) ≤
      (apart.certificate.lowerSq⁻¹ * apart.certificate.lowerSq⁻¹) * observation.spread := by
  rcases possible with ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  change numerator = 1 at numeratorPossible
  rewrite [numeratorPossible]
  change Norm.Basic.normSq ((1 : Canonical) * denominator⁻¹ - observation.witness⁻¹) ≤ _
  rewrite [Gaussian.Basic.one_mul, Gaussian.Field.inv_eq, Gaussian.Field.inv_eq,
    Gaussian.Field.inverse_sub_inverse_direct (root_nonzero sheet apart denominatorPossible)
      (root_nonzero sheet apart (root_possible sheet state observation cache_eq)),
    Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  have denominatorObserved : observation.Possible denominator := by
    rewrite [cache_eq]
    exact denominatorPossible
  have distance := observation.pairwise observation.witness_possible denominatorObserved
  have denominatorBound := reciprocal_bound sheet apart denominatorPossible
  have anchorBound := reciprocal_bound sheet apart (root_possible sheet state observation cache_eq)
  rewrite [Gaussian.Field.inv_eq] at denominatorBound anchorBound
  calc
    _ ≤ (apart.certificate.lowerSq⁻¹ * observation.spread) * apart.certificate.lowerSq⁻¹ :=
      Order.Arithmetic.mul_le_mul_direct
        (Order.Arithmetic.mul_le_mul_direct denominatorBound distance (Norm.Basic.normSq_nonneg _)
          (Fraction.Order.Field.inv_pos_direct apart.certificate.positive).le)
        anchorBound (Norm.Basic.normSq_nonneg _)
        (Order.Arithmetic.mul_nonneg_direct
          (Fraction.Order.Field.inv_pos_direct apart.certificate.positive).le observation.spread_nonnegative)
    _ = _ := by ring1

/-- Actual initialized arithmetic coefficient candidates are close to the unchanged scalar witness.

Every reciprocal occurrence may choose its own possible sheet reading. The
original process margin and cached observation spread pay those independent
choices through the finite power sensitivity factor.
-/
theorem initial_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    {candidate : Canonical}
    (possible : (differential.value point sheet apart).name.process.Possible
      (initialState differential point sheet apart state) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) ≤
      sensitivity differential point sheet apart * observation.spread := by
  rcases possible with ⟨numerator, power, numeratorPossible, powerPossible, rfl⟩
  change numerator = differential.scale * differential.numerator.eval point at numeratorPossible
  rewrite [numeratorPossible]
  let reciprocal := Arithmetic.reciprocalChannel sheet apart
  let bound := apart.certificate.lowerSq⁻¹
  let distance := (apart.certificate.lowerSq⁻¹ * apart.certificate.lowerSq⁻¹) * observation.spread
  have boundNonnegative : 0 ≤ bound := (Fraction.Order.Field.inv_pos_direct apart.certificate.positive).le
  have distanceNonnegative : 0 ≤ distance := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct boundNonnegative boundNonnegative) observation.spread_nonnegative
  have powerClose := Power.possible_difference_le reciprocal ((), state) observation.witness⁻¹ bound distance
    boundNonnegative distanceNonnegative (reciprocal_bound sheet apart (root_possible sheet state observation cache_eq))
    (fun possible => reciprocal_possible_bound sheet apart state possible)
    (fun possible => reciprocal_possible_distance sheet apart state observation cache_eq possible)
    differential.denominatorExponent powerPossible
  have identity : (differential.scale * differential.numerator.eval point) * power -
      scalarReading differential point observation =
      (differential.scale * differential.numerator.eval point) *
        (power - observation.witness⁻¹ ^ differential.denominatorExponent) := by
    unfold scalarReading
    ring1
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerClose (Norm.Basic.normSq_nonneg _)).trans_eq
    (by unfold sensitivity distance bound; ring1)

/-- The original comparison request pays one eighth of the free arithmetic-observation budget. -/
@[expose] def comparisonRequest (accuracy : AccuracyRequest) : AccuracyRequest :=
  ⟨accuracy.tolerance / 8, Rat.Bounds.Quarter.eighth_pos accuracy.positive⟩

/-- The left arithmetic ball-radius request pays one sixteenth of the same free budget. -/
@[expose] def radiusRequest (accuracy : AccuracyRequest) : AccuracyRequest := by
  have denominatorPositive : (0 : Fraction.Rational) < 16 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide +kernel)
  exact ⟨accuracy.tolerance / 16,
    Fraction.Order.Field.div_pos_direct (numerator := accuracy.tolerance) (denominator := (16 : Fraction.Rational))
      accuracy.positive denominatorPositive⟩

/-- The computed canonical left-stage floor pays the actual original arithmetic ball spread before comparison. -/
@[expose] def minimumIndex (accuracy : AccuracyRequest) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 (radiusRequest accuracy).tolerance

/-- The finite observation bound adds the free arithmetic budget to the retained sheet-spread sensitivity payment. -/
@[expose] def errorBound (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (observation : RootObservation) (accuracy : AccuracyRequest) : Fraction.Rational :=
  accuracy.tolerance + 4 * sensitivity differential point sheet apart * observation.spread

/-- The original arithmetic process has the requested small ball radius at every stage after the retained floor. -/
theorem radius_lt (value : CoherentNamed) (accuracy : AccuracyRequest) {index : Nat}
    (floor : minimumIndex accuracy ≤ index) :
    (value.name.process.ball (Process.Sampling.stateAt value.name.process value.name.state index)).radiusSq <
      (radiusRequest accuracy).tolerance := by
  have selected := Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0
    (radiusRequest accuracy).tolerance (radiusRequest accuracy).positive
  exact ((Process.Sampling.stateAt_accurate value.name.process value.name.state index).trans_le
    (Geometric.Basic.quarterRadius_antitone (by decide +kernel) floor)).trans selected

/-- The actual spread and comparison subdivisions pay exactly their original free arithmetic budget. -/
theorem budget_identity (accuracy : AccuracyRequest) (payment : Fraction.Rational) :
    2 * (4 * (radiusRequest accuracy).tolerance +
      2 * ((comparisonRequest accuracy).tolerance + payment)) = accuracy.tolerance + 4 * payment := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := (16 : Fraction.Rational)) (by decide +kernel)
  change (2 * (4 * (accuracy.tolerance / 16) + 2 * (accuracy.tolerance / 8 + payment))) * 16 =
    (accuracy.tolerance + 4 * payment) * 16
  calc
    _ = 8 * ((accuracy.tolerance / 16) * 16) +
        8 * ((accuracy.tolerance / 8) * 8) + (4 * payment) * 16 := by ring1
    _ = _ := by
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (16 : Fraction.Rational) ≠ 0),
        Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel : (8 : Fraction.Rational) ≠ 0)]
      ring1

/-- An actual original-process arithmetic candidate pays the internally computed observation bound.

The original-start and paid-start witnesses are chosen independently by the
existing rebase comparison. The paid-start witness persists into the original
initialized coefficient state, whose independently possible factors are
bounded against the unchanged sheet witness. The original candidate pays its
own observed spread; no scalar anchor is substituted for an arithmetic witness.
-/
theorem candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest)
    (comparison : Comparison
      (Name.Sampling.approximation (differential.value point sheet apart).name)
      (Name.Sampling.approximation
        ({ process := (differential.value point sheet apart).name.process,
           state := initialState differential point sheet apart state } : Named))
      (minimumIndex accuracy) 0 (comparisonRequest accuracy).tolerance)
    {candidate : Canonical}
    (possible : (differential.value point sheet apart).name.process.Possible
      (Process.Sampling.stateAt (differential.value point sheet apart).name.process
        (differential.value point sheet apart).name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) <
      errorBound differential point sheet apart observation accuracy := by
  let value := differential.value point sheet apart
  let process := value.name.process
  let paidStart := initialState differential point sheet apart state
  let leftState := Process.Sampling.stateAt process value.name.state comparison.leftIndex
  let leftReading := Process.Sampling.witnessAt process value.name.state comparison.leftIndex
  let rightReading := Process.Sampling.witnessAt process paidStart comparison.rightIndex
  have leftPossible := Process.Sampling.witnessAt_possible process value.name.state comparison.leftIndex
  have rightPossible := Process.Sampling.witnessAt_possible process paidStart comparison.rightIndex
  have rightAtStart := Process.Sampling.stateAt_possible_at_start process paidStart comparison.rightIndex rightPossible
  have rightClose := initial_candidate_close differential point sheet apart state observation cache_eq rightAtStart
  have pairwise : Norm.Basic.normSq (candidate - leftReading) ≤ 4 * (process.ball leftState).radiusSq :=
    (process.observation leftState).pairwise possible leftPossible
  have radiusSmall := radius_lt value accuracy comparison.left_ge
  have pairwiseSmall : Norm.Basic.normSq (candidate - leftReading) < 4 * (radiusRequest accuracy).tolerance :=
    pairwise.trans_lt (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel) radiusSmall)
  have compared : Norm.Basic.normSq (leftReading - rightReading) < (comparisonRequest accuracy).tolerance :=
    comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  have leftClose : Norm.Basic.normSq (leftReading - scalarReading differential point observation) <
      2 * ((comparisonRequest accuracy).tolerance + sensitivity differential point sheet apart * observation.spread) :=
    calc
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          Norm.Basic.normSq (rightReading - scalarReading differential point observation)) :=
        Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          sensitivity differential point sheet apart * observation.spread) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) rightClose) (by decide +kernel)
      _ < _ := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_right_direct compared _)
  calc
    _ ≤ 2 * (Norm.Basic.normSq (candidate - leftReading) +
        Norm.Basic.normSq (leftReading - scalarReading differential point observation)) :=
      Norm.Bounds.normSq_sub_le_via _ _ _
    _ < 2 * (4 * (radiusRequest accuracy).tolerance +
        2 * ((comparisonRequest accuracy).tolerance +
          sensitivity differential point sheet apart * observation.spread)) :=
      Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_direct pairwiseSmall leftClose)
    _ = accuracy.tolerance + 4 * (sensitivity differential point sheet apart * observation.spread) :=
      budget_identity accuracy _
    _ = errorBound differential point sheet apart observation accuracy := by unfold errorBound; ring1

/-- The exact existing comparison type retains the supplied coefficient cache and its actual paid starting state. -/
abbrev PreparedComparison (coefficient : CoherentNamed) (paidStart : coefficient.name.process.State)
    (accuracy : AccuracyRequest) :=
  Comparison (Name.Sampling.approximation coefficient.name)
    (Name.Sampling.approximation ({ process := coefficient.name.process, state := paidStart } : Named))
    (minimumIndex accuracy) 0 (comparisonRequest accuracy).tolerance

/-- Transport the initialized state to the exact retained coefficient cache. -/
@[expose] def cachedInitialState (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (coefficient : CoherentNamed) (cache_eq : coefficient = differential.value point sheet apart) :
    coefficient.name.process.State :=
  Process.Sampling.castState
    (congrArg (fun retained : CoherentNamed => retained.name.process) cache_eq).symm
    (initialState differential point sheet apart state)

/-- Complete original evaluator and starting-state equalities transport the same paid arithmetic comparison.

The comparison, selected index and possible reading remain unchanged. Only
complete cache equalities identify the original evaluator construction and
its retained initialized state before the existing bound is consumed.
-/
theorem cached_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (coefficientCache : coefficient = differential.value point sheet apart)
    (paidStart : coefficient.name.process.State)
    (paidStartCache : paidStart = cachedInitialState differential point sheet apart state coefficient coefficientCache)
    (comparison : PreparedComparison coefficient paidStart accuracy) {candidate : Canonical}
    (possible : coefficient.name.process.Possible
      (Process.Sampling.stateAt coefficient.name.process coefficient.name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) <
      errorBound differential point sheet apart observation accuracy := by
  cases coefficientCache
  cases paidStartCache
  exact candidate_close differential point sheet apart state observation rootCache accuracy comparison possible

set_option genInjectivity false in
/-- An actual original arithmetic observation with both selected process states and the paid scalar comparison.

The retained coefficient is the original odd-power evaluator. Its two starts
share exactly that original process. Both selected states and observations
belong to the actual rebase comparison; the sheet observation's cached witness
is used only as the scalar anchor of the proved quantitative bound.
-/
structure Reading (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (accuracy : AccuracyRequest) where
  /-- The original sheet observation's complete cache equality. -/ rootCache_eq :
    rootObservation = sheet.name.process.observation state
  /-- The retained original arithmetic coefficient name and process. -/ coefficient : CoherentNamed
  /-- The cache is the original odd-power evaluator on the retained original sheet channel. -/ coefficient_eq :
    coefficient = differential.value point sheet apart
  /-- The cached second starting state of this exact original coefficient process. -/ paidStart :
    coefficient.name.process.State
  /-- The second starting state places each reciprocal occurrence at the original paid sheet state. -/ paidStart_eq :
    paidStart = cachedInitialState differential point sheet apart state coefficient coefficient_eq
  /-- The existing comparison retains both original-start and paid-start arithmetic samplers. -/ comparison : Comparison
    (Name.Sampling.approximation coefficient.name)
    (Name.Sampling.approximation ({ process := coefficient.name.process, state := paidStart } : Named))
    (minimumIndex accuracy) 0 (comparisonRequest accuracy).tolerance
  /-- The actual independently selected original-start state. -/ originalState : coefficient.name.process.State
  /-- The original state belongs to the comparison's selected left index. -/ originalState_eq : originalState =
    Process.Sampling.stateAt coefficient.name.process coefficient.name.state comparison.leftIndex
  /-- The actual independently selected paid-start state. -/ paidState : coefficient.name.process.State
  /-- The paid state belongs to the comparison's selected right index. -/ paidState_eq : paidState =
    Process.Sampling.stateAt coefficient.name.process paidStart comparison.rightIndex
  /-- The cached original-start arithmetic observation, with its actual witness and candidate predicate. -/ original :
    RootObservation
  /-- The original observation is exactly that of the retained original process state. -/ original_eq :
    original = coefficient.name.process.observation originalState
  /-- The cached paid-start observation retains its own actual arithmetic witness. -/ paid : RootObservation
  /-- The paid observation is exactly that of the independently selected original process state. -/ paid_eq :
    paid = coefficient.name.process.observation paidState
  /-- Every actual original observation candidate meets the internally computed scalar comparison bound. -/ close :
    ∀ {candidate : Canonical}, original.Possible candidate →
      Norm.Basic.normSq (candidate - scalarReading differential point rootObservation) <
        errorBound differential point sheet apart rootObservation accuracy

constructive_injectivity Reading

/-- Observe the exact retained arithmetic evaluator cache through its original two-start comparison.

The actual supplied evaluator is used once throughout state selection and
both retained observations. Complete cache equality transports the original
initialized state and scalar bound; it does not reconstruct the evaluator or
replace either selected witness.
-/
@[expose] def requestWithEvaluator (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (cache_eq : rootObservation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (coefficientCache : coefficient = differential.value point sheet apart) :
    Reading differential point sheet apart state rootObservation accuracy := by
  let paidStart := cachedInitialState differential point sheet apart state coefficient coefficientCache
  let comparison := (coefficient.rebaseEquivalent paidStart).compare (minimumIndex accuracy) 0
    (comparisonRequest accuracy).tolerance (comparisonRequest accuracy).positive
  let originalState := Process.Sampling.stateAt coefficient.name.process coefficient.name.state comparison.leftIndex
  let paidState := Process.Sampling.stateAt coefficient.name.process paidStart comparison.rightIndex
  let original := coefficient.name.process.observation originalState
  let paid := coefficient.name.process.observation paidState
  exact
    { rootCache_eq := cache_eq
      coefficient := coefficient
      coefficient_eq := coefficientCache
      paidStart := paidStart
      paidStart_eq := rfl
      comparison := comparison
      originalState := originalState
      originalState_eq := rfl
      paidState := paidState
      paidState_eq := rfl
      original := original
      original_eq := rfl
      paid := paid
      paid_eq := rfl
      close := cached_candidate_close differential point sheet apart state rootObservation cache_eq accuracy
        coefficient coefficientCache paidStart rfl comparison }

/-- The shared constructor retains the complete supplied evaluator cache as its original numerical owner. -/
theorem requestWithEvaluator_coefficient (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (cache_eq : rootObservation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (coefficientCache : coefficient = differential.value point sheet apart) :
    (requestWithEvaluator differential point sheet apart state rootObservation cache_eq accuracy
      coefficient coefficientCache).coefficient = coefficient := rfl

/-- Observe the original arithmetic evaluator with the shared retained-cache constructor.

The original evaluator is constructed once. The same original constructor
selects its two process states and retains their witnesses, comparison and
request payments without a second interpretation of state selection.
-/
@[expose] def request (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (cache_eq : rootObservation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) : Reading differential point sheet apart state rootObservation accuracy :=
  let coefficient := differential.value point sheet apart
  requestWithEvaluator differential point sheet apart state rootObservation cache_eq accuracy coefficient rfl

/-- The original request is the complete shared evaluator construction with the identical original evaluator.

The equality concerns the full retained reading, including both original
states, observations, request indices and comparison. The supplied-cache
operation runs the same comparison once rather than rebuilding another view.
-/
theorem request_eq_requestWithEvaluator (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (cache_eq : rootObservation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) :
    request differential point sheet apart state rootObservation cache_eq accuracy =
      requestWithEvaluator differential point sheet apart state rootObservation cache_eq accuracy
        (differential.value point sheet apart) rfl := rfl

namespace Reading

/-- Read the actual witness cached in the original-start arithmetic observation. -/
@[expose] def reading {differential : OddPowerDifferential radicand} {point : Canonical} {sheet : CoherentNamed}
    {apart : Named.Apart sheet.name} {state : sheet.name.process.State}
    {rootObservation : RootObservation} {accuracy : AccuracyRequest}
    (retained : Reading differential point sheet apart state rootObservation accuracy) : Canonical :=
  retained.original.witness

/-- The retained arithmetic witness is possible at the actual original coefficient-process state. -/
theorem reading_possible {differential : OddPowerDifferential radicand} {point : Canonical} {sheet : CoherentNamed}
    {apart : Named.Apart sheet.name} {state : sheet.name.process.State}
    {rootObservation : RootObservation} {accuracy : AccuracyRequest}
    (retained : Reading differential point sheet apart state rootObservation accuracy) :
    retained.coefficient.name.process.Possible retained.originalState retained.reading := by
  have possible : retained.original.Possible retained.reading := retained.original.witness_possible
  rewrite [retained.original_eq] at possible
  exact possible

/-- The actual original arithmetic witness meets the paid scalar comparison bound. -/
theorem reading_close {differential : OddPowerDifferential radicand} {point : Canonical} {sheet : CoherentNamed}
    {apart : Named.Apart sheet.name} {state : sheet.name.process.State}
    {rootObservation : RootObservation} {accuracy : AccuracyRequest}
    (retained : Reading differential point sheet apart state rootObservation accuracy) :
    Norm.Basic.normSq (retained.reading - scalarReading differential point rootObservation) <
      errorBound differential point sheet apart rootObservation accuracy :=
  retained.close retained.original.witness_possible

end Reading

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
