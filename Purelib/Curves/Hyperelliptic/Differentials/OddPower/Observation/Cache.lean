module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Data.Gaussian.Norm.Reciprocal
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Bounds
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Cached original coefficient observations with actual observation floors

The existing odd-power arithmetic process and its original apartness data
remain unchanged. A supplied floor bounds every candidate in the actual
retained sheet observation. That floor pays reciprocal and independent-power
sensitivity, even when the original global apartness certificate is more
conservative. Existing rebase comparisons select both arithmetic states.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

/-- The original finite power sensitivity uses the positive floor of the actual retained observation candidates. -/
@[expose] def sensitivity (differential : OddPowerDifferential radicand) (point : Canonical)
    (floor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq (differential.scale * differential.numerator.eval point) *
    Norm.Power.differenceFactor floor⁻¹ differential.denominatorExponent * (floor⁻¹ * floor⁻¹)

/-- The actual-floor sensitivity is nonnegative under its original positive floor. -/
theorem sensitivity_nonnegative (differential : OddPowerDifferential radicand) (point : Canonical)
    {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ sensitivity differential point floor := by
  have inverseNonnegative := (Fraction.Order.Field.inv_pos_direct positive).le
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Norm.Power.differenceFactor_nonnegative inverseNonnegative _))
    (Order.Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative)

/-- The arithmetic free request and actual observation spread pay the retained fixed-floor comparison error. -/
@[expose] def errorBound (differential : OddPowerDifferential radicand) (point : Canonical) (floor : Fraction.Rational)
    (observation : RootObservation) (accuracy : AccuracyRequest) : Fraction.Rational :=
  accuracy.tolerance + 4 * sensitivity differential point floor * observation.spread

/-- The actual-floor arithmetic allowance uses the original sample's paid radius denominator. -/
@[expose] def allowanceFactor {parameter : Canonical} (differential : OddPowerDifferential radicand) (point : Canonical)
    (source : CertifiedSquareRoot.Certificate parameter) (floor : Fraction.Rational) : Fraction.Rational :=
  1 + 16 * sensitivity differential point floor /
    CertifiedSquareRoot.Sampling.radiusDenominator source

/-- The original arithmetic allowance is nonnegative under its actual positive observation floor. -/
theorem allowanceFactor_nonnegative {parameter : Canonical}
    (differential : OddPowerDifferential radicand) (point : Canonical)
    (source : CertifiedSquareRoot.Certificate parameter) {floor : Fraction.Rational} (positive : 0 < floor) :
    0 ≤ allowanceFactor differential point source floor := by
  unfold allowanceFactor
  exact Order.Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    (Fraction.Order.Field.div_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
        (sensitivity_nonnegative differential point positive))
      (CertifiedSquareRoot.Sampling.radiusDenominator_pos source).le)

/-- The actual root spread internally pays the original cache observation's computed arithmetic allowance. -/
theorem errorBound_le_factor {parameter : Canonical} {accuracy : AccuracyRequest}
    (differential : OddPowerDifferential radicand) (point : Canonical)
    (source : CertifiedSquareRoot.Certificate parameter)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy) {floor : Fraction.Rational}
    (positive : 0 < floor) :
    errorBound differential point floor sample.observation accuracy ≤
      allowanceFactor differential point source floor * accuracy.tolerance := by
  let sensitivity := sensitivity differential point floor
  have nonnegative := Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
    (sensitivity_nonnegative differential point positive)
  calc
    _ = accuracy.tolerance + (4 * sensitivity) * sample.observation.spread := rfl
    _ ≤ accuracy.tolerance + (4 * sensitivity) *
        (4 * (accuracy.tolerance / CertifiedSquareRoot.Sampling.radiusDenominator source)) :=
      Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sample.spread_le nonnegative)
    _ = _ := by
      unfold allowanceFactor
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- The unchanged cached sheet observation transports each actual process candidate to its original predicate. -/
private theorem possible_observed (sheet : CoherentNamed) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    {candidate : Canonical} (possible : sheet.name.process.Possible state candidate) :
    observation.Possible candidate := by
  rewrite [cache_eq]
  exact possible

/-- A possible initialized reciprocal factor pays its distance from the same unchanged observed sheet witness. -/
private theorem reciprocal_distance (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (state : sheet.name.process.State) (observation : RootObservation)
    (cache_eq : observation = sheet.name.process.observation state) {floor : Fraction.Rational}
    (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    {candidate : Canonical}
    (possible : (Arithmetic.reciprocalChannel sheet apart).name.process.Possible ((), state) candidate) :
    Norm.Basic.normSq candidate ≤ floor⁻¹ ∧
      Norm.Basic.normSq (candidate - observation.witness⁻¹) ≤ (floor⁻¹ * floor⁻¹) * observation.spread := by
  rcases possible with ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  change numerator = 1 at numeratorPossible
  rewrite [numeratorPossible]
  change Norm.Basic.normSq ((1 : Canonical) * denominator⁻¹) ≤ floor⁻¹ ∧ _
  rewrite [Gaussian.Basic.one_mul]
  have denominatorObserved := possible_observed sheet state observation cache_eq denominatorPossible
  have denominatorLower := lower denominatorObserved
  have anchorLower := lower observation.witness_possible
  constructor
  · exact Norm.Reciprocal.normSq_le positive denominatorLower
  · rewrite [Algebra.Field.ExplicitField.div_eq_mul_inv, Gaussian.Basic.one_mul]
    exact (Norm.Reciprocal.difference_normSq_le positive denominatorLower anchorLower).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (observation.pairwise denominatorObserved observation.witness_possible)
        (Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le
          (Fraction.Order.Field.inv_pos_direct positive).le))

/-- Every independently chosen initialized arithmetic factor pays the actual retained observation's floor and spread. -/
theorem initial_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    {candidate : Canonical}
    (possible : (differential.value point sheet apart).name.process.Possible
      (initialState differential point sheet apart state) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) ≤
      sensitivity differential point floor * observation.spread := by
  rcases possible with ⟨numerator, power, numeratorPossible, powerPossible, rfl⟩
  change numerator = differential.scale * differential.numerator.eval point at numeratorPossible
  rewrite [numeratorPossible]
  let reciprocal := Arithmetic.reciprocalChannel sheet apart
  let bound := floor⁻¹
  let distance := (floor⁻¹ * floor⁻¹) * observation.spread
  have boundNonnegative := (Fraction.Order.Field.inv_pos_direct positive).le
  have distanceNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct boundNonnegative boundNonnegative) observation.spread_nonnegative
  have powerClose := Power.possible_difference_le reciprocal ((), state) observation.witness⁻¹ bound distance
    boundNonnegative distanceNonnegative (Norm.Reciprocal.normSq_le positive (lower observation.witness_possible))
    (fun possible => (reciprocal_distance sheet apart state observation cache_eq positive lower possible).1)
    (fun possible => (reciprocal_distance sheet apart state observation cache_eq positive lower possible).2)
    differential.denominatorExponent powerPossible
  have identity : (differential.scale * differential.numerator.eval point) * power -
      scalarReading differential point observation = (differential.scale * differential.numerator.eval point) *
        (power - observation.witness⁻¹ ^ differential.denominatorExponent) := by unfold scalarReading; ring1
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerClose (Norm.Basic.normSq_nonneg _)).trans_eq
    (by unfold sensitivity distance bound; ring1)

/-- The actual rebase comparison bounds every original arithmetic candidate using the paid observation floor. -/
theorem candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    (accuracy : AccuracyRequest)
    (comparison : PreparedComparison (differential.value point sheet apart)
      (initialState differential point sheet apart state) accuracy)
    {candidate : Canonical}
    (possible : (differential.value point sheet apart).name.process.Possible
      (Process.Sampling.stateAt (differential.value point sheet apart).name.process
        (differential.value point sheet apart).name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) <
      errorBound differential point floor observation accuracy := by
  let value := differential.value point sheet apart
  let process := value.name.process
  let paidStart := initialState differential point sheet apart state
  let leftState := Process.Sampling.stateAt process value.name.state comparison.leftIndex
  let leftReading := Process.Sampling.witnessAt process value.name.state comparison.leftIndex
  let rightReading := Process.Sampling.witnessAt process paidStart comparison.rightIndex
  have leftPossible := Process.Sampling.witnessAt_possible process value.name.state comparison.leftIndex
  have rightPossible := Process.Sampling.witnessAt_possible process paidStart comparison.rightIndex
  have rightAtStart := Process.Sampling.stateAt_possible_at_start process paidStart comparison.rightIndex rightPossible
  have rightClose := initial_candidate_close differential point sheet apart state observation cache_eq positive lower
    rightAtStart
  have pairwise := (process.observation leftState).pairwise possible leftPossible
  have pairwiseSmall : Norm.Basic.normSq (candidate - leftReading) < 4 * (radiusRequest accuracy).tolerance :=
    pairwise.trans_lt (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
      (radius_lt value accuracy comparison.left_ge))
  have compared : Norm.Basic.normSq (leftReading - rightReading) < (comparisonRequest accuracy).tolerance :=
    comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  have leftClose : Norm.Basic.normSq (leftReading - scalarReading differential point observation) <
      2 * ((comparisonRequest accuracy).tolerance + sensitivity differential point floor * observation.spread) :=
    calc
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          Norm.Basic.normSq (rightReading - scalarReading differential point observation)) :=
        Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          sensitivity differential point floor * observation.spread) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) rightClose) (by decide +kernel)
      _ < _ := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_right_direct compared _)
  calc
    _ ≤ 2 * (Norm.Basic.normSq (candidate - leftReading) +
        Norm.Basic.normSq (leftReading - scalarReading differential point observation)) :=
      Norm.Bounds.normSq_sub_le_via _ _ _
    _ < 2 * (4 * (radiusRequest accuracy).tolerance +
        2 * ((comparisonRequest accuracy).tolerance + sensitivity differential point floor * observation.spread)) :=
      Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_direct pairwiseSmall leftClose)
    _ = accuracy.tolerance + 4 * (sensitivity differential point floor * observation.spread) :=
      budget_identity accuracy _
    _ = _ := by unfold errorBound; ring1

/-- Complete original cache equalities transport the stronger actual-observation-floor comparison. -/
private theorem cached_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (coefficientCache : coefficient = differential.value point sheet apart)
    (paidStart : coefficient.name.process.State)
    (paidStartCache : paidStart = cachedInitialState differential point sheet apart state coefficient coefficientCache)
    (comparison : PreparedComparison coefficient paidStart accuracy) {candidate : Canonical}
    (possible : coefficient.name.process.Possible
      (Process.Sampling.stateAt coefficient.name.process coefficient.name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) <
      errorBound differential point floor observation accuracy := by
  cases coefficientCache
  cases paidStartCache
  exact candidate_close differential point sheet apart state observation rootCache positive lower accuracy comparison
    possible

/-- The stronger floor bound consumes the same saved original reading and its exact selected comparison states. -/
private theorem retained_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    (accuracy : AccuracyRequest)
    (retained : Observation.Reading differential point sheet apart state observation accuracy)
    {candidate : Canonical} (possible : retained.original.Possible candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point observation) <
      errorBound differential point floor observation accuracy := by
  have processPossible : retained.coefficient.name.process.Possible retained.originalState candidate := by
    rewrite [retained.original_eq] at possible
    exact possible
  rewrite [retained.originalState_eq] at processPossible
  exact cached_candidate_close differential point sheet apart state observation rootCache positive lower accuracy
    retained.coefficient retained.coefficient_eq retained.paidStart retained.paidStart_eq retained.comparison
    processPossible

set_option genInjectivity false in
/-- The existing original arithmetic observation with its retained caller cache and stronger paid observation floor.

The original apartness, process, comparison and both selected arithmetic
states remain in the original nominal parent. The additional quantitative
certificate concerns every candidate of the actual selected observation.
-/
structure Reading (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (floor : Fraction.Rational) where
  /-- The original arithmetic observation owns its actual two states and comparison. -/
  original : Observation.Reading differential point sheet apart state rootObservation accuracy
  /-- The original observation uses the identical caller-retained complete coefficient cache. -/
  coefficient_eq : original.coefficient = coefficient
  /-- The actual observed-sheet candidate floor is strictly positive. -/
  positive : 0 < floor
  /-- The floor belongs to every actual candidate of the same retained root observation. -/
  lower : ∀ {candidate : Canonical}, rootObservation.Possible candidate → floor ≤ Norm.Basic.normSq candidate
  /-- Every original arithmetic candidate pays the actual observed-sheet floor and spread. -/
  close : ∀ {candidate : Canonical}, original.original.Possible candidate →
    Norm.Basic.normSq (candidate - scalarReading differential point rootObservation) <
      errorBound differential point floor rootObservation accuracy

constructive_injectivity Reading

/-- Request both arithmetic states on the unchanged supplied evaluator cache and certify its actual observation floor.

The original process executes the existing rebase comparison once. Both
selected states and observations retain that caller cache; opaque comparison
proofs transport only complete construction equalities. The supplied floor
concerns original root candidates and is never a final arithmetic bound.
-/
def request (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (rootObservation : RootObservation) (rootCache : rootObservation = sheet.name.process.observation state)
    (accuracy : AccuracyRequest) (coefficient : CoherentNamed)
    (coefficientCache : coefficient = differential.value point sheet apart)
    (floor : Fraction.Rational) (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, rootObservation.Possible candidate → floor ≤ Norm.Basic.normSq candidate) :
    Reading differential point sheet apart state rootObservation accuracy coefficient floor := by
  let retained := Observation.requestWithEvaluator differential point sheet apart state rootObservation rootCache
    accuracy coefficient coefficientCache
  exact
    { original := retained
      coefficient_eq := Observation.requestWithEvaluator_coefficient differential point sheet apart state
        rootObservation rootCache accuracy coefficient coefficientCache
      positive := positive
      lower := lower
      close := retained_candidate_close differential point sheet apart state rootObservation rootCache
        positive lower accuracy retained }

namespace Reading

/-- The stronger certificate uses the actual unchanged witness of its original arithmetic observation. -/
@[expose] def reading {differential : OddPowerDifferential radicand} {point : Canonical} {sheet : CoherentNamed}
    {apart : Named.Apart sheet.name} {state : sheet.name.process.State} {rootObservation : RootObservation}
    {accuracy : AccuracyRequest} {coefficient : CoherentNamed} {floor : Fraction.Rational}
    (retained : Reading differential point sheet apart state rootObservation accuracy coefficient floor) : Canonical :=
  retained.original.reading

/-- The same actual original arithmetic witness pays the stronger observed-floor comparison bound. -/
theorem reading_close {differential : OddPowerDifferential radicand} {point : Canonical} {sheet : CoherentNamed}
    {apart : Named.Apart sheet.name} {state : sheet.name.process.State} {rootObservation : RootObservation}
    {accuracy : AccuracyRequest} {coefficient : CoherentNamed} {floor : Fraction.Rational}
    (retained : Reading differential point sheet apart state rootObservation accuracy coefficient floor) :
    Norm.Basic.normSq (retained.reading - scalarReading differential point rootObservation) <
      errorBound differential point floor rootObservation accuracy :=
  retained.close retained.original.original.witness_possible

end Reading

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
