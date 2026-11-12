module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Factorization
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paid observations of the original factored odd-power processes

An independently retained original evaluator is compared to its actual
factored coefficient process. The latter's reciprocal occurrences start at
the same retained cofactor observation; its exact additional weight scales
the existing plain odd-power candidate bound. The original two-process
comparison selects both actual arithmetic states and readings independently.

The original differential, polynomial coefficients, source channel, apartness,
cofactor state, original evaluator and factored evaluator remain indices.
No scalar anchor is substituted for either actual arithmetic witness.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

variable {radicand : Coefficients}

/-- The exact additional coefficient weight of the existing factored odd-power process. -/
@[expose] def weight (differential : OddPowerDifferential radicand) (factor velocity : Canonical) : Canonical :=
  velocity * factor⁻¹ ^ (2 * differential.denominatorPairs)

/-- The factored coefficient's scalar anchor uses the unchanged original cofactor observation witness. -/
@[expose] def scalarReading (differential : OddPowerDifferential radicand) (point factor velocity : Canonical)
    (observation : RootObservation) : Canonical :=
  weight differential factor velocity * Observation.scalarReading differential point observation

/-- The exact original scalar weight multiplies the plain arithmetic candidate sensitivity. -/
@[expose] def sensitivity (differential : OddPowerDifferential radicand) (point factor velocity : Canonical)
    (floor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq (weight differential factor velocity) * Cache.sensitivity differential point floor

/-- The computed factored sensitivity is nonnegative under the actual original candidate floor. -/
theorem sensitivity_nonnegative (differential : OddPowerDifferential radicand) (point factor velocity : Canonical)
    {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ sensitivity differential point factor velocity floor :=
  Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
    (Cache.sensitivity_nonnegative differential point positive)

/-- The original free request and paid cofactor spread determine the factored arithmetic error bound. -/
@[expose] def errorBound (differential : OddPowerDifferential radicand) (point factor velocity : Canonical)
    (floor : Fraction.Rational) (observation : RootObservation) (accuracy : AccuracyRequest) : Fraction.Rational :=
  accuracy.tolerance + 4 * sensitivity differential point factor velocity floor * observation.spread

/-- Initialize every actual factored reciprocal occurrence at the identical retained cofactor process state. -/
@[expose] def initialState (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (factor velocity : Canonical) :
    (differential.factorizedValue point sheet apart factor velocity).name.process.State :=
  ((), Name.Coherent.Power.stateFrom (Arithmetic.reciprocalChannel sheet apart) ((), state)
    differential.denominatorExponent)

/-- Pay the actual factored reciprocal-power subtree by the original plain bound and its exact weight. -/
theorem initial_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (cache_eq : observation = sheet.name.process.observation state)
    (factor velocity : Canonical) {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    {candidate : Canonical}
    (possible : (differential.factorizedValue point sheet apart factor velocity).name.process.Possible
      (initialState differential point sheet apart state factor velocity) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point factor velocity observation) ≤
      sensitivity differential point factor velocity floor * observation.spread := by
  rcases possible with ⟨coefficient, power, coefficientPossible, powerPossible, rfl⟩
  change coefficient = differential.scale * differential.numerator.eval point * velocity *
    factor⁻¹ ^ (2 * differential.denominatorPairs) at coefficientPossible
  rewrite [coefficientPossible]
  let plain := (differential.scale * differential.numerator.eval point) * power
  have plainPossible : (differential.value point sheet apart).name.process.Possible
      (Observation.initialState differential point sheet apart state) plain :=
    ⟨differential.scale * differential.numerator.eval point, power, rfl, powerPossible, rfl⟩
  have paid := Cache.initial_candidate_close differential point sheet apart state observation cache_eq
    positive lower plainPossible
  have identity :
      (differential.scale * differential.numerator.eval point * velocity *
          factor⁻¹ ^ (2 * differential.denominatorPairs)) * power -
        scalarReading differential point factor velocity observation =
      weight differential factor velocity * (plain - Observation.scalarReading differential point observation) := by
    unfold scalarReading weight
    dsimp only [plain]
    ring1
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid (Norm.Basic.normSq_nonneg _)).trans_eq
    (by unfold sensitivity; ring1)

/-- Exact complete factored-cache equality transports its initialized original cofactor state. -/
@[expose] def cachedInitialState (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (factor velocity : Canonical) (factored : CoherentNamed)
    (cache_eq : factored = differential.factorizedValue point sheet apart factor velocity) :
    factored.name.process.State :=
  Process.Sampling.castState (congrArg (fun value : CoherentNamed => value.name.process) cache_eq).symm
    (initialState differential point sheet apart state factor velocity)

/-- The original two-process comparison type keeps both evaluator owners and the exact initialized factored state. -/
abbrev PreparedComparison (original factored : CoherentNamed) (paidStart : factored.name.process.State)
    (accuracy : AccuracyRequest) :=
  Equivalence.Comparison (Name.Sampling.approximation original.name)
    (Name.Sampling.approximation ({ process := factored.name.process, state := paidStart } : Named))
    (minimumIndex accuracy) 0 (comparisonRequest accuracy).tolerance

/-- Complete factored-cache and state equalities preserve the original initialized candidate bound. -/
private theorem cached_initial_candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    (factor velocity : Canonical) (factored : CoherentNamed)
    (cache_eq : factored = differential.factorizedValue point sheet apart factor velocity)
    (paidStart : factored.name.process.State)
    (paidStart_eq : paidStart =
      cachedInitialState differential point sheet apart state factor velocity factored cache_eq)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    {candidate : Canonical} (possible : factored.name.process.Possible paidStart candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point factor velocity observation) ≤
      sensitivity differential point factor velocity floor * observation.spread := by
  cases cache_eq
  cases paidStart_eq
  exact initial_candidate_close differential point sheet apart state observation rootCache factor velocity
    positive lower possible

/-- Pay each original evaluator candidate with its own spread, comparison and initialized factored bound. -/
private theorem candidate_close (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    (factor velocity : Canonical) (original factored : CoherentNamed)
    (cache_eq : factored = differential.factorizedValue point sheet apart factor velocity)
    (paidStart : factored.name.process.State)
    (paidStart_eq : paidStart =
      cachedInitialState differential point sheet apart state factor velocity factored cache_eq)
    {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate)
    (accuracy : AccuracyRequest) (comparison : PreparedComparison original factored paidStart accuracy)
    {candidate : Canonical}
    (possible : original.name.process.Possible
      (Process.Sampling.stateAt original.name.process original.name.state comparison.leftIndex) candidate) :
    Norm.Basic.normSq (candidate - scalarReading differential point factor velocity observation) <
      errorBound differential point factor velocity floor observation accuracy := by
  let leftState := Process.Sampling.stateAt original.name.process original.name.state comparison.leftIndex
  let leftReading := Process.Sampling.witnessAt original.name.process original.name.state comparison.leftIndex
  let rightReading := Process.Sampling.witnessAt factored.name.process paidStart comparison.rightIndex
  have leftPossible := Process.Sampling.witnessAt_possible
    original.name.process original.name.state comparison.leftIndex
  have rightPossible := Process.Sampling.witnessAt_possible factored.name.process paidStart comparison.rightIndex
  have paid := cached_initial_candidate_close differential point sheet apart state observation rootCache factor velocity
    factored cache_eq paidStart paidStart_eq positive lower
    (Process.Sampling.stateAt_possible_at_start factored.name.process paidStart comparison.rightIndex rightPossible)
  have pairwise := (original.name.process.observation leftState).pairwise possible leftPossible
  have spread : Norm.Basic.normSq (candidate - leftReading) < 4 * (radiusRequest accuracy).tolerance :=
    pairwise.trans_lt (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
      (Observation.radius_lt original accuracy comparison.left_ge))
  have compared : Norm.Basic.normSq (leftReading - rightReading) < (comparisonRequest accuracy).tolerance :=
    comparison.close (Nat.le_refl _) (Nat.le_refl _)
  have anchor : Norm.Basic.normSq (leftReading - scalarReading differential point factor velocity observation) <
      2 * ((comparisonRequest accuracy).tolerance +
        sensitivity differential point factor velocity floor * observation.spread) :=
    calc
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          Norm.Basic.normSq (rightReading - scalarReading differential point factor velocity observation)) :=
        Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (Norm.Basic.normSq (leftReading - rightReading) +
          sensitivity differential point factor velocity floor * observation.spread) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) paid) (by decide +kernel)
      _ < _ := Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_right_direct compared _)
  calc
    _ ≤ 2 * (Norm.Basic.normSq (candidate - leftReading) +
        Norm.Basic.normSq (leftReading - scalarReading differential point factor velocity observation)) :=
      Norm.Bounds.normSq_sub_le_via _ _ _
    _ < 2 * (4 * (radiusRequest accuracy).tolerance +
        2 * ((comparisonRequest accuracy).tolerance +
          sensitivity differential point factor velocity floor * observation.spread)) :=
      Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
        (Order.Arithmetic.add_lt_add_direct spread anchor)
    _ = _ := by
      rewrite [Observation.budget_identity]
      unfold errorBound
      ring1

set_option genInjectivity false in
/-- Actual independently selected observations of the retained original and factored arithmetic processes.

The existing original Comparison owns both finite selected indices. Stored
states and observations read those exact indices, while the factored start
places every original cofactor occurrence at the supplied retained state.
The actual observed candidate bound is derived by the request constructor.
-/
structure Reading (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (factor velocity : Canonical)
    (original factored : CoherentNamed) (accuracy : AccuracyRequest) (floor : Fraction.Rational) where
  /-- The unchanged cofactor observation belongs to its exact original selected process state. -/
  rootCache_eq : observation = sheet.name.process.observation state
  /-- The complete retained factored evaluator is the existing original factorization factory. -/
  factored_eq : factored = differential.factorizedValue point sheet apart factor velocity
  /-- The original retained evaluator agrees with that actual factored process. -/
  agreement : NamedEquivalent original.name factored.name
  /-- The initialized actual factored process state retains every original cofactor occurrence. -/
  paidStart : factored.name.process.State
  /-- The initialized state is its exact original cache-transport factory. -/
  paidStart_eq : paidStart =
    cachedInitialState differential point sheet apart state factor velocity factored factored_eq
  /-- The existing two-process comparison owns the actual original and initialized factored sample indices. -/
  comparison : PreparedComparison original factored paidStart accuracy
  /-- The actual original evaluator state selected by that retained comparison. -/
  originalState : original.name.process.State
  /-- The original state belongs to the exact retained left comparison index. -/
  originalState_eq : originalState =
    Process.Sampling.stateAt original.name.process original.name.state comparison.leftIndex
  /-- The actual independently selected factored arithmetic state. -/
  paidState : factored.name.process.State
  /-- The paid state belongs to the exact retained right comparison index. -/
  paidState_eq : paidState = Process.Sampling.stateAt factored.name.process paidStart comparison.rightIndex
  /-- The retained original arithmetic observation, with its actual candidate predicate and witness. -/
  originalObservation : RootObservation
  /-- The original observation is the actual observation of its selected original process state. -/
  original_eq : originalObservation = original.name.process.observation originalState
  /-- The actual observation of the independently selected factored process state. -/
  paidObservation : RootObservation
  /-- The paid observation belongs to that same actual independently selected state. -/
  paid_eq : paidObservation = factored.name.process.observation paidState
  /-- The actual original cofactor candidate floor is positive. -/
  positive : 0 < floor
  /-- Every original cofactor observation candidate pays the same finite floor. -/
  lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate
  /-- Every actual original arithmetic observation candidate meets the internally paid scalar bound. -/
  close : ∀ {candidate : Canonical}, originalObservation.Possible candidate →
    Norm.Basic.normSq (candidate - scalarReading differential point factor velocity observation) <
      errorBound differential point factor velocity floor observation accuracy

constructive_injectivity Reading

/-- Compare and observe both unchanged actual evaluator processes using one retained original cofactor observation.

The existing operational agreement and rebase comparison select both states
once. Each actual observation retains its own selected witness; the cofactor
floor and spread internally pay their difference from the prescribed scalar
anchor without substituting that anchor into either arithmetic process.
-/
def request (differential : OddPowerDifferential radicand) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) (state : sheet.name.process.State)
    (observation : RootObservation) (rootCache : observation = sheet.name.process.observation state)
    (factor velocity : Canonical) (original factored : CoherentNamed)
    (factored_eq : factored = differential.factorizedValue point sheet apart factor velocity)
    (agreement : NamedEquivalent original.name factored.name) (accuracy : AccuracyRequest)
    (floor : Fraction.Rational) (positive : 0 < floor)
    (lower : ∀ {candidate : Canonical}, observation.Possible candidate → floor ≤ Norm.Basic.normSq candidate) :
    Reading differential point sheet apart state observation factor velocity original factored accuracy floor := by
  let paidStart := cachedInitialState differential point sheet apart state factor velocity factored factored_eq
  let comparison := (agreement.trans (factored.rebaseEquivalent paidStart)).compare (minimumIndex accuracy) 0
    (comparisonRequest accuracy).tolerance (comparisonRequest accuracy).positive
  let originalState := Process.Sampling.stateAt original.name.process original.name.state comparison.leftIndex
  let paidState := Process.Sampling.stateAt factored.name.process paidStart comparison.rightIndex
  let originalObservation := original.name.process.observation originalState
  let paidObservation := factored.name.process.observation paidState
  exact
    { rootCache_eq := rootCache
      factored_eq := factored_eq
      agreement := agreement
      paidStart := paidStart
      paidStart_eq := rfl
      comparison := comparison
      originalState := originalState
      originalState_eq := rfl
      paidState := paidState
      paidState_eq := rfl
      originalObservation := originalObservation
      original_eq := rfl
      paidObservation := paidObservation
      paid_eq := rfl
      positive := positive
      lower := lower
      close := by
        intro candidate possible
        change original.name.process.Possible originalState candidate at possible
        exact candidate_close differential point sheet apart state observation rootCache
          factor velocity original factored
          factored_eq paidStart rfl positive lower accuracy comparison possible }

namespace Reading

/-- Read the actual original evaluator witness from its same retained selected observation. -/
@[expose] def reading {differential : OddPowerDifferential radicand} {point : Canonical}
    {sheet : CoherentNamed} {apart : Named.Apart sheet.name} {state : sheet.name.process.State}
    {observation : RootObservation} {factor velocity : Canonical} {original factored : CoherentNamed}
    {accuracy : AccuracyRequest} {floor : Fraction.Rational}
    (retained : Reading differential point sheet apart state observation
      factor velocity original factored accuracy floor) :
    Canonical := retained.originalObservation.witness

/-- The independent actual evaluator witness pays the retained factored coefficient's internally computed bound. -/
theorem reading_close {differential : OddPowerDifferential radicand} {point : Canonical}
    {sheet : CoherentNamed} {apart : Named.Apart sheet.name} {state : sheet.name.process.State}
    {observation : RootObservation} {factor velocity : Canonical} {original factored : CoherentNamed}
    {accuracy : AccuracyRequest} {floor : Fraction.Rational}
    (retained : Reading differential point sheet apart state observation
      factor velocity original factored accuracy floor) :
    Norm.Basic.normSq (retained.reading - scalarReading differential point factor velocity observation) <
      errorBound differential point factor velocity floor observation accuracy :=
  retained.close retained.originalObservation.witness_possible

end Reading

/-- The exact factored weight scales the original paid arithmetic allowance of the same retained cofactor root. -/
@[expose] def allowanceFactor {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (point factor velocity : Canonical) (root : CertifiedSquareRoot.Certificate parameter)
    (floor : Fraction.Rational) : Fraction.Rational :=
  1 + Norm.Basic.normSq (weight differential factor velocity) * Cache.allowanceFactor differential point root floor

/-- The paid factored arithmetic allowance is nonnegative under the original positive candidate floor. -/
theorem allowanceFactor_nonnegative {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (point factor velocity : Canonical) (root : CertifiedSquareRoot.Certificate parameter)
    {floor : Fraction.Rational} (positive : 0 < floor) :
    0 ≤ allowanceFactor differential point factor velocity root floor :=
  Order.Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Cache.allowanceFactor_nonnegative differential point root positive))

/-- The same original cofactor observation pays the factored process error through the original scaled allowance.

The unchanged observation request pays spread before the original square
comparison selects its state. Scaling the original public arithmetic bound
preserves that observation, root and radius denominator without a new query
or duplicated square-sampling estimate.
-/
theorem errorBound_le_factor {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (point factor velocity : Canonical) (root : CertifiedSquareRoot.Certificate parameter) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy)
    {floor : Fraction.Rational} (positive : 0 < floor) :
    errorBound differential point factor velocity floor sample.observation accuracy ≤
      allowanceFactor differential point factor velocity root floor * accuracy.tolerance := by
  have plain := Cache.errorBound_le_factor differential point root sample positive
  have plainPayment : 4 * Cache.sensitivity differential point floor * sample.observation.spread ≤
      Cache.errorBound differential point floor sample.observation accuracy := by
    change 4 * Cache.sensitivity differential point floor * sample.observation.spread ≤
      accuracy.tolerance + 4 * Cache.sensitivity differential point floor * sample.observation.spread
    have paid := Order.Arithmetic.add_le_add_direct accuracy.positive.le
      (Fraction.Order.Basic.le_refl (4 * Cache.sensitivity differential point floor * sample.observation.spread))
    rewrite [Fraction.Field.zero_add] at paid
    exact paid
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (plainPayment.trans plain)
    (Norm.Basic.normSq_nonneg (weight differential factor velocity))
  have added := Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl accuracy.tolerance) scaled
  exact (show errorBound differential point factor velocity floor sample.observation accuracy =
    accuracy.tolerance + Norm.Basic.normSq (weight differential factor velocity) *
      (4 * Cache.sensitivity differential point floor * sample.observation.spread) by
        unfold errorBound sensitivity
        ring1).trans_le
    (added.trans_eq (by unfold allowanceFactor; ring1))

/-- The original fixed-box arithmetic allowance and exact weight budget compute the factored allowance ceiling. -/
@[expose] def allowanceCeiling (differential : OddPowerDifferential radicand)
    (box : Purelib.Geometry.Rational.Box) (floor weightUpper : Fraction.Rational) : Fraction.Rational :=
  1 + weightUpper * Cache.allowanceCeiling differential box floor

/-- The computed fixed-box allowance is nonnegative under the original floor and exact weight budget. -/
theorem allowanceCeiling_nonnegative (differential : OddPowerDifferential radicand)
    (box : Purelib.Geometry.Rational.Box) {floor weightUpper : Fraction.Rational}
    (positive : 0 < floor) (weightNonnegative : 0 ≤ weightUpper) :
    0 ≤ allowanceCeiling differential box floor weightUpper :=
  Order.Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    (Order.Arithmetic.mul_nonneg_direct weightNonnegative
      (Cache.allowanceCeiling_nonnegative differential box positive))

/-- The original exact coefficient weight and point enclosure pay the factored allowance's fixed-box ceiling. -/
theorem allowanceFactor_le_ceiling {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (point factor velocity : Canonical) (root : CertifiedSquareRoot.Certificate parameter)
    {box : Purelib.Geometry.Rational.Box} (inside : box.Contains point) {floor weightUpper : Fraction.Rational}
    (positive : 0 < floor) (weightBound : Norm.Basic.normSq (weight differential factor velocity) ≤ weightUpper) :
    allowanceFactor differential point factor velocity root floor ≤
      allowanceCeiling differential box floor weightUpper := by
  unfold allowanceFactor allowanceCeiling
  exact Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
    (Order.Arithmetic.mul_le_mul_direct weightBound
      (Cache.allowanceFactor_le_ceiling differential root inside positive)
      (Cache.allowanceFactor_nonnegative differential point root positive)
      ((Norm.Basic.normSq_nonneg _).trans weightBound))

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization

end
