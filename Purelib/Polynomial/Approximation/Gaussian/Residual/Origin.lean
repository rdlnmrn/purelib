module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Origin
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Origin
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Origin
public import Purelib.Approximation.Gaussian.Geometric.Preparation
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Sequence.Equivalence.Power
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original-source zero certificates from retained origin data -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual.Origin

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric

/-- The same retained initial geometric observation of the original residual program and channel. -/
abbrev Initial {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) :=
  Geometric.Preparation.Observation residual.source channel residual.equivalent

set_option genInjectivity false in
/-- Retain the original residual polynomial's coordinate power and same cofactor neighborhood.

The source and channel remain the indices of the original residual.
Both coefficient caches concern that same polynomial and its retained
nonzero-origin cofactor, without constructing any isolated root family.
-/
structure Preparation {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) where
  /-- The exact original normalization's ordered squarefree decomposition. -/
  decomposition : Squarefree.Decomposition polynomial.normalize
  /-- The original polynomial's retained coordinate-power factorization. -/
  origin : Factorization.Origin.Decomposition polynomial
  /-- The actual retained same-cofactor coefficient neighborhood. -/
  neighborhood : Bounds.Origin.Neighborhood origin.cofactor

constructive_injectivity Preparation

/-- Compute coefficient caches from the original residual's positive-degree polynomial. -/
def prepare {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) : Preparation residual :=
  let nonzero := Degree.Global.isZero_false_of_natDegree_pos residual.degreePositive
  let decomposition := Squarefree.Decomposition.Compute.decomposeNormalized polynomial.normalize
    (Dense.Basic.DensePolynomial.normalize_normalize polynomial)
    (by rewrite [Dense.Basic.DensePolynomial.isZero_normalize]; exact nonzero)
    (by rewrite [Dense.Basic.DensePolynomial.natDegree_normalize]; exact residual.degreePositive)
  let origin := Factorization.Origin.prepare polynomial
    nonzero
  let neighborhood := Bounds.Origin.prepare origin.cofactor origin.originNonzero
  ⟨decomposition, origin, neighborhood⟩

/-- Positive origin order computes the same retained decomposition's original zero occurrence. -/
def Preparation.zeroOccurrence {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual)
    (positive : 0 < preparation.origin.order) :
    Multiplicity.Origin.Occurrence preparation.decomposition.positiveMultiplicityEntries := by
  have zero : polynomial.normalize.eval 0 = 0 := by
    rewrite [Dense.Basic.DensePolynomial.eval_normalize, preparation.origin.eval,
      zero_pow (Nat.ne_zero_of_lt positive), Data.Gaussian.Basic.mul_zero]
    rfl
  exact Multiplicity.Origin.ofZero preparation.decomposition zero

/-- The whole-ball norm bound needed for this same retained cofactor neighborhood. -/
abbrev Near {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual) :=
  2 * (normSq initial.ball.center + initial.ball.radiusSq) ≤ preparation.neighborhood.radiusSq

/-- The cached original initial center reads the same residual source's sample at index zero. -/
private theorem initial_center {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (initial : Initial residual) :
    initial.ball.center = residual.source.sample 0 := by
  rewrite [initial.readback, initial.state_eq]
  rfl

/-- The cached original initial radius reads the same source's original geometric allowance. -/
private theorem initial_radius {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (initial : Initial residual) :
    initial.ball.radiusSq = Basic.quarterRadius residual.source.errorScale 0 := by
  rewrite [initial.readback, initial.state_eq]
  rfl

/-- Whole-ball nearness carries the same original source's later samples inside the retained cofactor neighborhood. -/
theorem Preparation.samples_near {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual)
    (near : Near preparation initial) (index : Nat) :
    normSq (residual.source.sample index) ≤ preparation.neighborhood.radiusSq := by
  have offset := residual.source.later_close (Nat.zero_le index)
  rewrite [← initial_center initial, ← initial_radius initial] at offset
  exact (Norm.Bounds.value_normSq_le_of_offset offset).trans near

/-- The same cofactor floor transfers the original residual bound to each original sample norm power.

The exponent is the actual retained coordinate multiplicity, including its
zero case; every bound consumes the unchanged original sample and budget.
-/
theorem Preparation.power_bound {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual)
    (near : Near preparation initial) (index : Nat) :
    normSq (residual.source.sample index) ^ preparation.origin.order ≤
      Basic.quarterRadius (residual.scale / preparation.neighborhood.lower) index := by
  let point := residual.source.sample index
  have lower := preparation.neighborhood.lower_le (preparation.samples_near initial near index)
  have product := congrArg normSq (preparation.origin.eval point)
  rewrite [Norm.Basic.normSq_mul, Data.Gaussian.Power.normSq_pow] at product
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct lower
    (Arithmetic.pow_nonneg_direct (Norm.Basic.normSq_nonneg point) preparation.origin.order)
  have paid : normSq point ^ preparation.origin.order * preparation.neighborhood.lower ≤
      Basic.quarterRadius residual.scale index := by
    have commute : normSq point ^ preparation.origin.order * preparation.neighborhood.lower =
        preparation.neighborhood.lower * normSq point ^ preparation.origin.order := Fraction.Field.mul_comm _ _
    rewrite [commute]
    exact scaled.trans (product ▸ residual.bound index)
  have divided := (Field.le_div_iff_pos preparation.neighborhood.lower_positive).mpr paid
  have quarters : Basic.quarterRadius residual.scale index / preparation.neighborhood.lower =
      Basic.quarterRadius (residual.scale / preparation.neighborhood.lower) index := by
    unfold Basic.quarterRadius
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    ring0
  rewrite [quarters] at divided
  exact divided

/-- A checked original near-origin ball certifies every original operational zero request.

The original source's all-index polynomial residuals and computed cofactor
floor bound the same positive power of its sample norm. Finite searches at
each requested tolerance pay independent original starting stages; neither
syntactic identity nor an assumed successful root classifier is consumed.
-/
def Preparation.zero {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual)
    (near : Near preparation initial) (positive : 0 < preparation.origin.order) :
    Equivalence.Zero.ZeroIdentity channel := by
  let scale := residual.scale / preparation.neighborhood.lower
  have nonnegative : 0 ≤ scale := Field.div_nonneg_direct residual.scale_nonnegative
    preparation.neighborhood.lower_positive.le
  let compared := Sequence.Equivalence.Power.constant_after residual.source.toApproximation 0
    preparation.origin.order positive 0 scale nonnegative (fun index _ => by
      rewrite [Data.Gaussian.Basic.sub_zero]
      exact preparation.power_bound initial near index)
  exact residual.equivalent.trans
    (compared.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed 0).symm)

/-- A valid original near-origin residual program has positive coordinate multiplicity. -/
private theorem Preparation.order_positive {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual)
    (near : Near preparation initial) : 0 < preparation.origin.order := by
  cases order : preparation.origin.order with
  | zero =>
      let scale := residual.scale / preparation.neighborhood.lower
      have nonnegative : 0 ≤ scale := Field.div_nonneg_direct residual.scale_nonnegative
        preparation.neighborhood.lower_positive.le
      let index := Search.firstQuarterBelow scale 0 1
      have paid := preparation.power_bound initial near index
      rewrite [order, pow_zero] at paid
      have below := Search.firstQuarterBelow_accurate scale nonnegative 0 1 (by decide)
      exact (not_lt_of_ge paid below).elim
  | succ previous => exact Nat.zero_lt_succ previous

set_option genInjectivity false in
/-- A certified original zero, actual whole-ball preparation, or the same finite unresolved observation.

Each successful result retains its exact original construction equation.
Inconclusivity keeps both failed sufficient tests on the same cached ball;
it supplies no global zero, pole or divergence assertion.
-/
inductive Outcome {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual) where
  /-- The actual cofactor-neighborhood test certifies the original channel's complete zero comparison. -/
  | zero (near : Near preparation initial) (positive : 0 < preparation.origin.order)
      (occurrence : Multiplicity.Origin.Occurrence preparation.decomposition.positiveMultiplicityEntries)
      (occurrence_eq : occurrence = preparation.zeroOccurrence positive)
      (identity : Equivalence.Zero.ZeroIdentity channel)
      (identity_eq : identity = preparation.zero initial near positive)
  /-- The actual original cached ball certifies preparation of that unchanged original channel. -/
  | prepared (separated : Geometric.Preparation.Separated initial.ball) (result : Division.Prepared channel)
      (result_eq : result = Geometric.Preparation.fromBall residual.source channel residual.equivalent
        initial.state initial.ball initial.readback separated)
  /-- Both sufficient tests fail on the same retained original finite observation. -/
  | inconclusive (outside : ¬ Near preparation initial) (inseparable : ¬ Geometric.Preparation.Separated initial.ball)

constructive_injectivity Outcome

/-- Inspect the same cached original ball using its actual coefficient neighborhood and separation tests.

Both successes are constructed from the verified original conditions. The
near-origin branch derives its positive multiplicity from the original
all-index residual bounds, rather than accepting it or a successful floor
from a caller. Failure preserves both original finite unresolved tests.
-/
def Preparation.inspect {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (preparation : Preparation residual) (initial : Initial residual) :
    Outcome preparation initial :=
  if near : Near preparation initial then
    let positive := preparation.order_positive initial near
    .zero near positive (preparation.zeroOccurrence positive) rfl (preparation.zero initial near positive) rfl
  else if separated : Geometric.Preparation.Separated initial.ball then
    .prepared separated (Geometric.Preparation.fromBall residual.source channel residual.equivalent
      initial.state initial.ball initial.readback separated) rfl
  else .inconclusive near separated

set_option genInjectivity false in
/-- The actual retained coefficient caches, original observation and its certified finite outcome.

Inconclusive outcomes retain the same computed neighborhood and original
ball in this record. Success consumes those exact caches without rebuilding
them or replacing the original residual program and channel.
-/
structure Inspection {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) where
  /-- The once computed original coefficient caches. -/ preparation : Preparation residual
  /-- The actual retained original finite observation. -/ initial : Initial residual
  /-- The certified result of this same coefficient and ball inspection. -/ outcome : Outcome preparation initial

constructive_injectivity Inspection

/-- Inspect one retained original initial observation after computing its coefficient caches once. -/
def inspect {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (initial : Initial residual) : Inspection residual :=
  let preparation := prepare residual
  let outcome := preparation.inspect initial
  ⟨preparation, initial, outcome⟩

set_option genInjectivity false in
/-- Complete a retained original coefficient inspection, preserving its exact success or full localization fallback.

The inconclusive branch retains the actual complete localization cache,
stable selection and original-channel decision with their defining equalities.
Successful coefficient decisions preserve the original observation and exact
zero occurrence in the indexed inspection.
-/
inductive Completion {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (inspection : Inspection residual) where
  /-- The same inspected zero certificate requires no higher-factor isolation. -/
  | zero (near : Near inspection.preparation inspection.initial)
      (positive : 0 < inspection.preparation.origin.order)
      (occurrence : Multiplicity.Origin.Occurrence inspection.preparation.decomposition.positiveMultiplicityEntries)
      (occurrence_eq : occurrence = inspection.preparation.zeroOccurrence positive)
      (identity : Equivalence.Zero.ZeroIdentity channel)
      (identity_eq : identity = inspection.preparation.zero inspection.initial near positive)
      (computed : inspection.outcome = .zero near positive occurrence occurrence_eq identity identity_eq)
  /-- The same inspected ball retains its actual quantitative original-channel preparation. -/
  | prepared (separated : Geometric.Preparation.Separated inspection.initial.ball)
      (result : Division.Prepared channel)
      (result_eq : result = Geometric.Preparation.fromBall residual.source channel residual.equivalent
        inspection.initial.state inspection.initial.ball inspection.initial.readback separated)
      (computed : inspection.outcome = .prepared separated result result_eq)
  /-- The exact finite inconclusive inspection consumes complete localization on its retained decomposition. -/
  | localized (outside : ¬ Near inspection.preparation inspection.initial)
      (inseparable : ¬ Geometric.Preparation.Separated inspection.initial.ball)
      (computed : inspection.outcome = .inconclusive outside inseparable)
      (preparation : Localization.Preparation polynomial residual.source)
      (decomposition_eq : preparation.decomposition = inspection.preparation.decomposition)
      (preparation_eq : preparation = Localization.Preparation.ofDecomposition polynomial
        inspection.preparation.decomposition residual.source residual.scale residual.scale_nonnegative residual.bound)
      (selected : Localization.Preparation.Selection preparation)
      (selected_eq : selected = preparation.select)
      (decision : Division.Prepared.Decision channel)
      (decision_eq : decision = selected.decideOriginal channel residual.equivalent)

constructive_injectivity Completion

/-- Complete the actual inspected branch, reusing its retained decomposition for the complete fallback. -/
def Inspection.complete {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (inspection : Inspection residual) : Completion inspection :=
  match computed : inspection.outcome with
  | .zero near positive occurrence occurrenceEq identity identityEq =>
      .zero near positive occurrence occurrenceEq identity identityEq computed
  | .prepared separated result resultEq => .prepared separated result resultEq computed
  | .inconclusive outside inseparable =>
      let preparation := Localization.Preparation.ofDecomposition polynomial inspection.preparation.decomposition
        residual.source residual.scale residual.scale_nonnegative residual.bound
      let selected := preparation.select
      let decision := selected.decideOriginal channel residual.equivalent
      .localized outside inseparable computed preparation
        (Localization.Preparation.ofDecomposition_decomposition _ _ _ _ _ _) rfl
        selected rfl decision rfl

/-- Read the complete original-channel division decision from the same retained inspection and its actual completion. -/
def Completion.decision {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {inspection : Inspection residual}
    (completion : Completion inspection) : Division.Prepared.Decision channel :=
  match completion with
  | .zero _ _ _ _ identity _ _ => .excluded identity
  | .prepared _ result _ _ => .prepared result
  | .localized _ _ _ _ _ _ _ _ decision _ => decision

/-- Localized completion reads its same stored original-channel decision without repeating stable selection. -/
theorem Completion.decision_localized {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {inspection : Inspection residual}
    (outside : ¬ Near inspection.preparation inspection.initial)
    (inseparable : ¬ Geometric.Preparation.Separated inspection.initial.ball)
    (computed : inspection.outcome = .inconclusive outside inseparable)
    (preparation : Localization.Preparation polynomial residual.source)
    (decomposition_eq : preparation.decomposition = inspection.preparation.decomposition)
    (preparation_eq : preparation = Localization.Preparation.ofDecomposition polynomial
      inspection.preparation.decomposition residual.source residual.scale residual.scale_nonnegative residual.bound)
    (selected : Localization.Preparation.Selection preparation) (selected_eq : selected = preparation.select)
    (decision : Division.Prepared.Decision channel)
    (decision_eq : decision = selected.decideOriginal channel residual.equivalent) :
    (Completion.localized outside inseparable computed preparation decomposition_eq preparation_eq
      selected selected_eq decision decision_eq).decision = decision := by
  unfold Completion.decision
  rfl

/-- Completing an original inspection retains the exact previous original-channel decision in every outcome.

The finite inconclusive branch computes its original localization, pair bank,
anchor and decision once. Its complete decision agrees with the former
reader that performed selection when the decision was requested.
-/
theorem Inspection.complete_decision_eq_original {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} (inspection : Inspection residual) :
    inspection.complete.decision = match inspection.outcome with
      | .zero _ _ _ _ identity _ => .excluded identity
      | .prepared _ result _ => .prepared result
      | .inconclusive _ _ => residual.decidePrepared
          (Localization.Preparation.ofDecomposition polynomial inspection.preparation.decomposition
            residual.source residual.scale residual.scale_nonnegative residual.bound) := by
  cases inspection with
  | mk preparation initial outcome =>
      cases outcome with
      | zero _ _ _ _ _ _ => rfl
      | prepared _ _ _ => rfl
      | inconclusive _ _ => exact (residual.decidePrepared_eq _).symm

end Purelib.Polynomial.Approximation.Gaussian.Residual.Origin

end
