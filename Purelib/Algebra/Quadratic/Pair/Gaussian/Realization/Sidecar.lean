module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Coherent.Additive
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original numerical channels with admitted quadratic coordinate evidence

A sidecar retains the actual channel, original realization and cached pair
interpretation, with an operational comparison between them. Exact decisions
transport the same cached denominator presentation back to the original input;
they never replace or reconstruct that numerical channel.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Coherent
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

variable {K : Type} [ExplicitField K] [DecidableEq K]

set_option genInjectivity false in
/-- An original numerical channel linked to its retained admitted realization and exact cached pair coordinates. -/
structure Sidecar (realization : Realization K) (channel : CoherentNamed) where
  /-- The entire original numerical channel retained as executable data. -/
  source : CoherentNamed
  /-- The retained channel is the original input owner. -/
  source_eq : source = channel
  /-- The entire original admitted realization. -/
  owner : Realization K
  /-- The retained realization is the original mathematical owner. -/
  owner_eq : owner = realization
  /-- The original nominal pair of exact scalar coordinates. -/
  value : Pair K realization.parameter
  /-- The actual cached interpretation of the same original pair. -/
  retained : Denotation realization value
  /-- The comparison links the unchanged original channel to this exact cached interpretation. -/
  equivalent : NamedEquivalent channel.name retained.channel.name

constructive_injectivity Sidecar

/-- Attach admitted coordinate evidence to the exact channel of an already cached original denotation. -/
@[expose] def Denotation.sidecar {realization : Realization K} {original : Pair K realization.parameter}
    (retained : Denotation realization original) : Sidecar realization retained.channel :=
  ⟨retained.channel, rfl, retained.owner, retained.owner_eq, original, retained, NamedEquivalent.refl _⟩

/-- Transport the same admitted coordinates and cached interpretation to an explicitly compared original channel. -/
@[noinline, nospecialize] def Sidecar.transport {realization : Realization K} {first second : CoherentNamed}
    (sidecar : Sidecar realization first) (equivalent : NamedEquivalent second.name first.name) :
    Sidecar realization second :=
  ⟨second, rfl, sidecar.owner, sidecar.owner_eq, sidecar.value, sidecar.retained,
    NamedEquivalent.trans equivalent sidecar.equivalent⟩

/-- Retain the same coordinates and interpretation at an exactly equal cached source without another comparison. -/
@[expose] def Sidecar.reindex {realization : Realization K} {first second : CoherentNamed}
    (sidecar : Sidecar realization first) (same : second = first) : Sidecar realization second :=
  ⟨second, rfl, sidecar.owner, sidecar.owner_eq, sidecar.value, sidecar.retained, same.symm ▸ sidecar.equivalent⟩

omit [DecidableEq K] in
/-- Exact source reindexing preserves the same original pair coordinates. -/
theorem Sidecar.reindex_value {realization : Realization K} {first second : CoherentNamed}
    (sidecar : Sidecar realization first) (same : second = first) :
    (sidecar.reindex same).value = sidecar.value := rfl

/-- Read the original pair interpretation through the same cached source comparison. -/
def Sidecar.to_coordinates {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) : NamedEquivalent channel.name (realization.denote sidecar.value).name := by
  have equivalent := sidecar.equivalent
  rewrite [sidecar.retained.channel_eq, sidecar.retained.value_eq] at equivalent
  exact equivalent

/-- Attach generator coordinates to the exact original generator of the same retained realization. -/
@[noinline, nospecialize] def Sidecar.generator (realization : Realization K) :
    Sidecar realization realization.generator :=
  let retained := realization.retain Pair.generator
  ⟨realization.generator, rfl, realization, rfl, Pair.generator, retained,
    NamedEquivalent.symm (denote_generator (parameter := realization.parameter)
      realization.coefficient realization.zero_eq realization.one_eq realization.generator)⟩

omit [DecidableEq K] in
/-- Evidence at the original generator retains the nominal generator pair at the same original parameter. -/
theorem Sidecar.generator_value (realization : Realization K) :
    (Sidecar.generator realization).value = Pair.generator :=
  (Eq.refl _).trans (Eq.refl _)

omit [DecidableEq K] in
/-- Transport preserves the exact original coordinate cache. -/
theorem Sidecar.transport_value {realization : Realization K} {first second : CoherentNamed}
    (sidecar : Sidecar realization first) (equivalent : NamedEquivalent second.name first.name) :
    (sidecar.transport equivalent).value = sidecar.value :=
  (Eq.refl _).trans (Eq.refl _)

/-- Read exact scalar provenance from an original sidecar whose retained generator coefficient is zero. -/
@[noinline, nospecialize] def Sidecar.scalarReading {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) (zero : sidecar.value.im = 0) : RationalSidecar channel := by
  have scalar_eq : sidecar.value = Pair.scalar sidecar.value.re := Pair.ext rfl zero
  have equivalent := sidecar.to_coordinates
  rewrite [scalar_eq] at equivalent
  exact ⟨realization.coefficient sidecar.value.re,
    NamedEquivalent.trans equivalent
      (denote_scalar (parameter := realization.parameter)
        realization.coefficient realization.zero_eq realization.generator sidecar.value.re)⟩

omit [DecidableEq K] in
/-- The scalar reading is the exact mapped original unit coefficient of the same sidecar. -/
theorem Sidecar.scalarReading_value {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) (zero : sidecar.value.im = 0) :
    (sidecar.scalarReading zero).value = realization.coefficient sidecar.value.re :=
  (Eq.refl _).trans (Eq.refl _)

/-- Retain admitted evidence for the actual original numerical sum and cache its exact pair interpretation once. -/
@[noinline, nospecialize] def Sidecar.add {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) :
    Sidecar realization (CoherentNamed.add first second) := by
  let value := left.value + right.value
  let retained := realization.retain value
  have left_eq : left.retained.channel = realization.denote left.value :=
    left.retained.channel_eq.trans (congrArg realization.denote left.retained.value_eq)
  have right_eq : right.retained.channel = realization.denote right.value :=
    right.retained.channel_eq.trans (congrArg realization.denote right.retained.value_eq)
  have normal : NamedEquivalent (CoherentNamed.add (realization.denote left.value)
      (realization.denote right.value)).name retained.channel.name :=
    denote_add realization.coefficient realization.add_eq realization.generator left.value right.value
  rewrite [← left_eq, ← right_eq] at normal
  have equivalent : NamedEquivalent (CoherentNamed.add first second).name retained.channel.name :=
    NamedEquivalent.trans
      (Sum.Congruence.coherentAdd_respects first left.retained.channel
        second right.retained.channel left.equivalent right.equivalent) normal
  exact ⟨CoherentNamed.add first second, rfl, realization, rfl, value, retained, equivalent⟩

/-- Retain admitted evidence for the actual original numerical negation with the original pair negated once. -/
@[noinline, nospecialize] def Sidecar.neg {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) : Sidecar realization (CoherentNamed.neg channel) := by
  let value := -sidecar.value
  let retained := realization.retain value
  have input_eq : sidecar.retained.channel = realization.denote sidecar.value :=
    sidecar.retained.channel_eq.trans (congrArg realization.denote sidecar.retained.value_eq)
  have normal : NamedEquivalent (CoherentNamed.neg (realization.denote sidecar.value)).name retained.channel.name :=
    denote_neg realization.coefficient realization.zero_eq realization.add_eq realization.generator sidecar.value
  rewrite [← input_eq] at normal
  have equivalent : NamedEquivalent (CoherentNamed.neg channel).name retained.channel.name :=
    NamedEquivalent.trans
      (Additive.coherentNeg_respects channel sidecar.retained.channel sidecar.equivalent) normal
  exact ⟨CoherentNamed.neg channel, rfl, realization, rfl, value, retained, equivalent⟩

/-- Retain admitted evidence for the actual numerical product using the original nominal pair multiplication. -/
@[noinline, nospecialize] def Sidecar.mul {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) :
    Sidecar realization (CoherentNamed.mul first second) := by
  let value := left.value * right.value
  let retained := realization.retain value
  have left_eq : left.retained.channel = realization.denote left.value :=
    left.retained.channel_eq.trans (congrArg realization.denote left.retained.value_eq)
  have right_eq : right.retained.channel = realization.denote right.value :=
    right.retained.channel_eq.trans (congrArg realization.denote right.retained.value_eq)
  have normal : NamedEquivalent (CoherentNamed.mul (realization.denote left.value)
      (realization.denote right.value)).name retained.channel.name :=
    denote_mul realization.coefficient realization.add_eq realization.mul_eq realization.sub_eq
      realization.generator realization.identity left.value right.value
  rewrite [← left_eq, ← right_eq] at normal
  have equivalent : NamedEquivalent (CoherentNamed.mul first second).name retained.channel.name :=
    NamedEquivalent.trans
      (Product.Congruence.coherentMul_respects first left.retained.channel
        second right.retained.channel left.equivalent right.equivalent) normal
  exact ⟨CoherentNamed.mul first second, rfl, realization, rfl, value, retained, equivalent⟩

omit [DecidableEq K] in
/-- Admitted sum coordinates are the sum of the same two original input pairs. -/
theorem Sidecar.add_value {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) :
    (left.add right).value = left.value + right.value :=
  (Eq.refl _).trans (Eq.refl _)

omit [DecidableEq K] in
/-- Admitted negation coordinates are the negation of the original input pair. -/
theorem Sidecar.neg_value {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) : sidecar.neg.value = -sidecar.value :=
  (Eq.refl _).trans (Eq.refl _)

omit [DecidableEq K] in
/-- Admitted product coordinates use the original nominal pair product of both retained inputs. -/
theorem Sidecar.mul_value {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) :
    (left.mul right).value = left.value * right.value :=
  (Eq.refl _).trans (Eq.refl _)

/-- Decide exact zero or preparation at the unchanged original channel using the same retained interpretation. -/
@[noinline, nospecialize] def Sidecar.decide {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) : Prepared.Decision channel :=
  match sidecar.retained.decide with
  | .excluded zero => .excluded (NamedEquivalent.trans sidecar.equivalent zero)
  | .prepared prepared => .prepared (prepared.transport (NamedEquivalent.symm sidecar.equivalent))

set_option genInjectivity false in
/-- A cached actual reciprocal retaining the original sidecar, preparation and admitted inverse evidence. -/
structure Reciprocal {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) where
  /-- The entire original sidecar as executable data. -/
  source : Sidecar realization channel
  /-- The input is the exact original sidecar. -/
  source_eq : source = sidecar
  /-- The actual cached interpreted inverse and its original factor observation. -/
  interpreted : Inverse sidecar.retained
  /-- The same cached preparation transported to the unchanged original channel. -/
  prepared : Prepared channel
  /-- Preparation reuses this exact interpreted inverse's denominator and apartness. -/
  prepared_eq : prepared = interpreted.prepared.transport (NamedEquivalent.symm sidecar.equivalent)
  /-- The cached actual original-source reciprocal program. -/
  output : CoherentNamed
  /-- The output reuses the cached interpreted reciprocal program. -/
  output_eq : output = interpreted.output
  /-- The output is actual division through the same original-source preparation. -/
  numerical_eq : output = prepared.quotient (CoherentNamed.Coherence.exact 1)
  /-- Admitted evidence at this exact actual numerical reciprocal. -/
  result : Sidecar realization output
  /-- The output's coordinates are the original input pair's explicit inverse. -/
  value_eq : result.value = sidecar.value.inverse

constructive_injectivity Reciprocal

/-- Compute one cached actual reciprocal and propagate evidence while retaining the original source sidecar. -/
@[noinline, nospecialize] def Sidecar.reciprocal {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) (nonzero : sidecar.value ≠ 0) : Reciprocal sidecar := by
  have cachedNonzero : sidecar.retained.value ≠ 0 :=
    fun zero => nonzero (sidecar.retained.value_eq.symm.trans zero)
  let interpreted := sidecar.retained.inverse cachedNonzero
  let prepared := interpreted.prepared.transport (NamedEquivalent.symm sidecar.equivalent)
  let output := interpreted.output
  let retained : Denotation realization interpreted.value :=
    ⟨realization, rfl, interpreted.value, rfl, interpreted.interpreted, interpreted.interpreted_eq⟩
  let result : Sidecar realization output :=
    ⟨output, rfl, realization, rfl, interpreted.value, retained, interpreted.equivalent⟩
  have valueEq : result.value = sidecar.value.inverse :=
    interpreted.value_eq.trans (congrArg Pair.inverse sidecar.retained.value_eq)
  exact
    { source := sidecar
      source_eq := rfl
      interpreted := interpreted
      prepared := prepared
      prepared_eq := rfl
      output := output
      output_eq := rfl
      numerical_eq := interpreted.output_eq
      result := result
      value_eq := valueEq }

/-- Every sidecar decides operational zero and finite preparation completely at its original source channel. -/
theorem Sidecar.complete {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) :
    (Zero.IsZero channel ↔ ¬ Prepared.Equivalence.IsPrepared channel) ∧
      (Prepared.Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel) :=
  ⟨sidecar.decide.zero_iff_unpreparable, sidecar.decide.prepared_iff_nonzero⟩

/-- Sidecars at the same realization have identical original pair coordinates when their source channels agree. -/
theorem Sidecar.coordinates_eq {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second)
    (equivalent : NamedEquivalent first.name second.name) : left.value = right.value := by
  have interpreted : NamedEquivalent left.retained.channel.name right.retained.channel.name :=
    NamedEquivalent.trans (NamedEquivalent.symm left.equivalent) (NamedEquivalent.trans equivalent right.equivalent)
  rewrite [left.retained.channel_eq, right.retained.channel_eq, left.retained.value_eq,
    right.retained.value_eq] at interpreted
  exact realization.coordinates_eq left.value right.value interpreted

/-- Equal admitted coordinates compare the two unchanged original numerical channels. -/
def Sidecar.equivalent_of_coordinates {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) (same : left.value = right.value) :
    NamedEquivalent first.name second.name := by
  have interpreted : NamedEquivalent (realization.denote left.value).name (realization.denote right.value).name := by
    rewrite [same]
    exact NamedEquivalent.refl _
  exact NamedEquivalent.trans left.to_coordinates
    (NamedEquivalent.trans interpreted (NamedEquivalent.symm right.to_coordinates))

/-- Agreement of the two original admitted channels is equivalent to equality of their retained coordinates. -/
theorem Sidecar.agreement_iff {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) :
    Nonempty (NamedEquivalent first.name second.name) ↔ left.value = right.value :=
  ⟨fun ⟨equivalent⟩ => left.coordinates_eq right equivalent,
    fun same => ⟨left.equivalent_of_coordinates right same⟩⟩

set_option genInjectivity false in
/-- Complete coordinate equality or a proved obstruction to agreement of two original admitted channels. -/
inductive Sidecar.ComparisonOutcome {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) where
  /-- Retain exact coordinate agreement and the actual operational comparison of both original channels. -/
  | equal (coordinates_eq : left.value = right.value) (equivalent : NamedEquivalent first.name second.name)
  /-- Unequal admitted coordinates exclude every operational agreement between these same original channels. -/
  | unequal (coordinates_ne : left.value ≠ right.value)
      (incompatible : NamedEquivalent first.name second.name → False)

constructive_injectivity Sidecar.ComparisonOutcome

set_option genInjectivity false in
/-- A complete comparison retaining both actual original sidecars and their coordinate outcome. -/
structure Sidecar.Comparison {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) where
  /-- The entire first original sidecar and its actual cached interpretation. -/
  sourceLeft : Sidecar realization first
  /-- The retained first input is the actual original sidecar. -/
  sourceLeft_eq : sourceLeft = left
  /-- The entire second original sidecar and its independently retained interpretation. -/
  sourceRight : Sidecar realization second
  /-- The retained second input is the actual original sidecar. -/
  sourceRight_eq : sourceRight = right
  /-- Agreement or its exact coordinate obstruction at these same original inputs. -/
  outcome : ComparisonOutcome left right

constructive_injectivity Sidecar.Comparison

/-- Decide agreement of two original channels at one admitted realization using their existing coordinate caches. -/
@[noinline, nospecialize] def Sidecar.compare {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) : Sidecar.Comparison left right :=
  let outcome := if same : left.value = right.value then
      Sidecar.ComparisonOutcome.equal same (left.equivalent_of_coordinates right same)
    else Sidecar.ComparisonOutcome.unequal same (fun equivalent => same (left.coordinates_eq right equivalent))
  ⟨left, rfl, right, rfl, outcome⟩

/-- Equal retained coordinates select the computed agreement certificate at both original channels. -/
theorem Sidecar.compare_equal {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) (same : left.value = right.value) :
    (left.compare right).outcome = .equal same (left.equivalent_of_coordinates right same) := by
  unfold Sidecar.compare
  dsimp only
  rewrite [dif_pos same]
  rfl

/-- Unequal retained coordinates select the computed obstruction to every original-channel agreement. -/
theorem Sidecar.compare_unequal {realization : Realization K} {first second : CoherentNamed}
    (left : Sidecar realization first) (right : Sidecar realization second) (different : left.value ≠ right.value) :
    (left.compare right).outcome =
      .unequal different (fun equivalent => different (left.coordinates_eq right equivalent)) := by
  unfold Sidecar.compare
  dsimp only
  rewrite [dif_neg different]
  rfl

/-- Retain a scalar sidecar at an explicitly compared original channel in the same admitted realization. -/
@[noinline, nospecialize] def Sidecar.scalar (realization : Realization K) (value : K) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name (CoherentNamed.Coherence.exact (realization.coefficient value)).name) :
    Sidecar realization channel := by
  let retained := realization.retain (Pair.scalar value)
  have toScalar := denote_scalar (parameter := realization.parameter)
    realization.coefficient realization.zero_eq realization.generator value
  have toRetained : NamedEquivalent channel.name retained.channel.name :=
    NamedEquivalent.trans equivalent (NamedEquivalent.symm toScalar)
  exact ⟨channel, rfl, realization, rfl, Pair.scalar value, retained, toRetained⟩

omit [DecidableEq K] in
/-- Scalar evidence retains the original scalar pair in the same admitted parameter. -/
theorem Sidecar.scalar_value (realization : Realization K) (value : K) (channel : CoherentNamed)
    (equivalent : NamedEquivalent channel.name (CoherentNamed.Coherence.exact (realization.coefficient value)).name) :
    (Sidecar.scalar realization value channel equivalent).value = Pair.scalar value :=
  (Eq.refl _).trans (Eq.refl _)

/-- Read retained coordinates, using zero only as a scalar fallback for an absent sidecar. -/
@[expose] def Sidecar.valueOrZero {realization : Realization K} {channel : CoherentNamed} :
    Option (Sidecar realization channel) → Pair K realization.parameter
  | some sidecar => sidecar.value
  | none => 0

/-- Read an actual retained sidecar from its certified nonempty optional cache. -/
@[noinline, nospecialize] def Sidecar.get {realization : Realization K} {channel : CoherentNamed} :
    (input : Option (Sidecar realization channel)) → input.isSome = true → Sidecar realization channel
  | some retained, _ => retained
  | none, impossible => False.elim (Bool.noConfusion impossible)

omit [DecidableEq K] in
/-- Reading a certified nonempty cache returns the same original coordinate data. -/
theorem Sidecar.get_value {realization : Realization K} {channel : CoherentNamed}
    (input : Option (Sidecar realization channel)) (available : input.isSome = true) :
    (Sidecar.get input available).value = Sidecar.valueOrZero input := by
  cases input with
  | none => cases available
  | some retained => rfl

/-- Attach a mapped scalar to its original exact Gaussian coefficient channel. -/
@[noinline, nospecialize] def Sidecar.constant (realization : Realization K)
    (coefficient : Canonical) (value : K)
    (same : coefficient = realization.coefficient value) :
    Sidecar realization (CoherentNamed.Coherence.exact coefficient) :=
  Sidecar.scalar realization value (CoherentNamed.Coherence.exact coefficient) (by
    rewrite [same]
    exact NamedEquivalent.refl _)

omit [DecidableEq K] in
/-- Exact coefficient evidence retains the original mapped scalar coordinate. -/
theorem Sidecar.constant_value (realization : Realization K)
    (coefficient : Canonical) (value : K)
    (same : coefficient = realization.coefficient value) :
    (Sidecar.constant realization coefficient value same).value = Pair.scalar value :=
  Sidecar.scalar_value _ _ _ _

/-- Propagate coordinates through the original finite numerical power program, retaining each computed prefix. -/
@[noinline, nospecialize] def Sidecar.pow {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) :
    (exponent : Nat) → Sidecar realization (Power.namedPower channel exponent)
  | 0 => Sidecar.constant realization 1 1 realization.one_eq.symm
  | exponent + 1 => (sidecar.pow exponent).mul sidecar

omit [DecidableEq K] in
/-- Finite numerical powers retain the corresponding power of the same original pair coordinates. -/
theorem Sidecar.pow_value {realization : Realization K} {channel : CoherentNamed}
    (sidecar : Sidecar realization channel) (exponent : Nat) :
    (sidecar.pow exponent).value = sidecar.value ^ exponent := by
  induction exponent with
  | zero =>
      change (Sidecar.constant realization 1 1 realization.one_eq.symm).value = sidecar.value ^ 0
      rewrite [Sidecar.constant_value, pow_zero]
      exact Pair.scalar_one
  | succ exponent ih =>
      change ((sidecar.pow exponent).mul sidecar).value = sidecar.value ^ (exponent + 1)
      rewrite [Sidecar.mul_value, ih, pow_succ]
      rfl

end Purelib.Algebra.Quadratic.Pair.Gaussian.Realization

end
