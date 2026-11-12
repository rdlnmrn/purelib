module

public import Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Query
public import Purelib.Riemann.RootContinuation.SquareRootProvenance.Movement
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Signed root streams inside one original fixed-box budget

Every requested radicand sample produces its own exact target owner and
retained certified root query. Same-box sum separation bounds independent
samples, while residual decay gives the named square agreement. The original
name is retained alongside its existing apartified denominator presentation.
-/

public section

namespace Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Budget

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric.Basic
  (quarterRadius quarterRadius_pos quarterRadius_antitone quarterRadius_eq_mul_pow)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Rational (Box)

variable {source : Canonical} {original : Owner source} (budget : Budget original)
    (radicand : GeometricApproximation)
    (within : ∀ index, Norm.Basic.normSq (source - radicand.sample index) ≤ budget.movement)
    (separated : budget.movement < Norm.Basic.normSq source)

include within separated in
/-- A retained sample inside a movement budget below the reference quadrance is nonzero. -/
theorem sample_nonzero (index : Nat)
    (parameter : { value : Canonical // value = radicand.sample index }) : parameter.val ≠ 0 := by
  intro zero
  have paid := within index
  rewrite [← parameter.property, zero, Basic.sub_zero] at paid
  exact (not_le_of_gt separated) paid

include within in
/-- The SAME cached radicand sample pays the original budget's canonical-norm movement input. -/
theorem sample_movement (index : Nat)
    (parameter : { value : Canonical // value = radicand.sample index }) :
    Canonical.normSq (source - parameter.val) ≤ budget.movement := by
  have paid := within index
  rewrite [← parameter.property, Norm.Basic.normSq_eq_canonical] at paid
  exact paid

/-- One requested stream sample retains its actual radicand and the complete paid original root query. -/
@[expose] def Sample (index : Nat) : Type _ :=
  (parameter : { value : Canonical // value = radicand.sample index }) ×
  { value : Query budget parameter.val
      (sample_nonzero budget radicand within separated index parameter)
      (sample_movement budget radicand within index parameter)
      index (quarterRadius 1 index) (quarterRadius_pos (by decide +kernel) index) //
    value = query budget parameter.val
      (sample_nonzero budget radicand within separated index parameter)
      (sample_movement budget radicand within index parameter)
      index (quarterRadius 1 index) (quarterRadius_pos (by decide +kernel) index) }

/-- Execute one actual radicand sample and one residual-paid query on its SAME cached Gaussian parameter. -/
def sample (index : Nat) : Sample budget radicand within separated index :=
  let parameter := radicand.sample index
  let cached : { value : Canonical // value = radicand.sample index } := ⟨parameter, rfl⟩
  let queried := query budget cached.val
    (sample_nonzero budget radicand within separated index cached)
    (sample_movement budget radicand within index cached)
    index (quarterRadius 1 index) (quarterRadius_pos (by decide +kernel) index)
  ⟨cached, ⟨queried, rfl⟩⟩

/-- The same original box side and radicand scale compute the root stream's geometric density. -/
@[expose] def streamScale (side : original.track.initial.box.OutsideSide 0) : Rational :=
  (6 + 4 * radicand.errorScale) / (4 * side.margin)

/-- The root stream's computed geometric density is nonnegative. -/
theorem streamScale_nonnegative (side : original.track.initial.box.OutsideSide 0) :
    0 ≤ streamScale radicand side := by
  have numerator : 0 ≤ 6 + 4 * radicand.errorScale :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) radicand.errorScale_nonneg))
  exact Fraction.Order.Field.div_nonneg_direct numerator
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) side.margin_pos).le

/-- Later actual retained queries have the computed geometric root displacement bound. -/
theorem samples_close (side : original.track.initial.box.OutsideSide 0)
    (queries : (index : Nat) → Sample budget radicand within separated index)
    {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq ((queries later).2.val.value - (queries earlier).2.val.value) ≤
      quarterRadius (streamScale radicand side) earlier := by
  have movement : Norm.Basic.normSq ((queries later).1.val - (queries earlier).1.val) ≤
      quarterRadius radicand.errorScale earlier := by
    rewrite [(queries later).1.property, (queries earlier).1.property]
    exact radicand.later_close order
  have firstResidual : Norm.Basic.normSq
      ((queries later).2.val.value * (queries later).2.val.value - (queries later).1.val) ≤
        quarterRadius 1 earlier :=
    (queries later).2.val.residual.le.trans (quarterRadius_antitone (by decide +kernel) order)
  have lastResidual := (queries earlier).2.val.residual.le
  have bounded := SquareRootProvenance.root_difference_in_box_le side
    (queries later).2.val.value (queries earlier).2.val.value (queries later).1.val (queries earlier).1.val
    (queries later).2.val.inside (queries earlier).2.val.inside firstResidual movement lastResidual
  exact bounded.trans_eq (by
    simp only [streamScale, quarterRadius_eq_mul_pow, Fraction.Field.div_eq_mul_inv_direct,
      -eq_self, -iff_self]
    ring1)

/-- Consume the GIVEN query rule as a geometric root approximation in the SAME original signed box.

Each requested index invokes that rule once. This is an executable query
family, not an infinite memoized cache; repeated independent requests may
perform fresh finite root queries at the same index.
-/
def approximation (side : original.track.initial.box.OutsideSide 0)
    (queries : (index : Nat) → Sample budget radicand within separated index) : GeometricApproximation where
  sample := fun index => (queries index).2.val.value
  errorScale := streamScale radicand side
  errorScale_nonneg := streamScale_nonnegative radicand side
  later_close := samples_close budget radicand within separated side queries
  centerBound := original.track.initial.box.normSqBound
  centerBound_nonneg := original.track.initial.box.normSqBound_nonneg
  sample_bounded := fun index => Box.normSq_le_normSqBound (queries index).2.val.inside

/-- The geometric approximation reads the SAME retained query anchor at each requested index. -/
theorem approximation_sample (side : original.track.initial.box.OutsideSide 0)
    (queries : (index : Nat) → Sample budget radicand within separated index) (index : Nat) :
    (approximation budget radicand within separated side queries).sample index = (queries index).2.val.value := by
  unfold approximation
  rfl

namespace Stream

variable {budget radicand within separated}
    (side : original.track.initial.box.OutsideSide 0)
    (queries : (index : Nat) → Sample budget radicand within separated index)
    (retained : { value : GeometricApproximation //
      value = approximation budget radicand within separated side queries })
    (channel : { value : CoherentNamed // value = ofApproximation retained.val.toApproximation })

/-- Every actual sample of the retained geometric root has residual below its original unit quarter-radius request. -/
theorem residual (index : Nat) :
    Norm.Basic.normSq (retained.val.sample index * retained.val.sample index - radicand.sample index) <
      quarterRadius 1 index := by
  have sampleEq := (congrArg (fun value : GeometricApproximation => value.sample index) retained.property).trans
    (approximation_sample budget radicand within separated side queries index)
  have paid := (queries index).2.val.residual
  have parameterEq := congrArg (fun parameter : Canonical => Norm.Basic.normSq
    ((queries index).2.val.value * (queries index).2.val.value - parameter)) (queries index).1.property
  rewrite [sampleEq]
  exact parameterEq.symm.trans_lt paid

/-- The retained original root name squares operationally to the SAME original radicand stream. -/
def square : NamedEquivalent (channel.val.mul channel.val).name
    (ofApproximation radicand.toApproximation).name := by
  let root := channel.val
  let parameter := ofApproximation radicand.toApproximation
  have rootSame : NamedEquivalent root.name retained.val.toApproximation.toNamed :=
    NamedEquivalent.transport (congrArg CoherentNamed.name channel.property.symm) rfl (NamedEquivalent.refl _)
  let squared := retained.val.mul retained.val
  let negative := radicand.neg
  let difference := squared.add negative
  let productCompared := Geometric.Coherent.Comparison.mul_agreesWith root root retained.val retained.val squared
    rootSame rootSame (GeometricApproximation.mul_sample retained.val retained.val)
  let differenceCompared := Geometric.Coherent.Comparison.sub_agreesWith
    (root.mul root) parameter squared radicand negative difference productCompared (NamedEquivalent.refl _)
    (GeometricApproximation.neg_sample radicand) (GeometricApproximation.add_sample squared negative)
  have differenceResidual : ∀ index, Norm.Basic.normSq (difference.toApproximation.sample index - 0) ≤
      quarterRadius 1 index := by
    intro index
    change Norm.Basic.normSq (difference.sample index - 0) ≤ _
    rewrite [Basic.sub_zero]
    have actual : difference.sample index =
        retained.val.sample index * retained.val.sample index - radicand.sample index := by
      change (squared.add negative).sample index = _
      rewrite [GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
        GeometricApproximation.neg_sample]
      ring1
    rewrite [actual]
    exact (residual side queries retained index).le
  let zero := (Sequence.Equivalence.equivalent_constant difference.toApproximation 0 1
    (by decide +kernel) differenceResidual).toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed 0).symm
  exact Coherent.Additive.equivalent_of_sub_zero (root.mul root) parameter (differenceCompared.trans zero)

/-- Every possible reading of the SAME original root process lies in its retained signed box.

Whole-name equality transports the supplied original state and possibility
proof. The actual geometric source supplies one of its retained query
anchors, whose original query certificate gives that same box containment.
-/
theorem possible_inside (state : channel.val.name.process.State) {value : Canonical}
    (possible : channel.val.name.process.Possible state value) : original.track.initial.box.Contains value := by
  have transported := possible_castState channel.property state possible
  change retained.val.toApproximation.Possible (castState channel.property state) value at transported
  rcases transported with ⟨later, _, same⟩
  have sampleEq := (congrArg (fun value : GeometricApproximation => value.sample later) retained.property).trans
    (approximation_sample budget radicand within separated side queries later)
  have inside := (queries later).2.val.inside
  exact Eq.mpr (congrArg original.track.initial.box.Contains (same.trans sampleEq)) inside

/-- Every native sample of the SAME retained root channel lies in the original signed box. -/
theorem native_inside (index : Nat) :
    original.track.initial.box.Contains ((Name.Sampling.approximation channel.val.name).sample index) :=
  possible_inside side queries retained channel channel.val.name.state
    (Process.Sampling.witnessAt_possible_start channel.val.name.process channel.val.name.state index)

/-- The actual original root process has the original outside-side lower quadrance on every possible reading. -/
def possibleApart : Process.Apart.Possible.PossibleApart channel.val.name.process where
  lowerSq := side.margin
  positive := side.margin_pos
  lower := by
    intro state value possible
    have inside := possible_inside side queries retained channel state possible
    have lower := side.margin_le_normSq_sub inside
    rewrite [Basic.sub_zero] at lower
    exact lower

end Stream

/-- A signed root stream retains its query rule, root approximation, original name and division preparation. -/
@[expose] def Stream (side : original.track.initial.box.OutsideSide 0) : Type _ :=
  (queries : { value : (index : Nat) → Sample budget radicand within separated index //
    value = fun index => sample budget radicand within separated index }) ×
  (retained : { value : GeometricApproximation //
    value = approximation budget radicand within separated side queries.val }) ×
  (channel : { value : CoherentNamed // value = ofApproximation retained.val.toApproximation }) ×
  NamedEquivalent (channel.val.mul channel.val).name (ofApproximation radicand.toApproximation).name ×
  (apart : Process.Apart.Possible.PossibleApart channel.val.name.process) ×
  { prepared : Division.Prepared.DenominatorPreparation channel.val //
    prepared = Division.Prepared.DenominatorPreparation.ofPossibleApart channel.val apart }

/-- Construct one signed root query rule and retain the original process plus its actual apartified denominator. -/
def stream (side : original.track.initial.box.OutsideSide 0) : Stream budget radicand within separated side := by
  let queries := fun index => sample budget radicand within separated index
  let retained := approximation budget radicand within separated side queries
  let channel := ofApproximation retained.toApproximation
  let rootCache : { value : GeometricApproximation //
      value = approximation budget radicand within separated side queries } := ⟨retained, rfl⟩
  let channelCache : { value : CoherentNamed // value = ofApproximation rootCache.val.toApproximation } :=
    ⟨channel, rfl⟩
  let square := Stream.square side queries rootCache channelCache
  let apart := Stream.possibleApart side queries rootCache channelCache
  let prepared := Division.Prepared.DenominatorPreparation.ofPossibleApart channel apart
  exact ⟨⟨queries, rfl⟩, rootCache, channelCache, square, apart, ⟨prepared, rfl⟩⟩

end Purelib.Riemann.RootContinuation.FixedRootBoxBudget.Budget

end
