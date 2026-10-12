module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Lp.L1
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

public import Purelib.Data.Bool.Relation
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
section
@[expose] public section

/-!
# Coupling witnesses between named finite laws

A raw coupling computes its own marginals.  A `LawCoupling` additionally
certifies that those marginals agree in every exact evaluation with two
particular displayed distributions.  Thus transport estimates can be stated
directly about the named finite laws without quotienting atom tables.
-/

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a joint distribution and evaluation identities for its two specified marginal laws.

Both probability and expectation agreement refer to the exact original left and right distributions, without replacing
their retained atoms. -/
structure LawCoupling {α β : Type}
    (left : Distribution α) (right : Distribution β) where
  /-- The exact finite joint distribution retained for the two specified laws. -/ coupling : Coupling α β
  /-- All probabilities and expectations of the left marginal agree with the exact supplied left law. -/ leftEquivalent
    : Distribution.EvaluationEquivalent
    coupling.leftMarginal left
  /-- All probabilities and expectations of the right marginal agree with the exact supplied right law. -/
    rightEquivalent : Distribution.EvaluationEquivalent
    coupling.rightMarginal right

constructive_injectivity LawCoupling

namespace LawCoupling

/-- Couple the exact source law to its supplied pushforward using the deterministic graph joint distribution. -/
def graph {α β : Type} (source : Distribution α) (function : α → β) :
    LawCoupling source (source.map function) where
  coupling := Coupling.graph source function
  leftEquivalent := by
    constructor
    · exact Coupling.graph_leftMarginal_probability source function
    · exact Coupling.graph_leftMarginal_expectation source function
  rightEquivalent := by
    constructor
    · exact Coupling.graph_rightMarginal_probability source function
    · exact Coupling.graph_rightMarginal_expectation source function

/-- Couple two pushforwards of the same exact source by pairing their images occurrence by occurrence. -/
def ofMaps {α β γ : Type} (source : Distribution α)
    (left : α → β) (right : α → γ) :
    LawCoupling (source.map left) (source.map right) where
  coupling :=
    { joint := source.map fun item => (left item, right item) }
  leftEquivalent := by
    change Distribution.EvaluationEquivalent
      ((source.map fun item => (left item, right item)).map fun pair => pair.1)
      (source.map left)
    simpa only [] using source.map_map_evaluationEquivalent
      (fun item => (left item, right item)) (fun pair => pair.1)
  rightEquivalent := by
    change Distribution.EvaluationEquivalent
      ((source.map fun item => (left item, right item)).map fun pair => pair.2)
      (source.map right)
    simpa only [] using source.map_map_evaluationEquivalent
      (fun item => (left item, right item)) (fun pair => pair.2)

/-- Couple a retained law to itself by the identity graph and its evaluation identities. -/
def refl {α : Type} (source : Distribution α) : LawCoupling source source := by
  let graphWitness := graph source (fun item => item)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (source.map_id_evaluationEquivalent) }

/-- Couple the exact source law to a pure target law by the constant graph. -/
def collapse {α β : Type} (source : Distribution α) (target : β) :
    LawCoupling source (Distribution.pure target) := by
  let graphWitness := graph source (fun _ => target)
  exact
    { coupling := graphWitness.coupling
      leftEquivalent := graphWitness.leftEquivalent
      rightEquivalent := graphWitness.rightEquivalent.trans
        (source.map_const_evaluationEquivalent target) }

/-- Swap the original joint distribution and reverse its retained marginal evaluation certificates. -/
def symm {α β : Type} {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) : LawCoupling right left where
  coupling := witness.coupling.swap
  leftEquivalent :=
    { probability_eq := fun event =>
        (witness.coupling.swap_leftMarginal_probability event).trans
          (witness.rightEquivalent.probability_eq event)
      expectation_eq := fun value =>
        (witness.coupling.swap_leftMarginal_expectation value).trans
          (witness.rightEquivalent.expectation_eq value) }
  rightEquivalent :=
    { probability_eq := fun event =>
        (witness.coupling.swap_rightMarginal_probability event).trans
          (witness.leftEquivalent.probability_eq event)
      expectation_eq := fun value =>
        (witness.coupling.swap_rightMarginal_expectation value).trans
          (witness.leftEquivalent.expectation_eq value) }

open Purelib.Data.Rat in
/-- Read the supplied relation's mismatch probability from the retained law coupling's joint distribution. -/
def mismatchProbability {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    Fraction.Rational :=
  witness.coupling.mismatchProbability relation

/-- The identity law coupling has zero mismatch for decidable payload equality. -/
theorem refl_mismatchProbability_eq_zero {α : Type} [DecidableEq α]
    (source : Distribution α) :
    (refl source).mismatchProbability equalityRelation = 0 := by
  unfold refl mismatchProbability
  change (Coupling.graph source (fun item => item)).mismatchProbability
    equalityRelation = 0
  apply Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  change decide (atom.item = atom.item) = true
  exact decide_eq_true (rfl : atom.item = atom.item)

open Purelib.Data.Rat in
/-- Read the supplied pair-cost expectation from the retained law coupling's joint distribution. -/
def transportCost {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right)
    (cost : α → β → Fraction.Rational) : Fraction.Rational :=
  witness.coupling.transportCost cost

/-- Every law coupling has nonnegative mismatch probability. -/
theorem mismatchProbability_nonneg {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    0 ≤ witness.mismatchProbability relation :=
  witness.coupling.mismatchProbability_nonneg relation

/-- Every law coupling has mismatch probability at most one. -/
theorem mismatchProbability_le_one {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool) :
    witness.mismatchProbability relation ≤ 1 :=
  witness.coupling.mismatchProbability_le_one relation

open Purelib.Data.Rat in
/-- A retained pairwise cost bound controls both signed expectation differences between the exact specified laws. -/
theorem expectation_close_of_transportCost {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (cost : α → β → Fraction.Rational)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational)
    (bounded : ∀ atom, atom ∈ witness.coupling.joint.atoms →
      rightValue atom.item.2 - leftValue atom.item.1 ≤
          cost atom.item.1 atom.item.2 ∧
        leftValue atom.item.1 - rightValue atom.item.2 ≤
          cost atom.item.1 atom.item.2) :
    right.expectation rightValue - left.expectation leftValue ≤
          witness.transportCost cost ∧
      left.expectation leftValue - right.expectation rightValue ≤
          witness.transportCost cost := by
  have estimate := witness.coupling.expectation_close_of_transportCost
    cost leftValue rightValue bounded
  rw [witness.leftEquivalent.expectation_eq leftValue,
    witness.rightEquivalent.expectation_eq rightValue] at estimate
  exact estimate

/-- Events agreeing on related retained joint occurrences differ in law probability by at most the mismatch probability.
-/
theorem probability_close_of_eventsAgree {α β : Type}
    {left : Distribution α} {right : Distribution β}
    (witness : LawCoupling left right) (relation : α → β → Bool)
    (leftEvent : α → Bool) (rightEvent : β → Bool)
    (agree : witness.coupling.EventsAgreeOn
      relation leftEvent rightEvent) :
    right.probability rightEvent - left.probability leftEvent ≤
          witness.mismatchProbability relation ∧
      left.probability leftEvent - right.probability rightEvent ≤
          witness.mismatchProbability relation := by
  have estimate := witness.coupling.probability_close_of_eventsAgree
    relation leftEvent rightEvent agree
  rw [witness.leftEquivalent.probability_eq leftEvent,
    witness.rightEquivalent.probability_eq rightEvent] at estimate
  exact estimate

end LawCoupling

end Purelib.Measure

end

end

section
@[expose] public section

/-!
# Finite transport couplings from CCL prefixes

Two realization families over the same finite weighted prefix table have a
canonical rowwise coupling.  CCL cylinder contraction bounds its exact
expected rational-separation cost.  This is the stable transport statement;
it does not claim that nearby but unequal atomic laws have small total
variation distance.
-/

namespace Purelib.Measure.Coupling.Law

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Couple two rational probe pushforwards by their common original finite index distribution.

Each joint occurrence evaluates the same projective probe on the left and right points of the same retained index. -/
def probeLawCoupling {ι : Type}
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (leftPoints rightPoints : ι →
      Line.GaussianLine) :
    Measure.LawCoupling
      (distribution.map fun item => probe (leftPoints item))
      (distribution.map fun item => probe (rightPoints item)) :=
  LawCoupling.ofMaps distribution
    (fun item => probe (leftPoints item))
    (fun item => probe (rightPoints item))

/-- The probe coupling's rational-separation cost equals the original index distribution's integrated probe distance. -/
theorem probeLawCoupling_transportCost {ι : Type}
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (leftPoints rightPoints : ι →
      Line.GaussianLine) :
    (probeLawCoupling distribution probe leftPoints rightPoints).transportCost
        Distance.rationalSeparation =
      distribution.l1Distance
        (fun item => probe (leftPoints item))
        (fun item => probe (rightPoints item)) := by
  unfold probeLawCoupling
  unfold LawCoupling.transportCost
  unfold LawCoupling.ofMaps
  unfold Coupling.transportCost
  rw [distribution.map_expectation]
  rfl

end Purelib.Measure.Coupling.Law

end
