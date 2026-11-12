module

public import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
public import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Preparing an original factor of an operationally nonzero product

A supplied comparison of the original product with a nonzero exact point
computes a finite product comparison and an additional operand sample index.
The cached second operand witness is bounded, so every candidate at the same
retained first operand state has an explicit positive lower squared norm.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared.Factor

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- A uniform positive bound for the original second operand's canonical witnesses. -/
@[expose] def upper (right : CoherentNamed) : Rational := 2 * (1 + right.name.process.centerBound)

/-- The original centre bound makes the canonical-witness upper bound strictly positive. -/
theorem upper_positive (right : CoherentNamed) : 0 < upper right := by
  have shifted := Order.Arithmetic.add_le_add_direct (show (1 : Rational) ≤ 1 from Order.Basic.le_refl _)
    right.name.process.centerBound_nonneg
  rewrite [add_zero] at shifted
  exact Order.Arithmetic.mul_pos_direct (by decide) ((by decide : (0 : Rational) < 1).trans_le shifted)

set_option genInjectivity false in
/-- Cached original operand observations and budgets certifying separation of the first product factor. -/
structure Observation (left right : CoherentNamed) (point : Basic.Canonical) where
  /-- The entire original first operand retained as executable data. -/
  first : CoherentNamed
  /-- The retained first operand is the original input owner. -/
  first_eq : first = left
  /-- The entire original second operand retained as executable data. -/
  second : CoherentNamed
  /-- The retained second operand is the original input owner. -/
  second_eq : second = right
  /-- The actual exact nonzero comparison point. -/
  value : Basic.Canonical
  /-- The retained point is the original requested point. -/
  value_eq : value = point
  /-- The supplied operational relation between the original product and exact point. -/
  identity : NamedEquivalent (CoherentNamed.mul left right).name (Coherence.exact point).name
  /-- The cached point squared norm. -/
  norm : Rational
  /-- The squared norm is computed from the same original point. -/
  norm_eq : norm = Norm.Basic.normSq point
  /-- The cached norm is strictly positive. -/
  norm_positive : 0 < norm
  /-- The actual cached second operand witness bound. -/
  bound : Rational
  /-- The bound uses the original second operand's centre bound. -/
  bound_eq : bound = upper right
  /-- The cached witness bound is strictly positive. -/
  bound_positive : 0 < bound
  /-- The product-comparison squared tolerance. -/
  target : Rational
  /-- The comparison tolerance pays one sixteenth of the retained norm. -/
  target_eq : target = norm / 16
  /-- The comparison request is strictly positive. -/
  target_positive : 0 < target
  /-- The extra original first operand squared-radius request. -/
  precision : Rational
  /-- The operand request pays the same comparison tolerance and second factor bound. -/
  precision_eq : precision = target / (4 * bound)
  /-- The extra operand request is strictly positive. -/
  precision_positive : 0 < precision
  /-- The actual canonical equal-index product approximation. -/
  product : ApproximationData
  /-- The cached approximation uses these same original operand names. -/
  product_eq : product = Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name
  /-- The finite comparison at the actual cached product and request. -/
  comparison : Comparison product (Name.Sampling.approximation (Coherence.exact point).name) 0 0 target
  /-- The actual common operand sample index. -/
  index : Nat
  /-- The common index is the computed radius refinement after the original product comparison. -/
  index_eq : index = Search.firstQuarterBelow 1 comparison.leftIndex precision
  /-- The common index meets the retained comparison's original product stage. -/
  index_ge : comparison.leftIndex ≤ index
  /-- The original first operand state and canonical retry position. -/
  source : Refinement.State left
  /-- The retained source is the exact original canonical sampling state. -/
  source_eq : source.source = Process.Sampling.stateAt left.name.process left.name.state index
  /-- The retained canonical retry position follows all performed sampling steps. -/
  next_eq : source.nextIndex = index + 1
  /-- The cached first operand witness. -/
  firstWitness : Basic.Canonical
  /-- The witness is read from the same cached source state. -/
  firstWitness_eq : firstWitness = (left.name.process.witness source.source).val
  /-- The cached witness is possible at the actual retained first operand state. -/
  first_possible : left.name.process.Possible source.source firstWitness
  /-- The cached original second operand sampling state. -/
  secondSource : right.name.process.State
  /-- The second operand state uses the same original common sample index. -/
  secondSource_eq : secondSource = Process.Sampling.stateAt right.name.process right.name.state index
  /-- The cached second operand witness. -/
  secondWitness : Basic.Canonical
  /-- The witness is read from the actual cached second operand state. -/
  secondWitness_eq : secondWitness = (right.name.process.witness secondSource).val
  /-- The cached second operand witness meets the retained original bound. -/
  second_bounded : Norm.Basic.normSq secondWitness ≤ bound
  /-- The cached first operand enclosure radius. -/
  radius : Rational
  /-- The radius is read from the same original retained first operand state. -/
  radius_eq : radius = (left.name.process.ball source.source).radiusSq
  /-- The actual retained source meets the extra operand precision request. -/
  radius_lt : radius < precision
  /-- The actual cached operand witnesses meet the retained product-comparison tolerance. -/
  product_close : Norm.Basic.normSq (firstWitness * secondWitness - point) < target

constructive_injectivity Observation

/-- Compute an original-factor separation observation from a supplied operational nonzero product identity. -/
@[expose] def observe (left right : CoherentNamed) (point : Basic.Canonical)
    (nonzero : point ≠ 0)
    (identity : NamedEquivalent (CoherentNamed.mul left right).name (Coherence.exact point).name) :
    Observation left right point := by
  let norm := Norm.Basic.normSq point
  have normPositive : 0 < norm := Norm.Basic.normSq_pos nonzero
  let bound := upper right
  have boundPositive : 0 < bound := upper_positive right
  let target := norm / 16
  have targetPositive : 0 < target := Order.Field.div_pos_direct normPositive (by decide)
  let precision := target / (4 * bound)
  have denominatorPositive : 0 < 4 * bound := Order.Arithmetic.mul_pos_direct (by decide) boundPositive
  have precisionPositive : 0 < precision := Order.Field.div_pos_direct targetPositive denominatorPositive
  let product := Sequence.Arithmetic.Product.sampledProductApproximation left.name right.name
  let bridge := Name.Coherent.Arithmetic.Product.Bridge.coherentMul_toNamed left right
  let productIdentity := Equivalent.trans (Equivalent.symm (Equivalent.toNamed_sampling product))
    (NamedEquivalent.trans (NamedEquivalent.symm bridge) identity)
  let comparison := productIdentity.compare 0 0 target targetPositive
  let index := Search.firstQuarterBelow 1 comparison.leftIndex precision
  have indexGe : comparison.leftIndex ≤ index := Search.firstQuarterBelow_ge 1 comparison.leftIndex precision
  have indexAccurate : Process.Sampling.refinementTarget index < precision :=
    Search.firstQuarterBelow_accurate 1 (by decide) comparison.leftIndex precision precisionPositive
  let source := Refinement.State.sampled left index
  let sourceState := source.source
  let secondSource := Process.Sampling.stateAt right.name.process right.name.state index
  let firstWitness := (left.name.process.witness sourceState).val
  let secondWitness := (right.name.process.witness secondSource).val
  let radius := (left.name.process.ball sourceState).radiusSq
  have close := comparison.close indexGe (Nat.le_refl comparison.rightIndex)
  change Norm.Basic.normSq (firstWitness * secondWitness - point) < target at close
  exact
    { first := left
      first_eq := rfl
      second := right
      second_eq := rfl
      value := point
      value_eq := rfl
      identity := identity
      norm := norm
      norm_eq := rfl
      norm_positive := normPositive
      bound := bound
      bound_eq := rfl
      bound_positive := boundPositive
      target := target
      target_eq := rfl
      target_positive := targetPositive
      precision := precision
      precision_eq := rfl
      precision_positive := precisionPositive
      product := product
      product_eq := rfl
      comparison := comparison
      index := index
      index_eq := rfl
      index_ge := indexGe
      source := source
      source_eq := Refinement.State.sampled_source left index
      next_eq := Refinement.State.sampled_nextIndex left index
      firstWitness := firstWitness
      firstWitness_eq := rfl
      first_possible := (left.name.process.witness sourceState).property
      secondSource := secondSource
      secondSource_eq := rfl
      secondWitness := secondWitness
      secondWitness_eq := rfl
      second_bounded := Process.Sampling.witnessAt_bounded right.name.process right.name.state index
      radius := radius
      radius_eq := rfl
      radius_lt := (Refinement.State.sampled_accurate left index).trans indexAccurate
      product_close := close }

/-- Four retained product tolerances equal one quarter of the same cached point norm. -/
theorem Observation.four_target {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) : 4 * observation.target = observation.norm / 4 := by
  apply Field.mul_right_cancel_of_ne (c := (4 : Rational)) (by decide)
  calc
    (4 * observation.target) * 4 = observation.target * 16 := by ring1
    _ = observation.norm := by
      rewrite [observation.target_eq]
      exact Field.div_mul_cancel_of_ne _ _ (by decide)
    _ = (observation.norm / 4) * 4 := (Field.div_mul_cancel_of_ne _ _ (by decide)).symm

/-- Every original candidate at the cached first operand state meets the computed positive factor lower bound. -/
theorem Observation.candidate_lower {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) {value : Basic.Canonical}
    (possible : left.name.process.Possible observation.source.source value) :
    observation.norm / 4 / observation.bound ≤ Norm.Basic.normSq value := by
  let center := (left.name.process.ball observation.source.source).center
  have valueInside := left.name.process.possible_inside possible
  have witnessInside := left.name.process.possible_inside observation.first_possible
  change Norm.Basic.normSq (value - center) ≤ _ at valueInside
  change Norm.Basic.normSq (observation.firstWitness - center) ≤ _ at witnessInside
  rewrite [← observation.radius_eq] at valueInside witnessInside
  have reverseInside : Norm.Basic.normSq (center - observation.firstWitness) ≤ observation.radius := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact witnessInside
  have deviation : Norm.Basic.normSq (value - observation.firstWitness) ≤ 4 * observation.radius := by
    calc
      Norm.Basic.normSq (value - observation.firstWitness) ≤
          2 * (Norm.Basic.normSq (value - center) + Norm.Basic.normSq (center - observation.firstWitness)) :=
        Norm.Bounds.normSq_sub_le_via value center observation.firstWitness
      _ ≤ 2 * (observation.radius + observation.radius) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct valueInside reverseInside) (by decide)
      _ = 4 * observation.radius := by ring1
  have radiusNonnegative : 0 ≤ observation.radius := by
    rewrite [observation.radius_eq]
    exact (left.name.process.ball observation.source.source).radiusSq_nonneg
  have denominatorPositive : 0 < 4 * observation.bound :=
    Order.Arithmetic.mul_pos_direct (by decide) observation.bound_positive
  have movement : Norm.Basic.normSq
      ((value - observation.firstWitness) * observation.secondWitness) < observation.target := by
    calc
      Norm.Basic.normSq ((value - observation.firstWitness) * observation.secondWitness) =
          Norm.Basic.normSq (value - observation.firstWitness) * Norm.Basic.normSq observation.secondWitness :=
        Norm.Basic.normSq_mul _ _
      _ ≤ (4 * observation.radius) * observation.bound :=
        Order.Arithmetic.mul_le_mul_direct deviation observation.second_bounded
          (Norm.Basic.normSq_nonneg observation.secondWitness)
          (Order.Arithmetic.mul_nonneg_direct (by decide) radiusNonnegative)
      _ = observation.radius * (4 * observation.bound) := by ring1
      _ < observation.precision * (4 * observation.bound) :=
        Order.Arithmetic.mul_lt_mul_of_pos_right_direct observation.radius_lt denominatorPositive
      _ = observation.target := by
        rewrite [observation.precision_eq]
        exact Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have movement_eq : value * observation.secondWitness - observation.firstWitness * observation.secondWitness =
      (value - observation.firstWitness) * observation.secondWitness := by ring1
  have productClose : Norm.Basic.normSq (value * observation.secondWitness - point) <
      4 * observation.target := by
    calc
      Norm.Basic.normSq (value * observation.secondWitness - point) ≤
          2 * (Norm.Basic.normSq (value * observation.secondWitness -
            observation.firstWitness * observation.secondWitness) +
            Norm.Basic.normSq (observation.firstWitness * observation.secondWitness - point)) :=
        Norm.Bounds.normSq_sub_le_via _ _ _
      _ < 2 * (observation.target + observation.target) := by
        rewrite [movement_eq]
        exact Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Order.Arithmetic.add_lt_add_direct movement observation.product_close)
      _ = 4 * observation.target := by ring1
  rewrite [observation.four_target] at productClose
  have reverseClose : Norm.Basic.normSq (point - value * observation.secondWitness) ≤ Norm.Basic.normSq point / 4 := by
    rewrite [Norm.Bounds.normSq_sub_symm, ← observation.norm_eq]
    exact productClose.le
  have productLower := Norm.Bounds.quarter_normSq_le_of_close point (value * observation.secondWitness) reverseClose
  rewrite [← observation.norm_eq] at productLower
  exact Norm.Bounds.factor_normSq_lower observation.bound_positive observation.second_bounded productLower

/-- The retained observation gives candidate apartness throughout the future of its original first operand state. -/
def Observation.evidence {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) :
    Process.Apart.Possible.PossibleApart (Process.Based.based left.name.process observation.source.source) where
  lowerSq := observation.norm / 4 / observation.bound
  positive := Order.Field.div_pos_direct
    (Order.Field.div_pos_direct observation.norm_positive (by decide)) observation.bound_positive
  lower := by
    intro state value possible
    exact observation.candidate_lower (state.persists possible)

/-- Prepare the original first operand using the same retained source and computed candidate lower bound. -/
def Observation.prepare {left right : CoherentNamed} {point : Basic.Canonical}
    (observation : Observation left right point) : Prepared left :=
  Prepared.ofEvidence observation.source observation.evidence

end Purelib.Approximation.Gaussian.Division.Prepared.Factor

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Equivalence

/-- A prepared original factor of an operationally zero product certifies that its actual other factor is zero. -/
def zero_other_factor {left : CoherentNamed} (prepared : Prepared left) (right : CoherentNamed)
    (identity : Zero.ZeroIdentity (CoherentNamed.mul left right)) : Zero.ZeroIdentity right := by
  have actualProduct := NamedEquivalent.trans
    (Congruence.coherentMul_respects prepared.denominator left right right
      (NamedEquivalent.symm prepared.equivalent) (NamedEquivalent.refl _)) identity
  have sameProducts := NamedEquivalent.trans actualProduct
    (NamedEquivalent.symm (Arithmetic.Mul.coherentMul_zero_right prepared.denominator))
  exact Cancellation.coherentMul_cancel_left prepared.denominator right (Coherence.exact 0)
    prepared.apart sameProducts

end Purelib.Approximation.Gaussian.Division.Prepared

end
