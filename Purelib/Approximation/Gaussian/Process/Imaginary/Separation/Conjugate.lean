module

public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Imaginary separation from a prepared conjugate difference

The supplied preparation belongs to the original difference channel. A finite
request to that channel retains its actual operand readings; two further
requests and the prepared comparison transfer its floor to every possible
reading at the selected original input state.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence.Observation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Fraction.Order

/-- The actual original channel minus its original conjugated channel. -/
@[expose] def conjugateDifference (original : CoherentNamed) : CoherentNamed :=
  original.add (original.conj.neg)

set_option genInjectivity false in
/-- The original requests and comparison used to transfer one prepared difference floor.

The sum request retains both original operand readings and their exact sum.
The stored tail comparison is the supplied preparation's actual request, with
its selected indices and their payment bounds intact.
-/
structure ConjugateObservations (original : CoherentNamed)
    (prepared : Division.Prepared (conjugateDifference original)) (target : Fraction.Rational) where
  /-- The request on the unchanged original input. -/
  source : Request original target
  /-- The request on the actual difference and its original operand readings. -/
  difference : (request : Request (conjugateDifference original) target) ×
    Reading.SumParts original original.conj.neg request.reading
  /-- The request on the same supplied prepared denominator. -/
  denominator : Request prepared.denominator target
  /-- The actual finite comparison with both paid starting indices. -/
  comparison : Equivalence.Comparison
    (Name.Sampling.approximation (conjugateDifference original).name)
    (Name.Sampling.approximation prepared.denominator.name) 0 0 target
  /-- The retained comparison is the supplied preparation's actual comparison request. -/
  comparison_eq : comparison = prepared.equivalent.compare 0 0 target source.positive

constructive_injectivity ConjugateObservations

namespace ConjugateObservations

/-- Request each original process once and retain the preparation's comparison at the same positive target. -/
@[expose, noinline, nospecialize] def build (original : CoherentNamed)
    (prepared : Division.Prepared (conjugateDifference original))
    (target : Fraction.Rational) (positive : 0 < target) : ConjugateObservations original prepared target :=
  let source := Request.build original target positive
  let difference := Request.buildSum original original.conj.neg target positive
  let denominator := Request.build prepared.denominator target positive
  let comparison := prepared.equivalent.compare 0 0 target positive
  ⟨source, difference, denominator, comparison, rfl⟩

/-- The original denominator reading obeys the exact supplied whole-ball floor. -/
private theorem denominator_lower {original : CoherentNamed}
    {prepared : Division.Prepared (conjugateDifference original)} {target : Fraction.Rational}
    (observed : ConjugateObservations original prepared target) :
    prepared.apart.certificate.lowerSq ≤ Norm.Basic.normSq observed.denominator.reading.value :=
  prepared.apart.certificate.lower observed.denominator.reading.state
    (prepared.denominator.name.process.possible_inside observed.denominator.reading.possible)

/-- Both original operand readings are close to every candidate at the retained source request. -/
private theorem difference_error {original : CoherentNamed}
    {prepared : Division.Prepared (conjugateDifference original)} {target : Fraction.Rational}
    (observed : ConjugateObservations original prepared target) {value : Canonical}
    (possible : original.name.process.Possible observed.source.reading.state value) :
    Norm.Basic.normSq (observed.difference.1.reading.value - (value - Basic.conj value)) ≤ 32 * target := by
  let parts := observed.difference.2
  rcases parts.val.2.possible with ⟨conjugated, ⟨second, secondPossible, conjugatedEq⟩, negativeEq⟩
  have firstClose := original.coherent.possible_close parts.val.1.possible possible
  have secondClose := original.coherent.possible_close secondPossible possible
  have firstPaid := parts.left_allowance_lt
  have secondPaid := parts.right_allowance_lt
  have sourcePaid := observed.source.allowance_lt
  have firstBound : Norm.Basic.normSq (parts.val.1.value - value) ≤ 8 * target := by
    calc
      _ ≤ 4 * (original.coherent.allowance parts.val.1.state +
          original.coherent.allowance observed.source.reading.state) := firstClose
      _ ≤ 4 * (target + target) := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct firstPaid.le sourcePaid.le) (by decide)
      _ = 8 * target := by ring1
  have secondBound : Norm.Basic.normSq (second - value) ≤ 8 * target := by
    calc
      _ ≤ 4 * (original.coherent.allowance parts.val.2.state +
          original.coherent.allowance observed.source.reading.state) := secondClose
      _ ≤ 4 * (target + target) := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct secondPaid.le sourcePaid.le) (by decide)
      _ = 8 * target := by ring1
  have summed : observed.difference.1.reading.value = parts.val.1.value + -(Basic.conj second) :=
    parts.property.2.2.trans (congrArg (fun last => parts.val.1.value + last)
      (negativeEq.trans (congrArg Neg.neg conjugatedEq)))
  have identity : observed.difference.1.reading.value - (value - Basic.conj value) =
      (parts.val.1.value - value) + -(Basic.conj (second - value)) :=
    (congrArg (fun sum => sum - (value - Basic.conj value)) summed).trans (by
      apply Basic.ext
      · change parts.val.1.value.re + -second.re - (value.re - value.re) =
          (parts.val.1.value.re - value.re) + -(second.re - value.re)
        ring1
      · change parts.val.1.value.im + -(-second.im) - (value.im - -value.im) =
          (parts.val.1.value.im - value.im) + -(-(second.im - value.im))
        ring1)
  rewrite [identity]
  have triangle := Norm.Bounds.normSq_add_le_two (parts.val.1.value - value) (-(Basic.conj (second - value)))
  rewrite [Norm.Basic.normSq_neg, Norm.Basic.normSq_conj] at triangle
  calc
    _ ≤ 2 * (Norm.Basic.normSq (parts.val.1.value - value) + Norm.Basic.normSq (second - value)) := triangle
    _ ≤ 2 * (8 * target + 8 * target) := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstBound secondBound) (by decide)
    _ = 32 * target := by ring1

/-- The same retained requests bound the prepared denominator floor by the original candidate's imaginary square. -/
private theorem floor_le {original : CoherentNamed}
    {prepared : Division.Prepared (conjugateDifference original)} {target : Fraction.Rational}
    (observed : ConjugateObservations original prepared target) {value : Canonical}
    (possible : original.name.process.Possible observed.source.reading.state value) :
    prepared.apart.certificate.lowerSq ≤ 264 * target + 16 * value.im ^ 2 := by
  have close := observed.difference.1.distance_le observed.denominator observed.comparison
  have closeBound : Norm.Basic.normSq
      (observed.denominator.reading.value - observed.difference.1.reading.value) ≤ 68 * target := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    calc
      _ ≤ 32 * (target + target) + 4 * target := close
      _ = 68 * target := by ring1
  have error := observed.difference_error possible
  have firstTriangle := Norm.Bounds.normSq_sub_le_via observed.denominator.reading.value
    observed.difference.1.reading.value 0
  have secondTriangle := Norm.Bounds.normSq_sub_le_via observed.difference.1.reading.value
    (value - Basic.conj value) 0
  rewrite [Basic.sub_zero, Basic.sub_zero] at firstTriangle
  rewrite [Basic.sub_zero, Basic.sub_zero] at secondTriangle
  have squareIdentity : Norm.Basic.normSq (value - Basic.conj value) = 4 * value.im ^ 2 := by
    change (value.re - value.re) ^ 2 + (value.im - -value.im) ^ 2 = _
    ring1
  rewrite [squareIdentity] at secondTriangle
  calc
    _ ≤ Norm.Basic.normSq observed.denominator.reading.value := observed.denominator_lower
    _ ≤ 2 * (Norm.Basic.normSq (observed.denominator.reading.value - observed.difference.1.reading.value) +
        Norm.Basic.normSq observed.difference.1.reading.value) := firstTriangle
    _ ≤ 2 * (68 * target + 2 * (32 * target + 4 * value.im ^ 2)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct closeBound
          (secondTriangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct error (Fraction.Order.Basic.le_refl _)) (by decide)))) (by decide)
    _ = 264 * target + 16 * value.im ^ 2 := by ring1

/-- Transfer the prepared floor to unsigned separation at the same original requested state.

The explicit gap pays the same squared target on all three requests and the
retained comparison. Its square must fit the prepared floor after the exact
finite comparison and coherence costs.
-/
def separation {original : CoherentNamed}
    {prepared : Division.Prepared (conjugateDifference original)} {gap : Fraction.Rational}
    (observed : ConjugateObservations original prepared (gap ^ 2)) (positive : 0 < gap)
    (paid : 280 * gap ^ 2 ≤ prepared.apart.certificate.lowerSq) : Separation original := by
  refine ⟨observed.source.reading.state, gap, positive, ?_⟩
  intro value possible
  have bound := paid.trans (observed.floor_le possible)
  have reduced : gap ^ 2 * 16 ≤ value.im ^ 2 * 16 := by
    apply Arithmetic.le_of_add_le_add_right_direct (c := 264 * gap ^ 2)
    calc
      gap ^ 2 * 16 + 264 * gap ^ 2 = 280 * gap ^ 2 := by ring1
      _ ≤ 264 * gap ^ 2 + 16 * value.im ^ 2 := bound
      _ = value.im ^ 2 * 16 + 264 * gap ^ 2 := by ring1
  exact Arithmetic.le_of_mul_le_mul_right_direct reduced (by decide)

end ConjugateObservations

/-- The finite comparison overhead is a positive rational scalar. -/
private theorem comparisonCost_positive : (0 : Fraction.Rational) < 280 :=
  Fraction.Cast.Order.natCast_pos_direct (n := 280) (by decide)

/-- A positive rational imaginary gap computed from the supplied prepared denominator floor. -/
@[expose] def conjugateGap {original : CoherentNamed}
    (prepared : Division.Prepared (conjugateDifference original)) : Fraction.Rational :=
  Bounds.AccuracyRadius.accuracyRadius (prepared.apart.certificate.lowerSq / 280)

/-- The computed gap is positive because the supplied denominator floor is positive. -/
theorem conjugateGap_positive {original : CoherentNamed}
    (prepared : Division.Prepared (conjugateDifference original)) : 0 < conjugateGap prepared :=
  Bounds.AccuracyRadius.accuracyRadius_pos
    (Fraction.Order.Field.div_pos_direct prepared.apart.certificate.positive comparisonCost_positive)

/-- The computed gap pays the finite observation and comparison costs from the same prepared floor. -/
theorem conjugateGap_paid {original : CoherentNamed}
    (prepared : Division.Prepared (conjugateDifference original)) :
    280 * conjugateGap prepared ^ 2 ≤ prepared.apart.certificate.lowerSq := by
  have positive : 0 < prepared.apart.certificate.lowerSq / 280 :=
    Fraction.Order.Field.div_pos_direct prepared.apart.certificate.positive comparisonCost_positive
  have bounded := Bounds.AccuracyRadius.accuracyRadius_sq_lt positive
  have scaled := (Fraction.Order.Field.le_div_iff_pos comparisonCost_positive).mp bounded.le
  calc
    280 * conjugateGap prepared ^ 2 = conjugateGap prepared ^ 2 * 280 := by ring1
    _ ≤ prepared.apart.certificate.lowerSq := scaled

/-- Request the original difference and construct separation from its already supplied preparation.

The returned observations are the actual inputs to the returned separation;
their sum operands, denominator request and paid comparison stay available.
No algebraic decision or additional root selection is performed.
-/
@[noinline, nospecialize] def ofConjugatePrepared {original : CoherentNamed}
    (prepared : Division.Prepared (conjugateDifference original)) :
    (observed : ConjugateObservations original prepared (conjugateGap prepared ^ 2)) ×
      { result : Separation original // result = observed.separation (conjugateGap_positive prepared)
        (conjugateGap_paid prepared) } :=
  let observed := ConjugateObservations.build original prepared _
    (Arithmetic.pow_pos_direct (conjugateGap_positive prepared) 2)
  ⟨observed, ⟨observed.separation (conjugateGap_positive prepared) (conjugateGap_paid prepared), rfl⟩⟩

end Purelib.Approximation.Gaussian.Process.Imaginary.Separation

end
