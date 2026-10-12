module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.Resource.Magnitude
public import Purelib.Approximation.Rational.Grid.CentralThird
public import Purelib.Approximation.Rational.Grid.Interior
import Purelib.Data.Rat.Fraction.Resource.Components
public import Purelib.Data.Rat.Fraction.Resource.Model

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Nat.Order
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Coordinate magnitudes of rational interval candidates

The source bound combines the two endpoint representations and the finite candidate denominator. Central-third
arithmetic and interior-grid arithmetic retain those representations through eight steps of the rational magnitude
envelope.
-/

namespace Purelib.Data.Rat.Interval.Candidates.Resource

open Purelib
open Purelib.Data.Rat
open Purelib.Algebra
open Purelib.Approximation.Rational

/-- Combine the endpoint magnitudes with the magnitude of the finite candidate denominator bound.

Take the maximum of the two actual endpoint magnitudes and the magnitude of the rational cast of max 3 (degreeBound +
2). This retains the exact common source bound for the later central-third and interior-grid arithmetic. -/
@[expose] public def intervalSourceMagnitude (a b : Fraction.Rational) (degreeBound : Nat) : Nat :=
  max (Fraction.Resource.Model.coordinateMagnitude a)
    (max (Fraction.Resource.Model.coordinateMagnitude b)
      (Fraction.Resource.Model.coordinateMagnitude ((max 3 (degreeBound + 2) : Nat) : Fraction.Rational)))

/-- The left endpoint magnitude is at most the combined interval source magnitude.

The first maximum contains the supplied left endpoint representation. -/
private theorem left_le_intervalSource (a b : Fraction.Rational)
    (degreeBound : Nat) :
    Fraction.Resource.Model.coordinateMagnitude a ≤ Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound
      := by
  simp only [intervalSourceMagnitude, Data.Nat.Order.max_eq_natMax]
  exact Data.Nat.Order.le_max_left _ _

/-- The right endpoint magnitude is at most the combined interval source magnitude.

The nested maximum contains the supplied right endpoint representation, and the outer maximum retains that bound. -/
private theorem right_le_intervalSource (a b : Fraction.Rational)
    (degreeBound : Nat) :
    Fraction.Resource.Model.coordinateMagnitude b ≤ Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound
      := by
  simp only [intervalSourceMagnitude, Data.Nat.Order.max_eq_natMax]
  exact Nat.le_trans (Data.Nat.Order.le_max_left _ _) (Data.Nat.Order.le_max_right _ _)

/-- A natural cast within the retained candidate-size bound has magnitude at most the interval source magnitude.

The supplied natural bound controls the cast representation. The denominator magnitude is retained in the nested
interval maximum. -/
private theorem natCast_le_intervalSource (a b : Fraction.Rational)
    (degreeBound value : Nat) (valueBound : value ≤ max 3 (degreeBound + 2)) :
    Fraction.Resource.Model.coordinateMagnitude (value : Fraction.Rational) ≤
      Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound := by
  apply Nat.le_trans (Fraction.Resource.Components.componentMagnitude_natCast_mono valueBound)
  simp only [intervalSourceMagnitude, Data.Nat.Order.max_eq_natMax]
  exact Nat.le_trans (Data.Nat.Order.le_max_right _ _) (Data.Nat.Order.le_max_right _ _)

/-- Three rational resource-envelope steps bound the computed lower central-third endpoint.

Subtract the endpoint records, divide the difference by three, and add the result to the left endpoint. Each operation
is bounded in the same rational magnitude model. -/
public theorem centralLower_magnitude_le (a b : Fraction.Rational) (degreeBound : Nat) :
    Fraction.Resource.Model.coordinateMagnitude (Grid.CentralThird.centralLower a b) ≤
      Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
        (Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound) 3 := by
  let bound := Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound
  have difference := Purelib.Data.Rat.Fraction.Resource.Model.normalizedSub_le
    (Interval.Candidates.Resource.right_le_intervalSource a b degreeBound)
    (Interval.Candidates.Resource.left_le_intervalSource a b degreeBound)
  have threeBound := (Interval.Candidates.Resource.natCast_le_intervalSource a b degreeBound 3
    ((by
        simpa only [Data.Nat.Order.max_eq_natMax]
          using Data.Nat.Order.le_max_left _ _))).trans
      (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound 1)
  have third := Purelib.Data.Rat.Fraction.Resource.Model.normalizedDiv_le difference threeBound
  have leftBound := (Interval.Candidates.Resource.left_le_intervalSource a b degreeBound).trans
    (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound 2)
  have result := Purelib.Data.Rat.Fraction.Resource.Model.normalizedAdd_le leftBound third
  simpa only [Grid.CentralThird.centralLower, Field.Resource.Magnitude.grow_add, Nat.cast_ofNat] using result

/-- Four rational resource-envelope steps bound the computed upper central-third endpoint.

The upper endpoint additionally multiplies the divided difference by two. The retained candidate denominator bound
controls both natural casts. -/
public theorem centralUpper_magnitude_le (a b : Fraction.Rational) (degreeBound : Nat) :
    Fraction.Resource.Model.coordinateMagnitude (Grid.CentralThird.centralUpper a b) ≤
      Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
        (Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound) 4 := by
  let bound := Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound
  have difference := Purelib.Data.Rat.Fraction.Resource.Model.normalizedSub_le
    (Interval.Candidates.Resource.right_le_intervalSource a b degreeBound)
    (Interval.Candidates.Resource.left_le_intervalSource a b degreeBound)
  have threeBound := (Interval.Candidates.Resource.natCast_le_intervalSource a b degreeBound 3
    ((by
        simpa only [Data.Nat.Order.max_eq_natMax]
          using Data.Nat.Order.le_max_left _ _))).trans
      (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound 1)
  have third := Purelib.Data.Rat.Fraction.Resource.Model.normalizedDiv_le difference threeBound
  have twoBound := (Interval.Candidates.Resource.natCast_le_intervalSource a b degreeBound 2
    (Nat.le_trans (by decide : 2 ≤ 3) (by
        simpa only [Data.Nat.Order.max_eq_natMax]
          using Data.Nat.Order.le_max_left 3 (degreeBound + 2)))).trans (Field.Resource.Magnitude.bound_le_grow
            Fraction.Resource.Model.rationalModel bound 2)
  have twice := Purelib.Data.Rat.Fraction.Resource.Model.normalizedMul_le twoBound third
  have leftBound := (Interval.Candidates.Resource.left_le_intervalSource a b degreeBound).trans
    (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound 3)
  have result := Purelib.Data.Rat.Fraction.Resource.Model.normalizedAdd_le leftBound twice
  simpa only [Grid.CentralThird.centralUpper, Field.Resource.Magnitude.grow_add, Nat.cast_ofNat] using result

/-- Four resource-envelope steps bound an interior candidate when endpoints, divisor and index cast satisfy the supplied
source bound.

The four bounds concern the actual endpoints, divisor cast and index cast. Their subtraction, division, multiplication
and addition determine the displayed candidate. -/
private theorem interiorCandidate_magnitude_le_of_source
    (a b : Fraction.Rational) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) (bound : Nat)
    (aBound : Fraction.Resource.Model.coordinateMagnitude a ≤ bound)
    (bBound : Fraction.Resource.Model.coordinateMagnitude b ≤ bound)
    (divisorBound : Fraction.Resource.Model.coordinateMagnitude (degreeBound + 2 : Nat) ≤ bound)
    (indexBound : Fraction.Resource.Model.coordinateMagnitude (index.val + 1 : Nat) ≤ bound) :
    Fraction.Resource.Model.coordinateMagnitude (Grid.Interior.interiorCandidate a b degreeBound index) ≤
      Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel bound 4 := by
  have difference := Purelib.Data.Rat.Fraction.Resource.Model.normalizedSub_le bBound aBound
  have divisorLift := divisorBound.trans (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel
    bound 1)
  have step := Purelib.Data.Rat.Fraction.Resource.Model.normalizedDiv_le difference divisorLift
  have indexLift := indexBound.trans (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound
    2)
  have offset := Purelib.Data.Rat.Fraction.Resource.Model.normalizedMul_le indexLift step
  have aLift := aBound.trans (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel bound 3)
  have result := Purelib.Data.Rat.Fraction.Resource.Model.normalizedAdd_le aLift offset
  simpa only [Grid.Interior.interiorCandidate, Grid.Interior.interiorStep, Field.Resource.Magnitude.grow_add] using
    result

/-- Eight rational resource-envelope steps bound each retained interior candidate of the central third.

Bound central-third endpoints after at most four growth steps, then retain those bounds as the source for the four
operations constructing each interior point. The index remains in the original Fin (degreeBound + 1) family. -/
public theorem centralCandidate_magnitude_le (a b : Fraction.Rational) (degreeBound : Nat)
    (index : Fin (degreeBound + 1)) :
    Fraction.Resource.Model.coordinateMagnitude
        (Grid.Interior.interiorCandidate (Grid.CentralThird.centralLower a b) (Grid.CentralThird.centralUpper a b)
          degreeBound index) ≤
      Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
        (Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound) 8 := by
  let source := Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound
  let centralBound := Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel source 4
  have lowerBound : Fraction.Resource.Model.coordinateMagnitude (Grid.CentralThird.centralLower a b) ≤ centralBound :=
    (Interval.Candidates.Resource.centralLower_magnitude_le a b degreeBound).trans
      (Field.Resource.Magnitude.grow_mono_steps Fraction.Resource.Model.rationalModel source (by decide))
  have upperBound : Fraction.Resource.Model.coordinateMagnitude (Grid.CentralThird.centralUpper a b) ≤ centralBound :=
    Interval.Candidates.Resource.centralUpper_magnitude_le a b degreeBound
  have divisorSource := Interval.Candidates.Resource.natCast_le_intervalSource a b degreeBound
    (degreeBound + 2) ((by
        simpa only [Data.Nat.Order.max_eq_natMax]
          using Data.Nat.Order.le_max_right _ _))
  have divisorBound := divisorSource.trans
    (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel source 4)
  have indexNatural : index.val + 1 ≤ max 3 (degreeBound + 2) := by
    exact (Nat.succ_le_of_lt index.isLt).trans
      ((Nat.succ_le_succ (Nat.le_succ degreeBound)).trans
        ((by
            simpa only [Data.Nat.Order.max_eq_natMax]
              using Data.Nat.Order.le_max_right 3 (degreeBound + 2))))
  have indexSource := Interval.Candidates.Resource.natCast_le_intervalSource a b degreeBound
    (index.val + 1) indexNatural
  have indexBound := indexSource.trans
    (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel source 4)
  have candidate := Interval.Candidates.Resource.interiorCandidate_magnitude_le_of_source
    (Grid.CentralThird.centralLower a b) (Grid.CentralThird.centralUpper a b) degreeBound index centralBound
    lowerBound upperBound divisorBound indexBound
  simpa only [centralBound, Field.Resource.Magnitude.grow_add] using candidate

/-! ## Structural counts -/

/-- Count one more candidate evaluation than the supplied natural degree bound.

The finite interior grid retains exactly degreeBound + 1 candidate indices. -/
@[expose] public def safeCandidateEvaluationBudget (degreeBound : Nat) : Nat :=
  degreeBound + 1

/-- The explicit finite interior-candidate list has length exactly the evaluation budget.

The explicit list retains one entry for each index in Fin (degreeBound + 1). Its existing length certificate identifies
the same evaluation budget. -/
public theorem safeCandidate_count_eq_budget (a b : Fraction.Rational)
    (degreeBound : Nat) :
    (Grid.Interior.interiorCandidates a b degreeBound).length =
      Interval.Candidates.Resource.safeCandidateEvaluationBudget degreeBound := by
  exact Grid.Interior.interiorCandidates_length a b degreeBound

/-- Combine a supplied endpoint magnitude bound with the finite candidate denominator magnitude.

The supplied endpoint bound and the rational denominator representation are retained as the two arguments of the
displayed maximum. -/
@[expose] public def safeCutSourceMagnitude (bound degreeBound : Nat) : Nat :=
  max bound
    (Fraction.Resource.Model.coordinateMagnitude ((max 3 (degreeBound + 2) : Nat) : Fraction.Rational))

/-- Advance the exact rational resource envelope eight steps from the retained safe-cut source bound.

Use the rational magnitude model and exactly eight growth steps from the combined source bound. The envelope accounts
for central-third endpoint construction followed by the interior candidate arithmetic. -/
@[expose] public def safeCutMagnitudeEnvelope (bound degreeBound : Nat) : Nat :=
  Field.Resource.Magnitude.grow Fraction.Resource.Model.rationalModel
    (Interval.Candidates.Resource.safeCutSourceMagnitude bound degreeBound) 8

/-- Bounds on both endpoint magnitudes bound their combined interval source by the safe-cut source magnitude.

The two supplied endpoint inequalities place all three components of the interval source beneath the same safe-cut
source maximum. -/
public theorem intervalSource_le_safeCutSource
    {a b : Fraction.Rational} {bound degreeBound : Nat}
    (aBound : Fraction.Resource.Model.coordinateMagnitude a ≤ bound)
    (bBound : Fraction.Resource.Model.coordinateMagnitude b ≤ bound) :
    Interval.Candidates.Resource.intervalSourceMagnitude a b degreeBound ≤
      Interval.Candidates.Resource.safeCutSourceMagnitude bound degreeBound := by
  simp only [intervalSourceMagnitude, safeCutSourceMagnitude, Data.Nat.Order.max_eq_natMax]
  apply Data.Nat.Order.max_le
  · exact aBound.trans ((Data.Nat.Order.le_max_left _ _))
  · apply Data.Nat.Order.max_le
    · exact bBound.trans ((Data.Nat.Order.le_max_left _ _))
    · exact (Data.Nat.Order.le_max_right _ _)

/-- The computed safe-cut magnitude envelope is at least its input bound.

The source maximum includes the supplied bound, and each of the eight rational growth steps preserves that inequality.
-/
public theorem bound_le_safeCutMagnitudeEnvelope (bound degreeBound : Nat) :
    bound ≤ Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound := by
  have source : bound ≤ safeCutSourceMagnitude bound degreeBound := by
    simp only [safeCutSourceMagnitude, Data.Nat.Order.max_eq_natMax]
    exact Data.Nat.Order.le_max_left _ _
  exact Nat.le_trans source
    (Field.Resource.Magnitude.bound_le_grow Fraction.Resource.Model.rationalModel (safeCutSourceMagnitude bound
      degreeBound) 8)

end Purelib.Data.Rat.Interval.Candidates.Resource
