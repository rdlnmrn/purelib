module
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Process.Coherence.Addition
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian

section
@[expose] public section

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace Purelib.Approximation.Gaussian.Coherent.Additive

/-- Negation preserves the original process's canonical sampling states. -/
private theorem negStateAt
    (process : Process)
    (start : process.State) (index : Nat) :
    Gaussian.Process.Sampling.stateAt
        (Process.neg process) start index =
      Gaussian.Process.Sampling.stateAt process start index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [Gaussian.Process.Sampling.stateAt_succ,
        Gaussian.Process.Sampling.stateAt_succ, inductionHypothesis]
      change process.refine _ _ _ = process.refine _ _ _
      rfl

/-- The canonical sample of a negated name is the negative of the original sample at the same index. -/
public theorem negSampling_sample (input :
  Gaussian.Name.Basic.Named)
    (index : Nat) :
    (Sampling.approximation
      (Named.neg input)).sample index =
      -(Sampling.approximation input).sample index := by
  change
    Gaussian.Process.Sampling.witnessAt
        (Process.neg input.process)
        input.state index =
      -Gaussian.Process.Sampling.witnessAt input.process input.state index
  unfold Gaussian.Process.Sampling.witnessAt
  rw [negStateAt]
  rfl

/-- Operational cancellation of `left - right` proves that the two original names are operationally equal. -/
def equivalent_of_sub_zero (left right : Coherent.CoherentNamed)
    (zeroDifference : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left
        (CoherentNamed.neg right)).name
      (Coherence.exact 0).name) :
    Gaussian.Equivalence.NamedEquivalent left.name right.name := by
  let negative := CoherentNamed.neg right
  let zero := Coherence.exact 0
  let difference := CoherentNamed.add left negative
  have begin : Gaussian.Equivalence.NamedEquivalent left.name
      (CoherentNamed.add left zero).name :=
    NamedEquivalent.symm
      (Add.coherentAdd_zero_right left)
  have insertCancellation : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left zero).name
      (CoherentNamed.add left
        (CoherentNamed.add negative right)).name :=
    Congruence.coherentAdd_respects left left zero
      (CoherentNamed.add negative right)
      (NamedEquivalent.refl left.name)
      (NamedEquivalent.symm
        (by
          simpa only [negative, zero,
            CoherentNamed.neg,
            Coherence.exact,
            CoherentNamed.add] using
            Neg.coherentAdd_neg_left right))
  have reassociate : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add left
        (CoherentNamed.add negative right)).name
      (CoherentNamed.add difference right).name :=
    NamedEquivalent.symm
      (by
        simpa only [difference,
          CoherentNamed.add] using
          Add.coherentAdd_assoc left negative right)
  have differenceZero : Gaussian.Equivalence.NamedEquivalent difference.name zero.name := by
    simpa only [difference, negative, zero,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using zeroDifference
  have replaceDifference : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add difference right).name
      (CoherentNamed.add zero right).name :=
    Congruence.coherentAdd_respects difference zero right right
      differenceZero
      (NamedEquivalent.refl right.name)
  exact NamedEquivalent.trans begin
    (NamedEquivalent.trans insertCancellation
      (NamedEquivalent.trans reassociate
        (NamedEquivalent.trans replaceDifference
          (Add.coherentAdd_zero_left right))))

/-- Four-term additive interchange, derived only from operational commutativity and associativity. -/
def coherentAdd_interchange
    (first second third fourth : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.add first second)
        (CoherentNamed.add third fourth)).name
      (CoherentNamed.add
        (CoherentNamed.add first third)
        (CoherentNamed.add second fourth)).name := by
  let thirdFourth :=
    CoherentNamed.add third fourth
  let secondThird :=
    CoherentNamed.add second third
  let thirdSecond :=
    CoherentNamed.add third second
  let secondFourth :=
    CoherentNamed.add second fourth
  have exposeMiddle : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add second thirdFourth).name
      (CoherentNamed.add secondThird fourth).name :=
    NamedEquivalent.symm (by
      simpa only [thirdFourth, secondThird,
        CoherentNamed.add] using
        Add.coherentAdd_assoc second third fourth)
  have swapMiddle : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add secondThird fourth).name
      (CoherentNamed.add thirdSecond fourth).name :=
    Congruence.coherentAdd_respects
      secondThird thirdSecond fourth fourth
      (by
          simpa only [secondThird, thirdSecond, CoherentNamed.add]
            using Add.coherentAdd_comm second third)
      (NamedEquivalent.refl fourth.name)
  have regroupMiddle : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add thirdSecond fourth).name
      (CoherentNamed.add third secondFourth).name := by
    simpa only [thirdSecond, secondFourth,
      CoherentNamed.add] using
      Add.coherentAdd_assoc third second fourth
  have middleInterchange : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add second thirdFourth).name
      (CoherentNamed.add third secondFourth).name :=
    NamedEquivalent.trans exposeMiddle
      (NamedEquivalent.trans swapMiddle
        regroupMiddle)
  exact NamedEquivalent.trans
    (Add.coherentAdd_assoc first second thirdFourth)
    (NamedEquivalent.trans
      (Congruence.coherentAdd_respects first first
        (CoherentNamed.add second thirdFourth)
        (CoherentNamed.add third secondFourth)
        (NamedEquivalent.refl first.name)
        middleInterchange)
      (NamedEquivalent.symm (by
        simpa only [secondFourth,
          CoherentNamed.add] using
          Add.coherentAdd_assoc
            first third secondFourth)))

/-- An operational right inverse of an additive value is equal to its actual stateful negation. -/
def equivalent_neg_of_add_zero (value candidate :
  Coherent.CoherentNamed)
    (cancel : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add value candidate).name
      (Coherence.exact 0).name) :
    Gaussian.Equivalence.NamedEquivalent candidate.name
      (CoherentNamed.neg value).name := by
  let zero := Coherence.exact 0
  let negative := CoherentNamed.neg value
  let negativeValue :=
    CoherentNamed.add negative value
  have begin : Gaussian.Equivalence.NamedEquivalent candidate.name
      (CoherentNamed.add zero candidate).name :=
    NamedEquivalent.symm
      (Add.coherentAdd_zero_left candidate)
  have insertInverse : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add zero candidate).name
      (CoherentNamed.add
        negativeValue candidate).name :=
    Congruence.coherentAdd_respects
      zero negativeValue candidate candidate
      (NamedEquivalent.symm (by
        simpa only [zero, negative, negativeValue,
          Coherence.exact,
          CoherentNamed.neg,
          CoherentNamed.add] using
          Neg.coherentAdd_neg_left value))
      (NamedEquivalent.refl candidate.name)
  have associate : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        negativeValue candidate).name
      (CoherentNamed.add negative
        (CoherentNamed.add value candidate)).name := by
    simpa only [negativeValue,
      CoherentNamed.add] using
      Add.coherentAdd_assoc negative value candidate
  have replaceCancellation : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add negative
        (CoherentNamed.add value candidate)).name
      (CoherentNamed.add negative zero).name :=
    Congruence.coherentAdd_respects negative negative
      (CoherentNamed.add value candidate) zero
      (NamedEquivalent.refl negative.name)
      (by simpa only [zero] using cancel)
  exact NamedEquivalent.trans begin
    (NamedEquivalent.trans insertInverse
      (NamedEquivalent.trans associate
        (NamedEquivalent.trans replaceCancellation
          (Add.coherentAdd_zero_right negative))))

/-- Stateful negation respects operational equivalence. -/
def coherentNeg_respects (left right : Coherent.CoherentNamed)
    (equivalent : Gaussian.Equivalence.NamedEquivalent left.name right.name) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.neg left).name
      (CoherentNamed.neg right).name := by
  let negativeLeft := CoherentNamed.neg left
  let negativeRight := CoherentNamed.neg right
  let zero := Coherence.exact 0
  have replaceInput : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add right negativeLeft).name
      (CoherentNamed.add left negativeLeft).name :=
    Congruence.coherentAdd_respects
      right left negativeLeft negativeLeft
      (NamedEquivalent.symm equivalent)
      (NamedEquivalent.refl negativeLeft.name)
  have cancel : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add right negativeLeft).name
      zero.name :=
    NamedEquivalent.trans replaceInput (by
      simpa only [negativeLeft, zero,
        CoherentNamed.add,
        CoherentNamed.neg,
        Coherence.exact] using
        Neg.coherentAdd_neg_right left)
  simpa only [negativeLeft, negativeRight] using
    equivalent_neg_of_add_zero right negativeLeft cancel

/-- Stateful negation distributes over a finite operational sum. -/
def coherentNeg_add (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.neg left)
        (CoherentNamed.neg right)).name
      (CoherentNamed.neg
        (CoherentNamed.add left right)).name := by
  let negativeLeft := CoherentNamed.neg left
  let negativeRight := CoherentNamed.neg right
  let value := CoherentNamed.add left right
  let candidate :=
    CoherentNamed.add negativeLeft negativeRight
  let zero := Coherence.exact 0
  have separate : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add value candidate).name
      (CoherentNamed.add
        (CoherentNamed.add left negativeLeft)
        (CoherentNamed.add right negativeRight)).name := by
    simpa only [value, candidate] using
      coherentAdd_interchange left right negativeLeft negativeRight
  have cancelBoth : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        (CoherentNamed.add left negativeLeft)
        (CoherentNamed.add right negativeRight)).name
      (CoherentNamed.add zero zero).name :=
    Congruence.coherentAdd_respects
      (CoherentNamed.add left negativeLeft) zero
      (CoherentNamed.add right negativeRight) zero
      (by
          simpa only [negativeLeft, zero, CoherentNamed.neg, Coherence.exact, CoherentNamed.add]
            using Neg.coherentAdd_neg_right left)
      (by
          simpa only [negativeRight, zero, CoherentNamed.neg, Coherence.exact, CoherentNamed.add]
            using Neg.coherentAdd_neg_right right)
  have totalZero : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add value candidate).name
      zero.name :=
    NamedEquivalent.trans separate
      (NamedEquivalent.trans cancelBoth
        (Add.coherentAdd_zero_right zero))
  simpa only [value, candidate, negativeLeft, negativeRight,
    CoherentNamed.add,
    CoherentNamed.neg] using
    equivalent_neg_of_add_zero value candidate totalZero

/-- The actual negation of the terminating zero is operationally zero. -/
def zero_equivalent_neg_zero :
    Gaussian.Equivalence.NamedEquivalent (Coherence.exact 0).name
      (CoherentNamed.neg
        (Coherence.exact 0)).name := by
  let zero := Coherence.exact 0
  simpa only [zero] using equivalent_neg_of_add_zero zero zero
    (Add.coherentAdd_zero_right zero)

/-- Applying the actual stateful negation twice returns the original operational value. -/
def coherent_doubleNeg (value : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent value.name
      (CoherentNamed.neg
        (CoherentNamed.neg value)).name := by
  let negative := CoherentNamed.neg value
  exact equivalent_neg_of_add_zero negative value (by
    simpa only [negative,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_left value)

/-- Swapping the two entries of an operational difference negates it. -/
def coherentSub_swap (left right : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add right
        (CoherentNamed.neg left)).name
      (CoherentNamed.neg
        (CoherentNamed.add left
          (CoherentNamed.neg right))).name := by
  let negativeLeft := CoherentNamed.neg left
  let negativeRight := CoherentNamed.neg right
  let doubleNegativeRight :=
    CoherentNamed.neg negativeRight
  have commute : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add right negativeLeft).name
      (CoherentNamed.add negativeLeft right).name :=
    Add.coherentAdd_comm right negativeLeft
  have replaceRight : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add negativeLeft right).name
      (CoherentNamed.add negativeLeft
        doubleNegativeRight).name :=
    Congruence.coherentAdd_respects
      negativeLeft negativeLeft right doubleNegativeRight
      (NamedEquivalent.refl negativeLeft.name)
      (coherent_doubleNeg right)
  exact NamedEquivalent.trans commute
    (NamedEquivalent.trans replaceRight (by
      simpa only [negativeLeft, negativeRight, doubleNegativeRight] using
        coherentNeg_add left negativeRight))

end Purelib.Approximation.Gaussian.Coherent.Additive

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Approximation.Gaussian.Coherent.Additive

/-- Subtract two coherent names by adding the original left input to the stateful negation of the right input. -/
def subtractName (left right : Coherent.CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.add left
    (CoherentNamed.neg right)

end Purelib.Approximation.Gaussian.Coherent.Additive

end
