module
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Addition
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Data.Rat

section
@[expose] public section

/-!
# One certified complex logarithm branch chart

A chart scales the input by one displayed Gaussian rational `factor`, forms
the exact progressive quotient

`(factor * input - 1) / (factor * input + 1)`,

and requires finite certificates that every possible denominator has a fixed
positive lower quadrance and that every possible quotient lies in the local
disk of the finite complex-log recurrence.  One finite preparation step turns
the first certificate into whole-ball apartness before division.  A separate
progressive correction name selects the desired additive branch normalization.

This is deliberately a one-chart interface.  It is not a total complex
logarithm and it does not hide a branch choice or a completed complex value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction

/-- The terminating Gaussian name for one. -/
def exactOne : Gaussian.Name.Basic.Named :=
  Named.exact 1

/-- Multiply the original Gaussian name by the exact displayed Gaussian scale factor. -/
def scaled (input : Gaussian.Name.Basic.Named) (factor :
  Canonical) : Gaussian.Name.Basic.Named :=
  Named.mul
    (Named.exact factor) input

/-- The scaled input name minus the exact unit name. -/
def numerator (input : Gaussian.Name.Basic.Named)
  (factor : Canonical) : Gaussian.Name.Basic.Named :=
  Named.sub
    (scaled input factor)
      exactOne

/-- The scaled input name plus the exact unit name. -/
def denominator (input : Gaussian.Name.Basic.Named)
  (factor : Canonical) : Gaussian.Name.Basic.Named :=
  Named.add
    (scaled input factor)
      exactOne

/-- Every possible scaled reading is the factor times a possible reading of the original process at the retained operand
state. -/
theorem scaled_possible (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    {state : (scaled input factor).process.State} {value :
      Canonical}
    (possible : (scaled input factor).process.Possible state value) :
    ∃ source : Canonical,
      input.process.Possible state.2 source ∧ value = factor * source := by
  rcases possible with
    ⟨exactFactor, source, factorPossible, sourcePossible, valueEqual⟩
  change exactFactor = factor at factorPossible
  subst exactFactor
  exact ⟨source, sourcePossible, valueEqual⟩

/-- Every possible numerator reading is the factor times an original possible reading, minus one. -/
theorem numerator_possible (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    {state : (numerator input factor).process.State} {value :
      Canonical}
    (possible : (numerator input factor).process.Possible state value)
      :
    ∃ source : Canonical,
      input.process.Possible state.1.2 source ∧
        value = factor * source - 1 := by
  rcases possible with
    ⟨scaledValue, negativeOne, scaledPossible,
      ⟨oneValue, onePossible, negativeEqual⟩, valueEqual⟩
  rcases scaled_possible input factor scaledPossible with
    ⟨source, sourcePossible, scaledEqual⟩
  change oneValue = (1 : Canonical) at onePossible
  subst oneValue
  rw [negativeEqual, scaledEqual] at valueEqual
  refine ⟨source, sourcePossible, ?_⟩
  rw [valueEqual]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.neg_re,
      Data.Gaussian.Basic.neg_im,
      Data.Gaussian.Basic.sub_re,
      Data.Gaussian.Basic.sub_im] <;> ring1

/-- Every possible denominator reading is the factor times an original possible reading, plus one. -/
theorem denominator_possible (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    {state : (denominator input factor).process.State} {value :
      Canonical}
    (possible : (denominator input factor).process.Possible state
      value) :
    ∃ source : Canonical,
      input.process.Possible state.1.2 source ∧
        value = factor * source + 1 := by
  rcases possible with
    ⟨scaledValue, oneValue, scaledPossible, onePossible, valueEqual⟩
  rcases scaled_possible input factor scaledPossible with
    ⟨source, sourcePossible, scaledEqual⟩
  change oneValue = (1 : Canonical) at onePossible
  subst oneValue
  rw [scaledEqual] at valueEqual
  exact ⟨source, sourcePossible, valueEqual⟩

/-- A lower bound stated only for genuine input candidates supplies the possible-denominator apartness used by chart
preparation. -/
def denominatorPossibleApart (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    (lowerSq : Fraction.Rational) (positive : 0 < lowerSq)
    (lower : ∀ (state : input.process.State) {source : Canonical},
      input.process.Possible state source →
        lowerSq ≤
          Data.Gaussian.Norm.Basic.normSq (factor * source + 1)) :
    Possible.PossibleApart (denominator input factor).process where
  lowerSq := lowerSq
  positive := positive
  lower := by
    intro state value possible
    rcases denominator_possible input factor possible with
      ⟨source, sourcePossible, valueEqual⟩
    rw [valueEqual]
    exact lower state.1.2 sourcePossible

/-- Prepare the scaled-plus-one denominator for whole-ball division using its retained candidate apartness certificate.
-/
def preparedDenominator (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    (apart : Possible.PossibleApart (denominator input factor).process)
      : Gaussian.Name.Basic.Named :=
  { process := Preparation.apartify apart
    state := Preparation.prepareApartState apart
      (denominator input factor).state }

/-- The prepared denominator carries the whole-ball apartness certificate produced by the same preparation. -/
def preparedDenominatorApart (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    (apart : Possible.PossibleApart (denominator input factor).process)
      :
    Named.Apart
      (preparedDenominator input factor apart) where
  certificate := Preparation.apartifyApart apart

/-- Form the reduced logarithm argument by dividing the scaled-minus-one numerator by its apartness-prepared
scaled-plus-one denominator. -/
def reduced (input : Gaussian.Name.Basic.Named) (factor
  : Canonical)
    (apart : Possible.PossibleApart (denominator input factor).process)
      : Gaussian.Name.Basic.Named :=
  Named.div
    (numerator input factor)
      (preparedDenominator input factor apart)
    (preparedDenominatorApart input factor apart)

/-- Every possible reduced reading is a quotient of two independently possible readings at the original input state.

The numerator and denominator retain their respective source witnesses and the exact displayed affine quotient identity.
-/
theorem reduced_possible (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    (apart : Possible.PossibleApart (denominator input factor).process)
    {value : Canonical}
    (possible : (reduced input factor apart).process.Possible
      (reduced input factor apart).state value) :
    ∃ numeratorSource denominatorSource : Canonical,
      input.process.Possible input.state numeratorSource ∧
      input.process.Possible input.state denominatorSource ∧
      value = (factor * numeratorSource - 1) /
        (factor * denominatorSource + 1) := by
  rcases possible with
    ⟨numeratorValue, denominatorValue, numeratorPossible,
      denominatorPossible, valueEqual⟩
  rcases numerator_possible input factor numeratorPossible with
    ⟨numeratorSource, numeratorSourcePossible, numeratorEqual⟩
  have originalDenominatorPossible :
      (denominator input factor).process.Possible
        (denominator input factor).state denominatorValue :=
    Preparation.prepareApartState_persists apart
      (denominator input factor).state denominatorPossible
  rcases denominator_possible input factor originalDenominatorPossible
    with
    ⟨denominatorSource, denominatorSourcePossible, denominatorEqual⟩
  exact ⟨numeratorSource, denominatorSource,
    numeratorSourcePossible, denominatorSourcePossible, by
      rw [valueEqual, numeratorEqual, denominatorEqual]⟩

/-- A square-root-free bound on all independently admitted numerator and denominator candidates constructs the local
reduced-disk certificate. The two candidates may differ because enclosure arithmetic conservatively duplicates a
progressive input. -/
theorem reducedDiskOfBounds (input :
  Gaussian.Name.Basic.Named) (factor : Canonical)
    (apart : Possible.PossibleApart (denominator input factor).process)
    (bound : ∀ {numeratorSource denominatorSource : Canonical},
      input.process.Possible input.state numeratorSource →
      input.process.Possible input.state denominatorSource →
      Data.Gaussian.Norm.Basic.normSq
          ((factor * numeratorSource - 1) /
            (factor * denominatorSource + 1)) ≤ 1 / 9) :
    Domain.Disk (reduced input factor apart) where
  possible_normSq := by
    intro value possible
    rcases reduced_possible input factor apart possible with
      ⟨numeratorSource, denominatorSource, numeratorPossible,
        denominatorPossible, valueEqual⟩
    rw [valueEqual]
    exact bound numeratorPossible denominatorPossible
end Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction

end
