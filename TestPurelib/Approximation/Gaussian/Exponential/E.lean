module

import Purelib.Examples.Approximation.Gaussian.Exponential.E
import Purelib.Approximation.Gaussian.Exponential.E.Presentation
public meta import Purelib.Examples.Approximation.Gaussian.Exponential.E
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

namespace TestPurelib.Approximation.Gaussian.Exponential.E

open Purelib.Approximation.Gaussian.Exponential
open Purelib.Examples.Approximation.Gaussian.Exponential
open Purelib.Data.Gaussian

example (index : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq (E.exactOneSamples.value index) ≤ 1 :=
  E.exactOneSamples_unit index

example {earlier later : Nat} (order : earlier ≤ later) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
        (E.exactOneSamples.value later - E.exactOneSamples.value earlier) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 4 earlier :=
  E.exactOneSamples_close order

example : E.exactOneSamples.value 2 = (1 : Basic.Canonical) := by decide

example : Taylor.Basic.truncatedExp 1 0 = (1 : Basic.Canonical) := rfl

example : Taylor.Basic.truncatedExp 1 1 = (2 : Basic.Canonical) := by decide

example : E.factorialSample 0 = (2 : Basic.Canonical) := by decide

example : E.factorialSample 1 = (⟨5 / 2, 0⟩ : Basic.Canonical) := by decide

example : E.factorialSample 2 = (⟨8 / 3, 0⟩ : Basic.Canonical) := by decide

example (index : Nat) : E.hornerApproximation.sample index = E.factorialSample index :=
  E.horner_sample_eq_factorial index

example (index : Nat) :
    (E.horner.name.process.ball (show E.horner.name.process.State from index)).center =
      Horner.Basic.step 1 1 (Horner.Basic.horner 1 2 index) :=
  E.horner_name_center index

example (current : Nat) (target : Purelib.Data.Rat.Fraction.Rational)
    (positive : 0 < target) :
    current ≤ E.hornerApproximation.refineIndex current target positive ∧
      E.hornerApproximation.radiusSq (E.hornerApproximation.refineIndex current target positive) < target :=
  ⟨E.horner_refine_ge current target positive, E.horner_refine_accurate current target positive⟩

example : E.hornerApproximation.refineIndex 7 4 (by decide) = 7 := by decide

example : (E.horner.name.process.ball E.horner.name.state).center = (2 : Basic.Canonical) := by decide

example (index : Nat) :
    E.factorialApproximation.sample index = Taylor.Basic.truncatedExp 1 (index + 1) :=
  E.factorial_sample_readback index

example (current : Nat) (target : Purelib.Data.Rat.Fraction.Rational)
    (positive : 0 < target) :
    E.factorialApproximation.refineIndex current target positive =
      Purelib.Approximation.Rational.Geometric.Search.firstQuarterBelow 10 current target :=
  E.factorial_refine_readback current target positive

example : 3 ≤ E.comparison.leftIndex := E.comparison.left_ge

example : 7 ≤ E.comparison.rightIndex := E.comparison.right_ge

#eval (E.comparison.leftIndex, E.comparison.rightIndex)

end TestPurelib.Approximation.Gaussian.Exponential.E
