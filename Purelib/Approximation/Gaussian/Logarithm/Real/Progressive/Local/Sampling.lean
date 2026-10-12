module
public import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sampling

/-- Every canonical witness of the certified real logarithm input is real and lies between one half and two. -/
theorem inputWitness_chart {input :
  Named} (chart : Domain.Chart input) (index : Nat) :
    (Log.inputWitness input index).im = 0 ∧
      1 / 2 ≤ (Log.inputWitness input index).re ∧
      (Log.inputWitness input index).re ≤ 2 :=
  chart.possible_real_chart (Log.inputWitness_possible_start input index)

/-- The rational real coordinate of the canonical finite Gaussian input witness. -/
def inputSample (input :
  Named) (index : Nat) : Fraction.Rational :=
  (Log.inputWitness input index).re

/-- The retained real logarithm input sample is at least one half. -/
theorem inputSample_half {input :
  Named} (chart : Domain.Chart input) (index : Nat) :
    1 / 2 ≤ inputSample input index :=
  (inputWitness_chart chart index).2.1

/-- The retained real logarithm input sample is at most two. -/
theorem inputSample_two {input :
  Named} (chart : Domain.Chart input) (index : Nat) :
    inputSample input index ≤ 2 :=
  (inputWitness_chart chart index).2.2

/-- Later real logarithm input samples have squared difference within the earlier index's scale-four quarter-radius
allowance. -/
theorem inputSample_later_close {input :
  Named} (chart : Domain.Chart input)
    {oldIndex newIndex : Nat} (indexOrder : oldIndex ≤ newIndex) :
    (inputSample input newIndex -
      inputSample input oldIndex) ^ 2 ≤
      Geometric.Basic.quarterRadius 4 oldIndex := by
  have movement := Gaussian.Process.Sampling.witnessAt_later_close
    input.process input.state indexOrder
  have newImaginary := (inputWitness_chart chart
    newIndex).1
  have oldImaginary := (inputWitness_chart chart
    oldIndex).1
  have equality :
      Data.Gaussian.Norm.Basic.normSq (Log.inputWitness input newIndex - Log.inputWitness input oldIndex) =
        (inputSample input newIndex -
          inputSample input oldIndex) ^ 2 := by
    rw [Data.Gaussian.Norm.Basic.normSq]
    simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      inputSample, newImaginary, oldImaginary]
    ring1
  rw [← equality]
  exact movement
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Sampling

end
