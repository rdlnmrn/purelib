module

public import Purelib.Approximation.Gaussian.Exponential.E
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling
public import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Rational.Geometric.Search

namespace Purelib.Approximation.Gaussian.Exponential.E

open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation
open Purelib.Data.Rat

public section

/-- The original unit-disk samples used by the local exponential at exact one.

The retained value procedure samples `Named.exact 1` through its original
process. Its unit and all-later movement proofs are the certificates supplied
by `Local.Sampling.unitDiskSamples`; this does not decide equality of arbitrary
sample functions or check an independently supplied proof presentation. -/
@[expose] def exactOneSamples : Gaussian.Sequence.UnitDisk.UnitDiskSamples :=
  Progressive.Local.Sampling.unitDiskSamples
    (Gaussian.Name.Basic.Named.exact 1)
    (Gaussian.Name.UnitDisk.exact 1 one_unit)

/-- Each exact-one input sample carries the original unit-disk certificate. -/
theorem exactOneSamples_unit (index : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq (exactOneSamples.value index) ≤ 1 :=
  exactOneSamples.unit index

/-- The original certificate bounds movement between all ordered sample stages. -/
theorem exactOneSamples_close {earlier later : Nat} (order : earlier ≤ later) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
        (exactOneSamples.value later - exactOneSamples.value earlier) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 4 earlier :=
  exactOneSamples.close order

/-- A stock e sample executes the original finite Horner recurrence at one.

The outer denominator-one step retains an inner tail beginning at denominator
two. The tail uses structural recursion on the supplied finite depth. -/
theorem horner_sample_readback (index : Nat) :
    hornerApproximation.sample index =
      Horner.Basic.step 1 1 (Horner.Basic.horner 1 2 index) := rfl

/-- The stock name's finite process ball retains the original Horner sample.

The sequence-backed process uses the supplied natural index as its state; its
center is computed by the same retained evaluator. -/
theorem horner_name_center (index : Nat) :
    (horner.name.process.ball (show horner.name.process.State from index)).center =
      Horner.Basic.step 1 1 (Horner.Basic.horner 1 2 index) := rfl

/-- The stock Horner refinement runs the original bounded quarter-radius selector. -/
theorem horner_refine_readback (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    hornerApproximation.refineIndex current target positive =
      Search.firstQuarterBelow 10 current target := rfl

/-- The stock refinement respects its supplied starting stage. -/
theorem horner_refine_ge (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    current ≤ hornerApproximation.refineIndex current target positive :=
  hornerApproximation.refineIndex_ge current target positive

/-- The stock refinement's squared allowance is strictly below the positive request. -/
theorem horner_refine_accurate (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    hornerApproximation.radiusSq (hornerApproximation.refineIndex current target positive) < target :=
  hornerApproximation.refineIndex_accurate current target positive

/-- The stock selector returns within its finite logarithmic scan fuel. -/
theorem horner_refine_le (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    hornerApproximation.refineIndex current target positive ≤
      current + (Nat.log2 (Purelib.Data.Rat.Rounding.Floor.ceilNat (10 / target)) + 1) :=
  Search.firstQuarterBelow_le 10 current target

/-- The factorial approximation executes the Taylor recurrence at one and degree `index + 1`.

This is a pointwise readback of the original approximation's sample field. -/
theorem factorial_sample_readback (index : Nat) :
    factorialApproximation.sample index = Taylor.Basic.truncatedExp 1 (index + 1) := rfl

/-- The factorial approximation retains the original bounded quarter-radius selector.

The selector receives scale ten, the supplied starting index and target. The
positivity proof is required by the approximation interface, but is not a
computational argument to the underlying finite search. -/
theorem factorial_refine_readback (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    factorialApproximation.refineIndex current target positive =
      Search.firstQuarterBelow 10 current target := rfl

/-- The factorial approximation's returned stage has the original finite scan bound.

The bound uses the same target and stage as the actual retained selector, whose
fuel is the binary width of the ceiling of `10 / target`. -/
theorem factorial_refine_le (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    factorialApproximation.refineIndex current target positive ≤
      current + (Nat.log2 (Purelib.Data.Rat.Rounding.Floor.ceilNat (10 / target)) + 1) :=
  Search.firstQuarterBelow_le 10 current target

end
end Purelib.Approximation.Gaussian.Exponential.E
