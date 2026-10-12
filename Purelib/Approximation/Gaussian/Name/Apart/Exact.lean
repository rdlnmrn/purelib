module
public import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Apartness of exact Gaussian names

A nonzero Gaussian rational gives an exact name with a positive squared-norm
floor. Every point in its radius-zero observation ball equals that value.
-/

namespace Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

/-- Certify apartness of the exact name of a nonzero Gaussian rational.

The certificate retains the value's positive squared norm as its lower floor.
Each candidate in the radius-zero observation ball equals the displayed value,
so the same floor bounds every observation state. -/
@[expose] public def exactApart (value : Data.Gaussian.Basic.Canonical)
    (nonzero : value ≠ 0) :
    Named.Apart
      (Coherence.exact value).name where
  certificate :=
    { lowerSq := Data.Gaussian.Norm.Basic.normSq value
      positive := Data.Gaussian.Norm.Basic.normSq_pos nonzero
      lower := by
        intro state candidate inside
        change Data.Gaussian.Norm.Basic.normSq
          (candidate - value) <= 0 at inside
        have normZero : Data.Gaussian.Norm.Basic.normSq
            (candidate - value) = 0 :=
          le_antisymm inside
            (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        have differenceZero :=
          Data.Gaussian.Norm.Basic.normSq_eq_zero.mp normZero
        have equal : candidate = value := Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero differenceZero
        rw [equal] }

end Purelib.Approximation.Gaussian.Name.Apart.Exact
