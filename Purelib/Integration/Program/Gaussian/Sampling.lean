module
public import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Sequence.Sampling
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

namespace Purelib.Integration.Program.Gaussian.Basic

public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace RefinementProgram

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Program in
/-- Bound the original program's process-selected sample against its sample at the same requested index.

The common quarter-radius scale is the maximum of the original error scale and one, retaining the exact process state
selected by the sampling procedure. -/
theorem witness_sample_close (program :
  Gaussian.Basic.RefinementProgram) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (program.approximation.sample
            (Process.Sampling.stateAt program.approximation.toProcess (0 : Nat) index) -
          program.approximation.sample index) <=
      Geometric.Basic.quarterRadius (max program.errorScale 1) index := by
  have close := program.approximation.witness_sample_close index
  have bound : max (Geometric.Basic.quarterRadius program.errorScale index)
      (Geometric.Basic.quarterRadius 1 index) <=
      Geometric.Basic.quarterRadius (max program.errorScale 1) index := by
    rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
      Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Purelib.Data.Rat.Fraction.Order.Basic.max_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _
        _)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _
        _)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index))
  exact close.trans bound
end RefinementProgram

end

end Purelib.Integration.Program.Gaussian.Basic
