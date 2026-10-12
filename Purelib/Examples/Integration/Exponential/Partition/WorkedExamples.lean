module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Integration.Exponential.Cached
import Purelib.Integration.Partition.QuadraticWeight
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic

@[expose] public section

/-!
# Finite exponential integration regressions

These are small kernel calculations at ordinary Lean limits.  In particular,
the unequal-width example witnesses why a progressive constructor must select
its degree using the actual geometric amplification, not assume it is one.
-/

namespace Purelib.Examples.Integration.Exponential.Partition.WorkedExamples

open Purelib.Integration.Partition

open Purelib.Approximation
open Purelib.Integration
open Purelib.Examples

/-- The unit interval partition with no interior cuts. -/
def whole : Unit.Normalized := Unit.Normalized.ofRequest []
/-- The unit interval partition cut at one half. -/
def halves : Unit.Normalized := Unit.Normalized.ofRequest [1 / 2]
/-- The unit interval partition cut at one third and two thirds. -/
def thirds : Unit.Normalized := Unit.Normalized.ofRequest [1 / 3, 2 / 3]
/-- The unequal-width unit interval partition cut at one third. -/
def uneven : Unit.Normalized := Unit.Normalized.ofRequest [1 / 3]

/-- The single-cell partition has quadratic-weight amplification one. -/
theorem whole_amplification : Partition.QuadraticWeight.amplification
  whole = 1 := by decide
/-- The equal-halves partition has quadratic-weight amplification one. -/
theorem halves_amplification : Partition.QuadraticWeight.amplification
  halves = 1 := by decide
/-- The equal-thirds partition has quadratic-weight amplification one. -/
theorem thirds_amplification : Partition.QuadraticWeight.amplification
  thirds = 1 := by decide
/-- The unequal one-third partition has quadratic-weight amplification ten ninths. -/
theorem uneven_amplification : Partition.QuadraticWeight.amplification
  uneven = 10 / 9 := by decide

/-- The first retained exponential polynomial has coefficients [1,1]. -/
theorem first_polynomial_coefficients :
    (Gaussian.Exponential.Taylor.Integral.polynomial 0).coefficients = [1, 1] := by decide

/-- The next retained exponential polynomial has coefficients [1,1,1/2]. -/
theorem next_polynomial_coefficients :
    (Gaussian.Exponential.Taylor.Integral.polynomial 1).coefficients = [1, 1, ⟨1 / 2, 0⟩] := by decide

/-- The coarse retained exponential integral on the unequal partition is three halves. -/
theorem first_integral : (Exponential.Cached.compile 0 uneven 0).sample
  = ⟨3 / 2, 0⟩ := by
  rw [Exponential.Cached.compile_sample]
  decide

/-- The next retained exponential integral on the equal-halves partition is five thirds. -/
theorem next_integral : (Exponential.Cached.compile 1 halves 0).sample
  = ⟨5 / 3, 0⟩ := by
  rw [Exponential.Cached.compile_sample]
  decide

/-- The displayed coarse and next exponential integral samples differ. -/
theorem coarse_samples_differ : (Exponential.Cached.compile 0 uneven
  0).sample ≠ (Exponential.Cached.compile 1 halves 0).sample := by
  rw [first_integral,
    next_integral]
  decide

/-- The path really contains affine restrictions of `1+t`, not a cell
containing the desired integral as a constant polynomial. -/
theorem restricted_coefficients :
    (Exponential.Cached.compile 0 uneven 0).model.cells.map (fun model
      => model.polynomial.coefficients) =
      [[1, ⟨1 / 3, 0⟩], [⟨4 / 3, 0⟩, ⟨2 / 3, 0⟩]] := by decide

/-- The affine restricted cells have exact integrals seven eighteenths and ten ninths. -/
theorem restricted_cell_integrals :
    (Exponential.Cached.compile 0 uneven 0).model.cells.map
      Polynomial.Gaussian.Cell.Basic.CellModel.integralSample =
      [⟨7 / 18, 0⟩, ⟨10 / 9, 0⟩] := by decide

/-- Both endpoints display genuinely later polynomial readings. -/
theorem actual_later_readings :
    (Exponential.Cached.compile 0 uneven 0).model.cells.map (fun model
      =>
      model.observations.map (fun observation => observation.integrandReading)) =
        [[1, ⟨25 / 18, 0⟩], [⟨25 / 18, 0⟩, ⟨5 / 2, 0⟩]] := by decide

/-- The coarse unequal-partition allowance exceeds the specified quarter-radius request. -/
theorem uneven_coarse_allowance_too_large :
    Rational.Geometric.Basic.quarterRadius 10 0 < (Exponential.Cached.compile 0
      uneven 0).allowance := by
  rw [Exponential.Cached.compile_allowance, uneven_amplification]
  decide

/-- The next unequal-partition allowance meets the specified quarter-radius request. -/
theorem deeper_allowance_suffices :
    (Exponential.Cached.compile 1 uneven 0).allowance <
      Rational.Geometric.Basic.quarterRadius 10 0 := by
  rw [Exponential.Cached.compile_allowance, uneven_amplification]
  decide

/-- Every cached exponential sample is the actual integral readback of its retained cell model. -/
theorem retained_sample_is_actual_integral (depth : Nat) (partition : Unit.Normalized)
  (extraDepth : Nat)
  :
    (Exponential.Cached.compile depth partition extraDepth).sample = (Exponential.Cached.compile depth partition
      extraDepth).model.integralSample :=
  (Exponential.Cached.compile depth partition extraDepth).sample_eq

/-- Every compiled exponential integration cell retains two endpoint observations. -/
theorem all_cells_have_observations (depth : Nat) (partition : Unit.Normalized) (extraDepth :
  Nat) :
    ∀ model ∈ (Exponential.Cached.compile depth partition extraDepth).model.cells, model.observations.length = 2 :=
  Exponential.Cached.compile_observations depth partition extraDepth

end Purelib.Examples.Integration.Exponential.Partition.WorkedExamples

end
