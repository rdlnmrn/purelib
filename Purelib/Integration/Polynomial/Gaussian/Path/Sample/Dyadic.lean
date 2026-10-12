module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Sample.Bounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Norm bounds for actual finite path samples

Uniform coefficient bounds are paid with the actual squared displacement.
On a dyadic side, the full squared cell count cancels its displacement scale;
the resulting norm bound does not grow with the refinement depth.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Sample.Dyadic

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Original dyadic cell sample bounds give a path-sample bound by density times movement.

The retained equality between cell count and two to the original depth cancels the quarter-radius count factors exactly.
-/
theorem dyadic_integral_norm_le (path :
  Basic.PathModel) (depth : Nat)
    (count : path.cells.length = 2 ^ depth) (movement density : Fraction.Rational)
    (bounded : ∀ cell ∈ path.cells,
      Data.Gaussian.Norm.Basic.normSq cell.integralSample ≤ density * Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq path.integralSample ≤ density * movement := by
  have estimate := Sample.Bounds.integral_norm_le_uniform path _ bounded
  rw [count] at estimate
  apply estimate.trans_eq
  calc
    _ = density * (((2 ^ depth : Nat) : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = density * movement := by rw [Geometric.DyadicCount.dyadic_count_cancel]

end Purelib.Integration.Polynomial.Gaussian.Path.Sample.Dyadic

end
