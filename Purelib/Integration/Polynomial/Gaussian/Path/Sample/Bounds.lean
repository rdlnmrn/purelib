module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Norm bounds for actual finite path samples

Uniform coefficient bounds are paid with the actual squared displacement.
On a dyadic side, the full squared cell count cancels its displacement scale;
the resulting norm bound does not grow with the refinement depth.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Sample.Bounds

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The zero primitive has zero total increment over the original cell list. -/
private theorem zero_increments (cells : List
  Basic.CellModel) :
    Primitive.incrementSum (fun _ => 0) cells = 0 := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      change 0 - 0 + Primitive.incrementSum (fun _ => 0) cells = 0
      rw [ih]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Uniform original cell sample bounds control the path sample by the square of its retained cell count.

The estimate uses the exact original path cells and their individual squared-norm certificates. -/
theorem integral_norm_le_uniform (path :
  Basic.PathModel) (bound : Fraction.Rational)
    (bounded : ∀ cell ∈ path.cells, Data.Gaussian.Norm.Basic.normSq cell.integralSample ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq path.integralSample ≤ (path.cells.length : Fraction.Rational) * ((path.cells.length
      :
      Fraction.Rational) * bound) := by
  have telescopes : Primitive.incrementSum (fun _ => 0) path.cells =
      (0 : Basic.Canonical) - 0 := by rw [zero_increments]; ring1
  have estimate := Primitive.integral_error_le_uniform (fun _ => 0) path
    (start := 0) (finish := 0) telescopes bound (fun cell member => by
      simpa only [Norm.Basic.normSq_eq_canonical, sub_self, zero_sub, Basic.Canonical.normSq_neg] using bounded cell
        member)
  simpa only [Norm.Basic.normSq_eq_canonical, sub_self, zero_sub, Basic.Canonical.normSq_neg] using estimate
end Purelib.Integration.Polynomial.Gaussian.Path.Sample.Bounds

end
