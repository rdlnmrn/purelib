module
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-! A geometric fragment capacity gives a conservative local tolerance before sampling. -/
namespace Purelib.Integration.Budget.Path.Capacity

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- Increasing the retained count capacity decreases the fragment-local tolerance for nonnegative original bound and
target.

The exact denominator comparison retains the squared-count and fourth-power terms and their original coefficients. -/
theorem fragmentLocalTolerance_count_antitone {count capacity : Nat} {bound target : InverseRootPolynomial.Coordinate}
    (countLe : count ≤ capacity) (boundNN : 0 ≤ bound) (targetNN : 0 ≤ target) :
    PairedFragmentBlocks.fragmentLocalTolerance capacity bound target ≤ PairedFragmentBlocks.fragmentLocalTolerance
      count bound target := by
  have countNN : 0 ≤ (count : InverseRootPolynomial.Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    count)
  have castLe : (count : InverseRootPolynomial.Coordinate) ≤ (capacity : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct countLe
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct countNN castLe 2
  have fourth := Fraction.Order.Arithmetic.pow_le_pow_direct countNN castLe 4
  have cross := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct fourth (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 16)) boundNN
  have denominatorLe := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct squares
      cross) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
    (le_refl (1 : InverseRootPolynomial.Coordinate))
  have costNN : 0 ≤ 2 * ((count : InverseRootPolynomial.Coordinate)^2 + 16 * (count :
    InverseRootPolynomial.Coordinate)^4 * bound) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.pow_nonneg_direct countNN 4)) boundNN))
  exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct targetNN
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct costNN (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 1)) denominatorLe

end Purelib.Integration.Budget.Path.Capacity
