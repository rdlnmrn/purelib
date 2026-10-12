module
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat

open Purelib.Algebra

section
@[expose] public section

/-!
# Generated sample certificates for the quartic A-backward connector

This module identifies the 64 canonical centred edges of the explicit
A-backward horizontal path with the independently generated rational root
and sample data.  The reversed stationary prefix is handled separately as a
zero-displacement path.
-/

namespace Purelib.LinearAlgebra.Rational.FiniteSum.Small

/-- Eight times the sum of eight copies of 1/65536 equals 1/1024.

The equality is exact in the constructive rational field. -/
theorem aBackwardOneOver65536CellBudget :
    (8 : Fraction.Rational) * FiniteSum.Fin.sumFin
        (fun _ : Fin 8 => (1 / 65536 : Fraction.Rational)) =
      (1 / 1024 : Fraction.Rational) := open Purelib.Data.Rat.Fraction in by
  have summed : FiniteSum.Fin.sumFin
      (fun _ : Fin 8 => (1 / 65536 : Fraction.Rational)) = 8 / 65536 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    rw [show FiniteSum.Fin.sumFin
        (fun _ : Fin 0 => (1 / 65536 : Fraction.Rational)) = 0 by rfl]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [summed]
  calc
    (8 : Fraction.Rational) * (8 / 65536) = 64 / 65536 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 1 / 1024 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 65536)).ne'
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 1024)).ne'
      ring1

/-- Eight times the sum of eight copies of 1/1024 equals 1/16.

The equality is exact in the constructive rational field. -/
theorem aBackwardOneOver1024ConnectorBudget :
    (8 : Fraction.Rational) * FiniteSum.Fin.sumFin
        (fun _ : Fin 8 => (1 / 1024 : Fraction.Rational)) =
      (1 / 16 : Fraction.Rational) := open Purelib.Data.Rat.Fraction in by
  have summed : FiniteSum.Fin.sumFin
      (fun _ : Fin 8 => (1 / 1024 : Fraction.Rational)) = 8 / 1024 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    rw [show FiniteSum.Fin.sumFin
        (fun _ : Fin 0 => (1 / 1024 : Fraction.Rational)) = 0 by rfl]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [summed]
  calc
    (8 : Fraction.Rational) * (8 / 1024) = 64 / 1024 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 1 / 16 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 1024)).ne'
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 16)).ne'
      ring1
end Purelib.LinearAlgebra.Rational.FiniteSum.Small

end

section
@[expose] public section

/-!
# Aggregate A-backward quartic sample certificates

This module identifies the explicit 64-edge A-backward sample table with the
canonical centres stored by the completed prepared path.
-/

namespace Purelib.LinearAlgebra.Rational.FiniteSum.Small

/-- Eight times the sum of eight copies of 1/1048576 equals 1/16384.

The equality is exact in the constructive rational field. -/
theorem aBackwardRoundingConnectorBudget :
    (8 : Fraction.Rational) * FiniteSum.Fin.sumFin
        (fun _ : Fin 8 => (1 / 1048576 : Fraction.Rational)) =
      (1 / 16384 : Fraction.Rational) := open Purelib.Data.Rat.Fraction in by
  have summed : FiniteSum.Fin.sumFin
      (fun _ : Fin 8 => (1 / 1048576 : Fraction.Rational)) = 8 / 1048576 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    rw [show FiniteSum.Fin.sumFin
        (fun _ : Fin 0 => (1 / 1048576 : Fraction.Rational)) = 0 by rfl]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [summed]
  calc
    (8 : Fraction.Rational) * (8 / 1048576) = 64 / 1048576 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 1 / 16384 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 1048576)).ne'
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 16384)).ne'
      ring1
end Purelib.LinearAlgebra.Rational.FiniteSum.Small

end

section
@[expose] public section

/-!
# Aggregate horizontal quartic sample certificates

This module connects the exact rational samples emitted by the standalone
Python generator to the 64 canonical centered edges of the prepared
A-forward horizontal connector, then aggregates the local error bounds by
finite Cauchy--Schwarz.
-/

namespace Purelib.LinearAlgebra.Rational.FiniteSum.Small

/-- Eight times the sum of eight copies of 3/65536 equals 3/1024.

The equality is exact in the constructive rational field. -/
theorem horizontalThreeOver65536CellBudget :
    (8 : Fraction.Rational) * FiniteSum.Fin.sumFin
        (fun _ : Fin 8 => (3 / 65536 : Fraction.Rational)) =
      (3 / 1024 : Fraction.Rational) := open Purelib.Data.Rat.Fraction in by
  have summed : FiniteSum.Fin.sumFin
      (fun _ : Fin 8 => (3 / 65536 : Fraction.Rational)) = 24 / 65536 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    rw [show FiniteSum.Fin.sumFin
        (fun _ : Fin 0 => (3 / 65536 : Fraction.Rational)) = 0 by rfl]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [summed]
  calc
    (8 : Fraction.Rational) * (24 / 65536) = 192 / 65536 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 3 / 1024 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 65536)).ne'
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 1024)).ne'
      ring1

/-- Eight times the sum of eight copies of 3/1024 equals 3/16.

The equality is exact in the constructive rational field. -/
theorem horizontalThreeOver1024ConnectorBudget :
    (8 : Fraction.Rational) * FiniteSum.Fin.sumFin
        (fun _ : Fin 8 => (3 / 1024 : Fraction.Rational)) =
      (3 / 16 : Fraction.Rational) := open Purelib.Data.Rat.Fraction in by
  have summed : FiniteSum.Fin.sumFin
      (fun _ : Fin 8 => (3 / 1024 : Fraction.Rational)) = 24 / 1024 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    rw [show FiniteSum.Fin.sumFin
        (fun _ : Fin 0 => (3 / 1024 : Fraction.Rational)) = 0 by rfl]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [summed]
  calc
    (8 : Fraction.Rational) * (24 / 1024) = 192 / 1024 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 3 / 16 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 1024)).ne'
        (Cast.Order.natCast_pos_direct
          (by omega : 0 < 16)).ne'
      ring1
end Purelib.LinearAlgebra.Rational.FiniteSum.Small

end

section
@[expose] public section

/-!
# Worked finite hyperelliptic period examples

This module records explicit squarefree cyclic curves for the worked examples
of the finite period theorem.  Every polynomial is the concrete finite dense
power polynomial `Z^d - 1`.  Its nonzeroness, degree, and displayed Bézout
identity are proved by the finite power-monodromy algebra, so the examples
introduce no separate squarefreeness assumption.

The five nontrivial examples are

* `y² = x³ - 1` and `y² = x⁴ - 1` in genus one;
* `y² = x⁵ - 1` and `y² = x⁶ - 1` in genus two;
* `y² = x⁷ - 1` in genus three.

Two genus-zero controls, `y² = x - 1` and `y² = x² - 1`, exercise the
complete unconditional theorem and its genuinely empty period matrix.

The topology statements below compute the classical Euler characteristics
`0`, `-2`, and `-4` and expose the expected symplectic intersection basis.
The analytic period conclusions use the unconditional public theorem on
these same curves. The separate exact matrix examples below are algebraic
models, not period-program evaluations.
-/

namespace Purelib.LinearAlgebra.Rational.FiniteSum.Small

/-- A rational family indexed by `Fin 0` has sum zero. -/
theorem exact_sumFin_fin_zero (values : Fin 0 ->
  Fraction.Rational) :
    FiniteSum.Fin.sumFin values = 0 := rfl

open Purelib in
/-- A two-entry rational sum is the sum of entries zero and one. -/
theorem exact_sumFin_fin_two (values : Fin 2 -> Fraction.Rational)
  :
    FiniteSum.Fin.sumFin values = values 0 + values 1 := by
  rw [FiniteSum.Fin.sumFin_succ]
  rw [FiniteSum.Fin.sumFin_succ]
  change values 0 +
      (values 1 + FiniteSum.Fin.sumFin (fun index : Fin 0 =>
        values index.succ.succ)) = _
  rw [exact_sumFin_fin_zero, _root_.add_zero]

end Purelib.LinearAlgebra.Rational.FiniteSum.Small

end
