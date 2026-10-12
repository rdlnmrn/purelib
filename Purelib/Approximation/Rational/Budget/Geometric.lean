module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Init.Data.Nat.Log2
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Basic
import Purelib.Data.Nat.BitWidth
import Purelib.Algebra.NatCast

/-!
# Explicit finite geometric search

This neutral utility turns a positive rational tolerance into a finite index
at which a displayed quarter-power allowance is small enough.  Termination
uses a coefficient-computed binary-length fuel certificate, not a limit or an
Archimedean existence theorem.
-/

namespace Purelib.Approximation.Geometric

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding

public section

/-- Rational allowance with quarter-power decay.

The supplied scale is divided by the displayed power of four at the retained natural stage. -/
@[expose] def quarterAllowance (scale : Fraction.Rational) (index : Nat) : Fraction.Rational :=
  scale / (4 : Fraction.Rational) ^ index

/-- Express the quarter allowance as its scale times the corresponding quarter-power.

The same allowance is expressed using the reciprocal power of four. No scale or stage is replaced. -/
theorem quarterAllowance_eq_mul_pow (scale : Fraction.Rational) (index : Nat) :
    Geometric.quarterAllowance scale index =
      scale * (1 / 4 : Fraction.Rational) ^ index := by
  rw [Geometric.quarterAllowance, Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.inv_pow_direct,
    Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.one_mul]

/-- A nonnegative scale gives a nonnegative allowance at every stage.

The denominator is a nonnegative power of four, and the supplied numerator is nonnegative. -/
theorem quarterAllowance_nonneg {scale : Fraction.Rational}
    (nonnegative : 0 ≤ scale) (index : Nat) :
    0 ≤ Geometric.quarterAllowance scale index :=
  Fraction.Order.Field.div_nonneg_direct nonnegative
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index)

/-- A positive scale gives a positive allowance at every stage.

The denominator is a positive power of four. The supplied positive scale gives a strictly positive quotient. -/
theorem quarterAllowance_pos {scale : Fraction.Rational} (positive : 0 < scale)
    (index : Nat) : 0 < Geometric.quarterAllowance scale index :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.pow_pos_direct (by decide) index)

/-- The explicit scan endpoint is below the requested allowance.

The binary width of the rational ceiling bounds the required power of two. Comparing it with the displayed power of four
controls the same terminal stage. -/
theorem terminal_quarterAllowance_lt {scale target : Fraction.Rational}
    (scaleNonnegative : 0 ≤ scale) (targetPositive : 0 < target)
    (current : Nat) :
    Geometric.quarterAllowance scale
        (current +
          (Nat.log2 (Floor.ceilNat (scale / target)) + 1)) <
      target := by
  let quotient : Fraction.Rational := scale / target
  let ceiling : Nat := Floor.ceilNat quotient
  let fuel : Nat := Nat.log2 ceiling + 1
  let exponent : Nat := current + fuel
  have quotientNonnegative : 0 ≤ quotient :=
    Fraction.Order.Field.div_nonneg_direct scaleNonnegative
      targetPositive.le
  have quotientLe : quotient ≤ (ceiling : Fraction.Rational) :=
    Floor.le_natCast_ceilNat_of_nonneg quotientNonnegative
  have ceilingLtTwoPowNat : ceiling < 2 ^ fuel := by
    exact BitWidth.lt_two_pow_natWidth ceiling
  have ceilingLtTwoPow : (ceiling : Fraction.Rational) <
      (2 : Fraction.Rational) ^ fuel := by
    have castBound := Fraction.Cast.Order.natCast_lt_direct
      ceilingLtTwoPowNat
    simpa only [NatCast.pow, Nat.cast_ofNat] using castBound
  have quotientLtTwoPow : quotient < (2 : Fraction.Rational) ^ fuel :=
    quotientLe.trans_lt ceilingLtTwoPow
  have fuelLeExponent : fuel ≤ exponent := by
    dsimp only [exponent]
    omega
  have twoPowMonotone : (2 : Fraction.Rational) ^ fuel ≤
      (2 : Fraction.Rational) ^ exponent := by
    have naturalBound : 2 ^ fuel ≤ 2 ^ exponent :=
      Nat.pow_le_pow_right (by decide) fuelLeExponent
    have castBound := Fraction.Cast.Order.natCast_le_direct naturalBound
    simpa only [NatCast.pow, Nat.cast_ofNat] using castBound
  have twoPowLeFourPow : (2 : Fraction.Rational) ^ exponent ≤
      (4 : Fraction.Rational) ^ exponent :=
    Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) (by decide) exponent
  have quotientLtPower : quotient < (4 : Fraction.Rational) ^ exponent :=
    quotientLtTwoPow.trans_le (twoPowMonotone.trans twoPowLeFourPow)
  have powerPositive : 0 < (4 : Fraction.Rational) ^ exponent :=
    Fraction.Order.Arithmetic.pow_pos_direct (by decide) exponent
  have scaled : scale < (4 : Fraction.Rational) ^ exponent * target :=
    (Fraction.Order.Field.div_lt_iff_pos targetPositive).mp
      quotientLtPower
  change scale / (4 : Fraction.Rational) ^ exponent < target
  apply (Fraction.Order.Field.div_lt_iff_pos powerPositive).mpr
  simpa only [Fraction.Field.mul_comm] using scaled

/-- Pure bounded scan for the first successful rational comparison.

The computation retains the current stage and remaining fuel. It stops at the first successful comparison or at the
displayed terminal stage. -/
@[expose] def scanFirstBelow (scale target : Fraction.Rational) : Nat → Nat → Nat
  | current, 0 => current
  | current, fuel + 1 =>
      if Geometric.quarterAllowance scale current < target then current
      else Geometric.scanFirstBelow scale target (current + 1) fuel

/-- The bounded scan never returns an index before its starting index.

A failed comparison increments the current stage. A successful comparison or exhausted fuel returns that same stage. -/
theorem scanFirstBelow_ge (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      current ≤ Geometric.scanFirstBelow scale target current fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [Geometric.scanFirstBelow]
      split
      · exact Nat.le_refl current
      · exact (Nat.le_succ current).trans
          (Geometric.scanFirstBelow_ge scale target (current + 1) fuel)

/-- The bounded scan returns an index at most its start plus its available fuel.

Every failed comparison spends one unit of fuel on a successor stage, preserving the upper bound by starting stage plus
fuel. -/
theorem scanFirstBelow_le_add (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      Geometric.scanFirstBelow scale target current fuel ≤ current + fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [Geometric.scanFirstBelow]
      split
      · omega
      · have bound := Geometric.scanFirstBelow_le_add scale target (current + 1) fuel
        omega

/-- If the scan's finite terminal index meets the target, its returned index also meets it.

A successful comparison supplies the bound directly. A failed comparison passes the same terminal-stage certificate to
the scan with preceding fuel. -/
theorem scanFirstBelow_accurate (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      Geometric.quarterAllowance scale (current + fuel) < target →
        Geometric.quarterAllowance scale
          (Geometric.scanFirstBelow scale target current fuel) < target
  | current, 0, terminal => by
      simpa only [Nat.add_zero, Geometric.scanFirstBelow] using terminal
  | current, fuel + 1, terminal => by
      rw [Geometric.scanFirstBelow]
      split
      · assumption
      · apply Geometric.scanFirstBelow_accurate scale target (current + 1) fuel
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using terminal

/-- Transparently computed successful index with finite binary-length fuel.

The original logarithm of the rational ceiling plus one supplies the scan fuel, retaining the same scale, target and
starting stage. -/
@[expose] def firstQuarterBelow (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) : Nat :=
  Geometric.scanFirstBelow scale target current
    (Nat.log2 (Floor.ceilNat (scale / target)) + 1)

/-- The computed successful index is no earlier than the requested starting index.

The lower bound applies to the same scan with its computed binary-width fuel. -/
theorem firstQuarterBelow_ge (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) :
    current ≤ Geometric.firstQuarterBelow scale current target :=
  Geometric.scanFirstBelow_ge scale target current _

/-- The computed index stays within the explicit binary-length fuel bound.

The finite upper bound is the starting stage plus the original logarithm-derived fuel. -/
theorem firstQuarterBelow_le (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) :
    Geometric.firstQuarterBelow scale current target ≤
      current +
        (Nat.log2 (Floor.ceilNat (scale / target)) + 1) :=
  Geometric.scanFirstBelow_le_add scale target current _

/-- For a nonnegative scale and positive target, the computed index has allowance strictly below the target.

The explicit endpoint certificate supplies accuracy to the same bounded scan without changing its successful comparison
or returned stage. -/
theorem firstQuarterBelow_accurate (scale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ scale) (current : Nat) (target : Fraction.Rational)
    (targetPositive : 0 < target) :
    Geometric.quarterAllowance scale (Geometric.firstQuarterBelow scale current target) < target := by
  apply Geometric.scanFirstBelow_accurate scale target current
  exact Geometric.terminal_quarterAllowance_lt scaleNonnegative targetPositive current

end

end Purelib.Approximation.Geometric
