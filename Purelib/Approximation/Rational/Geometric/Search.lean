module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Init.Data.Nat.Log2
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Basic
import Purelib.Data.Nat.BitWidth
import Purelib.Algebra.NatCast

/-!
# Explicit finite geometric refinement

This module turns a positive rational accuracy request into a finite natural
index at which a displayed quarter-power allowance is small enough.  The
search has a coefficient-computed finite fuel certificate.  It stops at the
first successful comparison, and neither its definition nor its proof refers
to a limit, an infinite sequence as an object, or an Archimedean existence
principle.
-/

public section

namespace Purelib.Approximation.Rational.Geometric.Search

open Purelib.Approximation.Rational
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Rounding
open Purelib.Algebra

/-- The endpoint computed from a nonnegative scale and positive target has quarter-radius strictly below the target.

The binary width of the rational ceiling bounds the required power of two. Its
comparison with the displayed power of four controls the same terminal stage. -/
public theorem terminal_quarterRadius_lt {scale target : Fraction.Rational}
    (scaleNonnegative : 0 ≤ scale) (targetPositive : 0 < target)
    (current : Nat) :
    Geometric.Basic.quarterRadius scale
        (current +
          (Nat.log2 (Floor.ceilNat (scale / target)) + 1)) <
      target := by
  let quotient : Fraction.Rational := scale / target
  let ceiling : Nat := Floor.ceilNat quotient
  let fuel : Nat := Nat.log2 ceiling + 1
  let exponent : Nat := current + fuel
  have quotientNonnegative : 0 ≤ quotient := by
    exact Fraction.Order.Field.div_nonneg_direct scaleNonnegative
      targetPositive.le
  have quotientLe : quotient ≤ (ceiling : Fraction.Rational) := by
    exact Floor.le_natCast_ceilNat_of_nonneg
      quotientNonnegative
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
      (2 : Fraction.Rational) ^ exponent :=
    by
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
  have scaled : scale < (4 : Fraction.Rational) ^ exponent * target := by
    exact (Fraction.Order.Field.div_lt_iff_pos targetPositive).mp
      quotientLtPower
  change scale / (4 : Fraction.Rational) ^ exponent < target
  apply (Fraction.Order.Field.div_lt_iff_pos powerPositive).mpr
  simpa only [Fraction.Field.mul_comm] using scaled

/-- Scan the displayed finite stages for the first quarter-radius below the target.

The computation retains the current stage and remaining fuel. It stops at the
first successful rational comparison or at the displayed terminal stage. -/
@[expose] public def scanFirstBelow (scale target : Fraction.Rational) : Nat → Nat → Nat
  | current, 0 => current
  | current, fuel + 1 =>
      if Geometric.Basic.quarterRadius scale current < target then current
      else Search.scanFirstBelow scale target (current + 1) fuel

/-- The quarter-radius scan never returns an index before its starting stage.

Each failed comparison increments the current stage, while a successful
comparison or exhausted fuel returns that same current stage. -/
public theorem scanFirstBelow_ge (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      current ≤ Search.scanFirstBelow scale target current fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [Search.scanFirstBelow]
      split
      · exact Nat.le_refl current
      · exact (Nat.le_succ current).trans
          (Search.scanFirstBelow_ge scale target (current + 1) fuel)

/-- The bounded scan examines no index beyond its displayed finite fuel.

Every failed comparison spends one unit of fuel on a successor stage. The
returned stage is bounded by the starting stage plus the supplied fuel. -/
public theorem scanFirstBelow_le_add (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      Search.scanFirstBelow scale target current fuel ≤ current + fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [Search.scanFirstBelow]
      split
      · omega
      · have bound := Search.scanFirstBelow_le_add scale target (current + 1) fuel
        omega

/-- If the terminal stage meets the target, the bounded scan returns a stage that also meets it.

A successful comparison supplies the bound directly. A failed comparison
passes the same terminal-stage certificate to the scan with preceding fuel. -/
public theorem scanFirstBelow_accurate (scale target : Fraction.Rational) :
    ∀ (current fuel : Nat),
      Geometric.Basic.quarterRadius scale (current + fuel) < target →
        Geometric.Basic.quarterRadius scale (Search.scanFirstBelow scale target current fuel) < target
  | current, 0, terminal => by
      simpa only [Nat.add_zero, Search.scanFirstBelow] using terminal
  | current, fuel + 1, terminal => by
      rw [Search.scanFirstBelow]
      split
      · assumption
      · apply Search.scanFirstBelow_accurate scale target (current + 1) fuel
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using terminal

/-- Compute a quarter-radius search stage using the binary width of its rational ceiling.

The original logarithm plus one supplies the finite scan fuel. The computation
retains the supplied scale, target and starting stage. -/
@[expose] public def firstQuarterBelow (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) : Nat :=
  Search.scanFirstBelow scale target current
    (Nat.log2 (Floor.ceilNat (scale / target)) + 1)

/-- An already accurate original starting stage is the exact result of the bounded search.

The first successful scalar comparison returns the supplied stage before
spending any of the original logarithmic scan budget.
-/
theorem firstQuarterBelow_eq_of_lt (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational)
    (accurate : Geometric.Basic.quarterRadius scale current < target) :
    Search.firstQuarterBelow scale current target = current := by
  unfold Search.firstQuarterBelow
  rewrite [Search.scanFirstBelow, if_pos accurate]
  rfl

/-- The computed quarter-radius stage is at least the requested starting stage.

The lower bound applies to the same bounded scan with its computed binary fuel. -/
public theorem firstQuarterBelow_ge (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) :
    current ≤ Search.firstQuarterBelow scale current target :=
  Search.scanFirstBelow_ge scale target current _

/-- The quarter-radius search stage is bounded by the starting stage plus its binary fuel.

The fuel remains one plus the original logarithm of the rational ceiling
computed from the supplied scale and target. -/
public theorem firstQuarterBelow_le (scale : Fraction.Rational) (current : Nat)
    (target : Fraction.Rational) :
    Search.firstQuarterBelow scale current target ≤
      current +
        (Nat.log2 (Floor.ceilNat (scale / target)) + 1) :=
  Search.scanFirstBelow_le_add scale target current _

/-- A nonnegative scale and positive target give a computed stage whose quarter-radius is strictly below that target.

The explicit endpoint certificate supplies termination accuracy to the same
bounded scan, preserving its first successful comparison and returned stage. -/
public theorem firstQuarterBelow_accurate (scale : Fraction.Rational)
    (scaleNonnegative : 0 ≤ scale) (current : Nat) (target : Fraction.Rational)
    (targetPositive : 0 < target) :
    Geometric.Basic.quarterRadius scale (Search.firstQuarterBelow scale current target) < target := by
  apply Search.scanFirstBelow_accurate scale target current
  exact Search.terminal_quarterRadius_lt scaleNonnegative targetPositive current

set_option genInjectivity false in
/-- A retained successful bounded quarter-radius search with the original scale, request and starting stage.

The quotient, ceiling, finite fuel, returned stage and attained allowance
carry their exact defining equations. The same scan proves both stage bounds
and payment of the retained positive request. -/
structure Selection (scale : Fraction.Rational) (current : Nat) (target : Fraction.Rational) where
  /-- The retained original scale is nonnegative. -/
  scaleNonnegative : 0 ≤ scale
  /-- The retained positive accuracy request. -/
  targetPositive : 0 < target
  /-- The cached scale-to-request quotient used to choose finite scan fuel. -/
  quotient : Fraction.Rational
  /-- The quotient uses the original retained scale and request. -/
  quotient_eq : quotient = scale / target
  /-- The cached natural ceiling of that same quotient. -/
  ceiling : Nat
  /-- The ceiling was computed on the retained quotient. -/
  ceiling_eq : ceiling = Floor.ceilNat quotient
  /-- The cached binary-width scan budget. -/
  fuel : Nat
  /-- The budget is the binary width of the retained ceiling. -/
  fuel_eq : fuel = Nat.log2 ceiling + 1
  /-- The actual returned stage of the original bounded scan. -/
  stage : Nat
  /-- The scan consumes the retained scale, request, starting stage and fuel. -/
  stage_eq : stage = Search.scanFirstBelow scale target current fuel
  /-- The returned stage does not precede the requested starting stage. -/
  lower : current ≤ stage
  /-- The returned stage spends no more than the retained finite fuel. -/
  upper : stage ≤ current + fuel
  /-- The actual allowance attained at the returned stage. -/
  allowance : Fraction.Rational
  /-- The allowance uses the retained scale and returned stage. -/
  allowance_eq : allowance = Geometric.Basic.quarterRadius scale stage
  /-- The attained allowance strictly pays the original accuracy request. -/
  accurate : allowance < target

constructive_injectivity Selection

/-- Compute and retain one certified quarter-radius search without repeating its fuel or allowance calculations. -/
@[expose] def Selection.build (scale : Fraction.Rational) (scaleNonnegative : 0 ≤ scale) (current : Nat)
    (target : Fraction.Rational) (targetPositive : 0 < target) : Selection scale current target :=
  let quotient := scale / target
  let ceiling := Floor.ceilNat quotient
  let fuel := Nat.log2 ceiling + 1
  let stage := scanFirstBelow scale target current fuel
  let allowance := Geometric.Basic.quarterRadius scale stage
  ⟨scaleNonnegative, targetPositive, quotient, rfl, ceiling, rfl, fuel, rfl, stage, rfl,
    scanFirstBelow_ge _ _ _ _, scanFirstBelow_le_add _ _ _ _, allowance, rfl,
    scanFirstBelow_accurate _ _ _ _ (terminal_quarterRadius_lt scaleNonnegative targetPositive current)⟩

/-- Any retained later stage also strictly pays the same original quarter-radius request. -/
theorem Selection.later_accurate {scale target : Fraction.Rational} {current later : Nat}
    (selection : Selection scale current target) (lower : selection.stage ≤ later) :
    Geometric.Basic.quarterRadius scale later < target := by
  have monotone := Geometric.Basic.quarterRadius_antitone selection.scaleNonnegative lower
  rewrite [← selection.allowance_eq] at monotone
  exact monotone.trans_lt selection.accurate

end Purelib.Approximation.Rational.Geometric.Search
