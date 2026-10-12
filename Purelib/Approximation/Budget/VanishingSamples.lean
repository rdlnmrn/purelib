module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Finite zero requests determine an operationally zero sample stream

A request retains an actual arbitrarily late sample and its proved error.
The geometric movement bound upgrades these individual finite witnesses to
an all-later comparison. No limit, completed value, or vanishing assumption
on every finite sample is used.
-/

namespace Purelib.Approximation.Budget.VanishingSamples

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Data.Rat

open Purelib.Approximation.Gaussian.Geometric.GeometricApproximation

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

set_option genInjectivity false in
/-- An actual sufficiently late sample with a certified small squared norm.

The record retains its original stream stage, exact sampled value, requested floor and strict norm bound. -/
structure ZeroSample (source : Gaussian.Geometric.GeometricApproximation) (target : Fraction.Rational) (minimum : Nat)
  where
  /-- The retained finite stage of this sample. -/ stage : Nat
  /-- The retained sample stage meets the requested lower floor. -/ stage_ge : minimum ≤ stage
  /-- The cached Gaussian rational sample value. -/ value : Data.Gaussian.Basic.Canonical
  /-- The cached value is the original source sample at the retained stage. -/ value_eq : value = source.sample stage
  /-- The cached sample's squared norm is strictly below the requested target. -/ small :
    Data.Gaussian.Norm.Basic.normSq value < target

constructive_injectivity ZeroSample

/-- The caller supplies a total finite witness producer, not a proposition that suitable indices exist. Each comparison
executes that producer once. -/
@[expose] public def equivalentZero (source : Gaussian.Geometric.GeometricApproximation)
    (request : ∀ (target : Fraction.Rational), 0 < target → (minimum : Nat) →
      Approximation.Budget.VanishingSamples.ZeroSample source target minimum) :
    Gaussian.Equivalence.Equivalent source.toApproximation (GeometricApproximation.exact 0).toApproximation where
  compare leftStart rightStart target positive := by
    let quarter := target / 4
    have quarterPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let first := Search.firstQuarterBelow source.errorScale leftStart quarter
    let selected := request quarter quarterPositive first
    have movementSmall : Geometric.Basic.quarterRadius source.errorScale selected.stage < quarter :=
      (quarterRadius_antitone source.errorScale_nonneg selected.stage_ge).trans_lt
        (Search.firstQuarterBelow_accurate source.errorScale source.errorScale_nonneg
          leftStart quarter quarterPositive)
    exact
      { leftIndex := selected.stage
        rightIndex := rightStart
        left_ge := (Search.firstQuarterBelow_ge source.errorScale leftStart quarter).trans selected.stage_ge
        right_ge := le_rfl
        close := by
          intro leftLater rightLater leftOrder _
          have movement := (source.later_close leftOrder).trans_lt movementSmall
          have small : Data.Gaussian.Norm.Basic.normSq (source.sample selected.stage) < quarter := by
            rw [← selected.value_eq]
            exact selected.small
          change Data.Gaussian.Norm.Basic.normSq (source.sample leftLater - 0) < target
          rw [Data.Gaussian.Basic.sub_zero]
          calc
            _ = Data.Gaussian.Norm.Basic.normSq ((source.sample leftLater - source.sample selected.stage) +
              source.sample selected.stage) := by
              congr 1; ring1
            _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (source.sample leftLater - source.sample selected.stage) +
              Data.Gaussian.Norm.Basic.normSq (source.sample selected.stage)) :=
              Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
            _ < 2 * (quarter + quarter) := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
              (Fraction.Order.Arithmetic.add_lt_add_direct movement small)
            _ = target := by
              change 2 * (target / 4 + target / 4) = target
              rw [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
              exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide) }

end Purelib.Approximation.Budget.VanishingSamples

end
