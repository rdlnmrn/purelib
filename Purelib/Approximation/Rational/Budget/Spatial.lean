module

import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

public section

/-!
# Nested finite accuracy budgets for primitive comparisons

Choose a polynomial first.  Its Taylor constant is then a fixed finite
number, however large.  This module selects root tolerance and spatial depth
after that choice, including an arbitrary computed preparation-depth floor.
There is no refinement-uniform Taylor bound or successful-search assumption.
-/

namespace Purelib.Approximation.Rational.Budget.Spatial

set_option genInjectivity false in
/-- Retained numeric choices and payment bounds for a spatial refinement.

The preparation floor is evaluated after choosing the positive root-diameter
request, and all model, Taylor and weighted errors use these exact choices. -/
structure SpatialBudget (target movement taylorWeight errorWeight preparedScale denominatorLower : Fraction.Rational)
    (preparationDepth : Fraction.Rational → Nat) where
  /-- The cached positive model-error allowance. -/ error : Fraction.Rational
  /-- The cached model-error allowance is strictly positive. -/ error_positive : 0 < error
  /-- The model error is at most one four-thousand-and-ninety-sixth of the denominator floor. -/ relative_small : error
    / denominatorLower ≤ 1 / 4096
  /-- The cached rational root-diameter request. -/ rootDiameter : Fraction.Rational
  /-- The root-diameter request is strictly positive. -/ rootDiameter_positive : 0 < rootDiameter
  /-- The retained spatial refinement depth. -/ depth : Nat
  /-- The selected depth meets the preparation floor for this exact root-diameter request. -/ prepared_depth :
    preparationDepth rootDiameter ≤ depth
  /-- The prepared scale times spatial and root errors is at most the retained model-error allowance. -/ modelError_le :
    preparedScale * (Geometric.Basic.quarterRadius movement depth + rootDiameter) ≤ error
  /-- The spatial Taylor contribution uses at most one third of the target. -/ taylor_le : taylorWeight *
    Geometric.Basic.quarterRadius movement depth ≤ target / 3
  /-- The weighted model error uses at most one third of the target. -/ error_le : errorWeight * error ≤ target / 3

constructive_injectivity SpatialBudget

namespace SpatialBudget

/-- Compute root and spatial requests satisfying the displayed error budgets.

For a positive target and denominator floor and nonnegative weights, the builder chooses a root diameter before
evaluating its preparation floor, then retains a sufficient geometric depth and all payment bounds. -/
@[expose] def acquire (target movement taylorWeight errorWeight preparedScale denominatorLower : Fraction.Rational)
    (preparationDepth : Fraction.Rational → Nat)
    (targetPositive : 0 < target) (movementNonnegative : 0 ≤ movement)
    (taylorNonnegative : 0 ≤ taylorWeight) (errorNonnegative : 0 ≤ errorWeight)
    (scaleNonnegative : 0 ≤ preparedScale) (lowerPositive : 0 < denominatorLower) :
    Approximation.Rational.Budget.Spatial.SpatialBudget target movement taylorWeight errorWeight preparedScale
      denominatorLower preparationDepth := by
  let third := target / 3
  have thirdPositive : 0 < third := Fraction.Order.Field.div_pos_direct targetPositive (by decide)
  let error := min (denominatorLower / 4096) (Weighted.allowance third errorWeight)
  have errorPositive : 0 < error := Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct lowerPositive (by decide +kernel))
    (Weighted.allowance_positive thirdPositive errorNonnegative)
  let rootDiameter := Weighted.allowance (error / 2) preparedScale
  have rootPositive : 0 < rootDiameter := Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct errorPositive (by decide)) scaleNonnegative
  let spatialTarget := min rootDiameter (Weighted.allowance third taylorWeight)
  have spatialPositive : 0 < spatialTarget := Fraction.Order.Basic.lt_min rootPositive
    (Weighted.allowance_positive thirdPositive taylorNonnegative)
  let floor := preparationDepth rootDiameter
  let depth := Search.firstQuarterBelow movement floor spatialTarget
  have spatialBound : Geometric.Basic.quarterRadius movement depth < spatialTarget :=
    Search.firstQuarterBelow_accurate movement movementNonnegative floor spatialTarget spatialPositive
  have movementLe : Geometric.Basic.quarterRadius movement depth ≤ rootDiameter :=
    spatialBound.le.trans (Fraction.Order.Basic.min_le_left _ _)
  refine
    { error := error
      error_positive := errorPositive
      relative_small := ?_
      rootDiameter := rootDiameter
      rootDiameter_positive := rootPositive
      depth := depth
      prepared_depth := Search.firstQuarterBelow_ge movement floor spatialTarget
      modelError_le := ?_
      taylor_le := ?_
      error_le := ?_ }
  · apply (Fraction.Order.Field.div_le_iff_pos lowerPositive).mpr
    calc
      error ≤ denominatorLower / 4096 := Fraction.Order.Basic.min_le_left _ _
      _ = (1 / 4096 : Fraction.Rational) * denominatorLower := by
        rw [Algebra.Field.ExplicitField.div_eq_mul_inv, Algebra.Field.ExplicitField.div_eq_mul_inv]
        ring1
  · calc
      _ ≤ preparedScale * (rootDiameter + rootDiameter) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add movementLe le_rfl) scaleNonnegative
      _ = preparedScale * rootDiameter + preparedScale * rootDiameter := by ring1
      _ ≤ error / 2 + error / 2 := add_le_add
        (Weighted.mul_allowance_le (Fraction.Order.Field.div_pos_direct errorPositive (by decide)).le scaleNonnegative)
        (Weighted.mul_allowance_le (Fraction.Order.Field.div_pos_direct errorPositive (by decide)).le scaleNonnegative)
      _ = (error / 2) * 2 := by ring1
      _ = error := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (spatialBound.le.trans (Fraction.Order.Basic.min_le_right _ _)) taylorNonnegative).trans
        (Weighted.mul_allowance_le thirdPositive.le taylorNonnegative)
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Basic.min_le_right _ _) errorNonnegative).trans (Weighted.mul_allowance_le thirdPositive.le
        errorNonnegative)

end SpatialBudget

end Purelib.Approximation.Rational.Budget.Spatial

end
