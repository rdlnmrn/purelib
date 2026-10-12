module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace Purelib.Approximation.Gaussian.Request.Basic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Data.Rat

namespace Name

/-- Operand accuracy used for addition and subtraction. -/
@[expose] public def additiveInputTarget (target :
  Fraction.Rational) : Fraction.Rational := target / 4

/-- Operand radii below the quarter-target request make the sum ball's squared radius below the original target. -/
theorem add_radius_lt (left right : Enclosure.Ball) {target :
  Fraction.Rational}
    (leftSmall : left.radiusSq < additiveInputTarget target)
    (rightSmall : right.radiusSq < additiveInputTarget target) :
    (left.add right).radiusSq < target := by
  unfold additiveInputTarget at leftSmall rightSmall
  change 2 * (left.radiusSq + right.radiusSq) < target
  have sumSmall : left.radiusSq + right.radiusSq < target / 2 := by
    calc
      left.radiusSq + right.radiusSq < target / 4 + target / 4 :=
        Fraction.Order.Arithmetic.add_lt_add_direct leftSmall rightSmall
      _ = target / 2 := Purelib.Data.Rat.Bounds.Quarter.two_quarters target
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Fraction.Rational) < 2) sumSmall
  calc
    2 * (left.radiusSq + right.radiusSq) < 2 * (target / 2) := scaled
    _ = target := by
      calc
        2 * (target / 2) = (target / 2) * 2 :=
          Fraction.Field.mul_comm _ _
        _ = target :=
          Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)

/-- Add two rational enclosure request oracles.

Each operand receives one quarter of the positive output target; the centre bound is twice the sum of the retained
operand bounds. -/
@[expose] public def add (left right :
  Gaussian.Request.Basic.Name) : Gaussian.Request.Basic.Name where
  request target positive :=
    let inputPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    (left.request (additiveInputTarget target) inputPositive).add
      (right.request (additiveInputTarget target) inputPositive)
  accurate target positive := by
    apply add_radius_lt
    · exact left.accurate _ _
    · exact right.accurate _ _
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  center_bounded target positive := by
    dsimp only
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.center_bounded _ _) (right.center_bounded _ _))
        (by decide))

/-- Negate each requested ball while retaining the original accuracy and uniform centre bound. -/
@[expose] public def neg (name : Gaussian.Request.Basic.Name) :
  Gaussian.Request.Basic.Name where
  request target positive := (name.request target positive).neg
  accurate target positive := name.accurate target positive
  centerBound := name.centerBound
  centerBound_nonneg := name.centerBound_nonneg
  center_bounded target positive := by
    change Data.Gaussian.Norm.Basic.normSq (-(name.request target positive).center) ≤ name.centerBound
    rw [Data.Gaussian.Norm.Basic.normSq_neg]
    exact name.center_bounded target positive

/-- Subtract two enclosure request oracles by adding the left oracle to the negated right oracle. -/
@[expose] public def sub (left right :
  Gaussian.Request.Basic.Name) : Gaussian.Request.Basic.Name := left.add right.neg

/-! ## Request-level soundness -/

/-- The sum request admits sums of readings admitted by the two original quarter-target operand requests. -/
theorem request_contains_add (left right :
  Gaussian.Request.Basic.Name) {target : Fraction.Rational}
    (positive : 0 < target) {x y : Data.Gaussian.Basic.Canonical}
    (xInside :
      (left.request (additiveInputTarget target)
        (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)).Contains x)
    (yInside :
      (right.request (additiveInputTarget target)
        (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive)).Contains y) :
    (left.add right).request target positive |>.Contains (x + y) :=
  Enclosure.Ball.contains_add xInside yInside
end Name

end Purelib.Approximation.Gaussian.Request.Basic

end

public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Data.Rat
namespace Coherent

/-- The finite operand request used by stateful addition is strictly smaller than its positive outer request. -/
theorem additiveInputTarget_lt_target {target :
  Fraction.Rational}
    (positive : 0 < target) :
    Purelib.Approximation.Gaussian.Request.Basic.Name.additiveInputTarget target <
      target := by
  unfold Approximation.Gaussian.Request.Basic.Name.additiveInputTarget
  apply (Fraction.Order.Field.div_lt_iff_pos
    (show (0 : Fraction.Rational) < 4 by decide)).2
  have threeTargetPositive : 0 < 3 * target :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive
  calc
    target = target + 0 := by ring1
    _ < target + 3 * target :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct
        threeTargetPositive target
    _ = target * 4 := by ring1
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
