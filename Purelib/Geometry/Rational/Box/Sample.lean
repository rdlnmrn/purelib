module

public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

@[expose] public section

/-!
# Rational boxes over constructive coordinates

These boxes contain only four constructive rational endpoints and finite order
certificates.  The norm bound uses endpoint squares directly, avoiding an
absolute-value compatibility layer.
-/

namespace Purelib.Geometry.Rational.Box
section

/-- A fixed executable rational sample of a box. -/
def anchor (B : Rational.Box) :
  Data.Gaussian.Basic.Canonical := ⟨B.xLower, B.yLower⟩

/-- The lower-left anchor belongs to its closed box. -/
theorem contains_anchor (B : Rational.Box) :
  B.Contains B.anchor :=
  ⟨le_rfl, B.x_valid, le_rfl, B.y_valid⟩

set_option genInjectivity false in
/-- A displayed nonzero rational point of every proper box. The lower-left anchor is used unless it is zero, in which
case strict width makes the upper-right corner nonzero. -/
structure NonzeroSample (B : Rational.Box) where
  /-- The retained nonzero Gaussian point. -/ point : Data.Gaussian.Basic.Canonical
  /-- The retained point belongs to the original box. -/ inside : B.Contains point
  /-- The retained point differs from zero. -/ nonzero : point ≠ 0

constructive_injectivity NonzeroSample

/-- Compute a nonzero sample without selecting from a collection of points. -/
def nonzeroSample (B : Rational.Box) (proper :
  B.Proper) : NonzeroSample B := by
  if anchorZero : B.anchor = 0 then
    let upperRight : Data.Gaussian.Basic.Canonical := ⟨B.xUpper, B.yUpper⟩
    have upperRightInside : B.Contains upperRight :=
      ⟨B.x_valid, le_rfl, B.y_valid, le_rfl⟩
    have upperRightNonzero : upperRight ≠ 0 := by
      intro upperRightZero
      have lowerRealZero := congrArg
        Canonical.re anchorZero
      have upperRealZero := congrArg
        Canonical.re upperRightZero
      dsimp only [anchor, upperRight,
        Canonical.re]
        at lowerRealZero upperRealZero
      simp only [Purelib.Data.Gaussian.Basic.zero_re] at lowerRealZero upperRealZero
      dsimp only [Rational.Box.Proper] at proper
      rw [lowerRealZero, upperRealZero] at proper
      exact (lt_irrefl (0 : Fraction.Rational) proper.1).elim
    exact ⟨upperRight, upperRightInside, upperRightNonzero⟩
  else
    exact ⟨B.anchor, B.contains_anchor, anchorZero⟩
end

end Purelib.Geometry.Rational.Box

end
