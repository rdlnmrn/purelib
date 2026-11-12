module
import Mathlib.Order.Defs.PartialOrder

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- A finite rational centre with a nonnegative squared-error allowance. -/
structure Ball where
  /-- The retained Gaussian rational centre. -/ center : Data.Gaussian.Basic.Canonical
  /-- The retained rational squared-error allowance. -/ radiusSq : Fraction.Rational
  /-- The squared-error allowance is nonnegative. -/ radiusSq_nonneg : 0 ≤ radiusSq

constructive_injectivity Ball

namespace Ball

/-- Exact centre and squared-radius readbacks determine the complete original certified ball. -/
theorem ext {left right : Ball} (center : left.center = right.center)
    (radius : left.radiusSq = right.radiusSq) : left = right := by
  cases left
  cases right
  cases center
  cases radius
  rfl

/-- Decide exact numerical ball equality from the retained centre and squared radius. -/
instance : DecidableEq Ball := fun left right =>
  if centerEq : left.center = right.center then
    if radiusEq : left.radiusSq = right.radiusSq then
      .isTrue (by cases left; cases right; cases centerEq; cases radiusEq; rfl)
    else .isFalse (fun same => radiusEq (congrArg Ball.radiusSq same))
  else .isFalse (fun same => centerEq (congrArg Ball.center same))

/-- The retained centre passes the exact sufficient whole-ball separation test. -/
abbrev Separated (ball : Ball) :=
  2 * ball.radiusSq < Norm.Basic.normSq ball.center

/-- Conjugate the original ball's centre while retaining its squared radius and nonnegativity certificate. -/
def conj (ball : Ball) : Ball where
  center := Data.Gaussian.Basic.conj ball.center
  radiusSq := ball.radiusSq
  radiusSq_nonneg := ball.radiusSq_nonneg

/-- Conjugation changes no stored squared radius. -/
theorem conj_radiusSq (ball : Ball) : ball.conj.radiusSq = ball.radiusSq := rfl

/-- Twice conjugating a ball recovers the same complete original ball. -/
theorem conj_conj (ball : Ball) : ball.conj.conj = ball := by
  cases ball with
  | mk center radius nonnegative =>
      unfold conj
      rewrite [Data.Gaussian.Basic.conj_conj]
      rfl

/-- The squared distance from a Gaussian rational reading to the retained centre is within the allowance. -/
def Contains (ball :
  Ball) (value : Data.Gaussian.Basic.Canonical) : Prop :=
  Norm.Basic.normSq (value - ball.center) ≤ ball.radiusSq

/-- Decide ball membership by exact rational comparison of the squared distance. -/
instance containsDecidable (ball :
  Ball) (value : Data.Gaussian.Basic.Canonical) :
    Decidable (ball.Contains value) := by
  unfold Contains
  infer_instance

/-- The retained centre belongs to its own ball. -/
theorem contains_center (ball :
  Ball) : ball.Contains ball.center := by
  unfold Contains
  rw [Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero]
  exact ball.radiusSq_nonneg
/-- The zero-radius ball centered at one exact Gaussian rational. -/
def point (value : Data.Gaussian.Basic.Canonical) : Ball where
  center := value
  radiusSq := 0
  radiusSq_nonneg := le_rfl

/-- An exact point ball contains its retained center. -/
theorem contains_point (value : Data.Gaussian.Basic.Canonical) :
    (point value).Contains value := by
  unfold Contains point
  rw [Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero]

/-- A zero-radius ball contains exactly its retained Gaussian-rational centre. -/
theorem contains_point_iff (center value : Data.Gaussian.Basic.Canonical) :
    (point center).Contains value ↔ value = center := by
  constructor
  · intro inside
    have nonnegative := Norm.Basic.normSq_nonneg (value - center)
    have equal := le_antisymm inside nonnegative
    exact Data.Gaussian.Basic.gaussian_eq_of_sub_eq_zero (Norm.Basic.normSq_eq_zero.mp equal)
  · intro equal
    exact equal.symm ▸ contains_point center

end Ball

end Purelib.Approximation.Gaussian.Enclosure

end
