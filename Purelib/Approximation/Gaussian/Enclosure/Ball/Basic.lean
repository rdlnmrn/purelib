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

set_option genInjectivity false in
/-- A finite rational centre with a nonnegative squared-error allowance. -/
structure Ball where
  /-- The retained Gaussian rational centre. -/ center : Data.Gaussian.Basic.Canonical
  /-- The retained rational squared-error allowance. -/ radiusSq : Fraction.Rational
  /-- The squared-error allowance is nonnegative. -/ radiusSq_nonneg : 0 ≤ radiusSq

constructive_injectivity Ball

namespace Ball

/-- The squared distance from a Gaussian rational reading to the retained centre is within the allowance. -/
def Contains (ball :
  Ball) (value : Data.Gaussian.Basic.Canonical) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (value - ball.center) ≤ ball.radiusSq

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
  rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
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
  rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]

end Ball

end Purelib.Approximation.Gaussian.Enclosure

end
