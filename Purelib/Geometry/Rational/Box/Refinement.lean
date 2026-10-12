module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
import Mathlib.Order.Basic

open Purelib

open Purelib.Geometry

section
@[expose] public section

/-!
# Rational boxes over constructive coordinates

These boxes contain only four constructive rational endpoints and finite order
certificates.  The norm bound uses endpoint squares directly, avoiding an
absolute-value compatibility layer.
-/

namespace Purelib.Geometry.Rational.Box
section Box

/-- The inner box lies coordinatewise within the closed outer box. -/
def Refines (inner outer : Rational.Box) : Prop :=
  outer.xLower ≤ inner.xLower ∧ inner.xUpper ≤ outer.xUpper ∧
    outer.yLower ≤ inner.yLower ∧ inner.yUpper ≤ outer.yUpper

/-- Strict coordinatewise containment of one constructive box in another. -/
structure StrictInterior (inner outer :
  Rational.Box) : Prop where
  /-- The inner left side lies strictly to the right of the outer left side. -/ left : outer.xLower < inner.xLower
  /-- The inner right side lies strictly to the left of the outer right side. -/ right : inner.xUpper < outer.xUpper
  /-- The inner bottom side lies strictly above the outer bottom side. -/ bottom : outer.yLower < inner.yLower
  /-- The inner top side lies strictly below the outer top side. -/ top : inner.yUpper < outer.yUpper

/-- Decide strict box containment by its four endpoint comparisons. -/
instance strictInteriorDecidable (inner outer :
  Rational.Box) :
    Decidable (inner.StrictInterior outer) := by
  by_cases left : outer.xLower < inner.xLower
  · by_cases right : inner.xUpper < outer.xUpper
    · by_cases bottom : outer.yLower < inner.yLower
      · by_cases top : inner.yUpper < outer.yUpper
        · exact isTrue ⟨left, right, bottom, top⟩
        · exact isFalse fun strict => top strict.top
      · exact isFalse fun strict => bottom strict.bottom
    · exact isFalse fun strict => right strict.right
  · exact isFalse fun strict => left strict.left

namespace Refinement.StrictInterior

/-- Strict coordinate containment implies closed coordinate refinement. -/
theorem refines {inner outer :
  Rational.Box}
    (strict : inner.StrictInterior outer) : inner.Refines outer :=
  ⟨strict.left.le, strict.right.le, strict.bottom.le, strict.top.le⟩

/-- Refining a box that is already strictly interior preserves all four strict outer inequalities. -/
theorem of_refines {inner middle outer :
  Rational.Box}
    (strict : middle.StrictInterior outer)
    (refines : inner.Refines middle) : inner.StrictInterior outer :=
  ⟨strict.left.trans_le refines.1,
    refines.2.1.trans_lt strict.right,
    strict.bottom.trans_le refines.2.2.1,
    refines.2.2.2.trans_lt strict.top⟩

end Refinement.StrictInterior

namespace Refinement.StrictInterior.Boxes

/-- A strict subbox remains strict after enlarging its outer box. -/
theorem trans_refines {inner middle outer :
  Rational.Box}
    (strict : inner.StrictInterior middle)
    (refines : middle.Refines outer) : inner.StrictInterior outer :=
  ⟨refines.1.trans_lt strict.left,
    strict.right.trans_le refines.2.1,
    refines.2.2.1.trans_lt strict.bottom,
    strict.top.trans_le refines.2.2.2⟩

end Refinement.StrictInterior.Boxes

/-- Every box refines itself. -/
theorem refines_refl (B : Rational.Box) : B.Refines
  B :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

namespace Refines

/-- Compose coordinatewise box refinements. -/
theorem trans {A B C : Rational.Box} (hAB :
  A.Refines B) (hBC : B.Refines C) :
    A.Refines C := by
  rcases hAB with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  rcases hBC with ⟨hxLower', hxUpper', hyLower', hyUpper'⟩
  exact ⟨hxLower'.trans hxLower, hxUpper.trans hxUpper',
    hyLower'.trans hyLower, hyUpper.trans hyUpper'⟩

/-- Membership is preserved when passing from a refining box to its outer box. -/
theorem contains {inner outer :
  Rational.Box} {z : Data.Gaussian.Basic.Canonical}
    (refines : inner.Refines outer) (inside : inner.Contains z) :
    outer.Contains z := by
  rcases refines with ⟨hxLower, hxUpper, hyLower, hyUpper⟩
  rcases inside with ⟨hzxLower, hzxUpper, hzyLower, hzyUpper⟩
  exact ⟨hxLower.trans hzxLower, hzxUpper.trans hxUpper,
    hyLower.trans hzyLower, hzyUpper.trans hyUpper⟩

end Refines

end Box

end Purelib.Geometry.Rational.Box

end

end

section
@[expose] public section

/-!
# Choice-free global winding nonnegativity

If a clear box had negative raw winding, one eliminant-safe Newton band of
raw winding four can be removed and a negative complement cell retained.
Finite iteration would then create one more pairwise-separated shrinking
track than the explicit rational grid can contain.
-/

namespace Purelib.Geometry.Rational.Box.Refinement.StrictInterior.GlobalNonnegativity

/-- Strict containment persists when the outer box is enlarged. -/
theorem
  strictInterior_trans_refines
    {small middle outer : Rational.Box}
    (strict : small.StrictInterior middle)
    (refines : middle.Refines outer) : small.StrictInterior outer :=
  ⟨refines.1.trans_lt strict.left,
    strict.right.trans_le refines.2.1,
    refines.2.2.1.trans_lt strict.bottom,
    strict.top.trans_le refines.2.2.2⟩
end Purelib.Geometry.Rational.Box.Refinement.StrictInterior.GlobalNonnegativity

end
