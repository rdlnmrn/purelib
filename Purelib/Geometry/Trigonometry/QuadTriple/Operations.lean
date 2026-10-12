module
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Trigonometry

@[expose] public section

/-!
# Divine Proportions, Chapter 11: the two struts theorem

Triangle proportions reduces the geometric configuration to the two
normalized quad triples used below.  Homogeneity then removes every quotient
with explicit cancellation of `p` and `r`.
-/

namespace Purelib.Geometry.Trigonometry.QuadTriple.Operations

variable {K : Type*} [ExplicitField K]

/-- Quad triples are homogeneous of degree two. -/
theorem quadTriple_scale (a b c scale : K) (triple :
  Geometry.Trigonometry.QuadTriple a b c) :
    Geometry.Trigonometry.QuadTriple (scale * a) (scale * b) (scale * c) := by
  unfold Geometry.Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction at triple ⊢
  calc
    (scale * a + scale * b + scale * c) ^ 2 -
        2 * ((scale * a) ^ 2 + (scale * b) ^ 2 +
          (scale * c) ^ 2) =
      scale ^ 2 *
        ((a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2)) := by ring1
    _ = 0 := by rw [triple]; ring1

/-- Reversing a quad triple does not change Archimedes' symmetric polynomial. -/
theorem quadTriple_reverse (a b c : K) (triple :
  Geometry.Trigonometry.QuadTriple a b c) :
    Geometry.Trigonometry.QuadTriple c b a := by
  unfold Geometry.Trigonometry.QuadTriple QuadTriple.Basic.archimedesFunction at triple ⊢
  calc
    (c + b + a) ^ 2 - 2 * (c ^ 2 + b ^ 2 + a ^ 2) =
        (a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring1
    _ = 0 := triple

/-- Multiplying all three entries by a displayed inverse—written as division by the scale—preserves a quad triple.
Cancellation is required only when a later proof identifies normalized coordinates. -/
theorem quadTriple_normalize (a b c scale : K)
    (triple : Geometry.Trigonometry.QuadTriple a b c) :
    Geometry.Trigonometry.QuadTriple (a / scale) (b / scale) (c / scale) := by
  have scaled := quadTriple_scale a b c (1 / scale) triple
  have firstCoordinate : (1 / scale) * a = a / scale := by
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have secondCoordinate : (1 / scale) * b = b / scale := by
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  have thirdCoordinate : (1 / scale) * c = c / scale := by
    simp only [ExplicitField.div_eq_mul_inv]
    ring1
  rwa [firstCoordinate, secondCoordinate, thirdCoordinate] at scaled
end Purelib.Geometry.Trigonometry.QuadTriple.Operations

end
