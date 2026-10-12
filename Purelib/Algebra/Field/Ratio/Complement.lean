module
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Algebra.Field.Ratio.Complement

section SurveyingApplications

variable {K : Type*} [ExplicitField K]

/-! ## Problems 21--23 and spherical Pythagoras -/

/-- The ratio of one minus a nonzero scalar to that scalar is its reciprocal minus one.

The explicit nonzero hypothesis justifies clearing the common denominator. -/
private theorem complement_div (spread : K) (spreadNonzero : spread ≠ 0) :
    (1 - spread) / spread = 1 / spread - 1 := by
  apply ExplicitField.eq_of_mul_eq_mul_right spreadNonzero
  calc
    ((1 - spread) / spread) * spread = 1 - spread :=
      ExplicitField.div_mul_cancel (1 - spread) spreadNonzero
    _ = (1 / spread) * spread - 1 * spread := by
      rw [ExplicitField.div_mul_cancel 1 spreadNonzero]
      ring1
    _ = (1 / spread - 1) * spread := by ring1

open Purelib in
/-- Factor a scaled complementary ratio into reciprocal minus one times the scale.

Only the denominator must be nonzero; the scale is arbitrary. -/
public theorem scaled_complement_div
    (spread H : K) (spreadNonzero : spread ≠ 0) :
    (1 - spread) * H / spread = (1 / spread - 1) * H := by
  simp only [ExplicitField.div_eq_mul_inv]
  have relation := complement_div spread spreadNonzero
  simp only [ExplicitField.div_eq_mul_inv] at relation
  calc
    (1 - spread) * H * spread⁻¹ =
        ((1 - spread) * spread⁻¹) * H := by ring1
    _ = (1 * spread⁻¹ - 1) * H := by rw [relation]

end SurveyingApplications
end Purelib.Algebra.Field.Ratio.Complement

end
