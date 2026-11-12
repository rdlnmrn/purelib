module

public import Init.Data.Prod

/-! # Structural laws for the original product Boolean comparison -/

public section

namespace Purelib.Data.Prod

universe u v

/-- The original product comparison is reflexive when both coordinate comparisons are reflexive.

The supplied coordinate dictionaries retain the original short-circuit Boolean
comparison. The certificate uses their scalar reflexivity laws directly.
-/
theorem reflBEq {Alpha : Type u} {Beta : Type v} [BEq Alpha] [BEq Beta]
    [ReflBEq Alpha] [ReflBEq Beta] : ReflBEq (Alpha × Beta) where
  rfl {value} := by
    have first : value.1 == value.1 := BEq.refl value.1
    have last : value.2 == value.2 := BEq.refl value.2
    change (value.1 == value.1 && value.2 == value.2) = true
    rewrite [first, last]
    rfl

/-- The original product comparison is lawful when both coordinate comparisons are lawful.

Structural certificates identify each successful coordinate comparison. The
global and scoped registrations have the same priority and retain the original
Boolean comparison dictionary and explicitly supplied local instances.
-/
scoped instance (priority := 1001) lawfulBEq {Alpha : Type u} {Beta : Type v}
    [BEq Alpha] [BEq Beta] [LawfulBEq Alpha] [LawfulBEq Beta] : LawfulBEq (Alpha × Beta) where
  toReflBEq := reflBEq
  eq_of_beq {first last} same := by
    change (first.1 == last.1 && first.2 == last.2) = true at same
    have left : first.1 == last.1 := by
      cases tested : first.1 == last.1 with
      | false =>
          rewrite [tested] at same
          nomatch same
      | true => rfl
    have right : first.2 == last.2 := by
      rewrite [left] at same
      exact same
    exact _root_.Prod.ext (eq_of_beq left) (eq_of_beq right)

attribute [instance 1001] lawfulBEq

end Purelib.Data.Prod

end
