import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.PoweredLp

/-!
# Root-free finite L2 geometry

The exact rational primitive is the powered quantity `∫ f²`, not a chosen
square root.  The parallelogram identity remains exact, while a direct
two-factor quasi-triangle inequality gives an unconditional rational bound.
-/

namespace FiniteMeasure

/-- Elementary rational square bound underlying the root-free powered-L2
quasi-triangle inequality. -/
theorem add_sq_le_two_mul_add_sq (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    2 * (left ^ 2 + right ^ 2) - (left + right) ^ 2 =
        (left - right) ^ 2 := by ring1
    _ ≥ 0 := RFAP.ConstructiveFraction.sq_nonneg_direct _

namespace FiniteContent

/-- Exact finite parallelogram identity for the rational powered-L2
quantity. -/
theorem poweredL2_add_sub {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL2 (fun item => left item + right item) +
        content.poweredL2 (fun item => left item - right item) =
      2 * (content.poweredL2 left + content.poweredL2 right) := by
  unfold poweredL2
  calc
    content.integral (fun item => (left item + right item) ^ 2) +
          content.integral (fun item => (left item - right item) ^ 2) =
        content.integral (fun item =>
          (left item + right item) ^ 2 +
            (left item - right item) ^ 2) :=
      (content.integral_add _ _).symm
    _ = content.integral (fun item =>
          2 * left item ^ 2 + 2 * right item ^ 2) := by
      exact content.integral_congr _ _ (fun item => by ring1)
    _ = 2 * (content.integral (fun item => left item ^ 2) +
          content.integral (fun item => right item ^ 2)) := by
      rw [content.integral_add, content.integral_scale,
        content.integral_scale]
      ring1

/-- Unconditional root-free quasi-triangle inequality for powered L2.  It
requires no rational upper approximation to either square root. -/
theorem poweredL2_add_le_two_mul_add {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.poweredL2 (fun item => left item + right item) ≤
      2 * (content.poweredL2 left + content.poweredL2 right) := by
  unfold poweredL2
  calc
    content.integral (fun item => (left item + right item) ^ 2) ≤
        content.integral (fun item =>
          2 * (left item ^ 2 + right item ^ 2)) := by
      apply content.integral_mono
      intro atom member
      exact add_sq_le_two_mul_add_sq (left atom.item) (right atom.item)
    _ = 2 * (content.integral (fun item => left item ^ 2) +
          content.integral (fun item => right item ^ 2)) := by
      rw [content.integral_scale, content.integral_add]

/-- Three-observable form of the same root-free powered-L2
quasi-triangle inequality. -/
theorem poweredL2Distance_le_two_mul_add {α : Type}
    (content : FiniteContent α)
    (left middle right : α → Coordinate) :
    content.poweredL2Distance left right ≤
      2 * (content.poweredL2Distance left middle +
        content.poweredL2Distance middle right) := by
  have bound := content.poweredL2_add_le_two_mul_add
    (fun item => left item - middle item)
    (fun item => middle item - right item)
  calc
    content.poweredL2Distance left right =
        content.poweredL2 (fun item =>
          (left item - middle item) + (middle item - right item)) := by
      unfold poweredL2Distance
      exact content.poweredL2_congr _ _ (fun item => by ring1)
    _ ≤ 2 * (content.poweredL2Distance left middle +
          content.poweredL2Distance middle right) := bound

end FiniteContent

namespace Distribution

theorem poweredL2_add_sub {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.poweredL2 (fun item => left item + right item) +
        distribution.poweredL2 (fun item => left item - right item) =
      2 * (distribution.poweredL2 left + distribution.poweredL2 right) :=
  distribution.toFiniteContent.poweredL2_add_sub left right

theorem poweredL2_add_le_two_mul_add {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL2 (fun item => left item + right item) ≤
      2 * (distribution.poweredL2 left + distribution.poweredL2 right) :=
  distribution.toFiniteContent.poweredL2_add_le_two_mul_add left right

theorem poweredL2Distance_le_two_mul_add {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Coordinate) :
    distribution.poweredL2Distance left right ≤
      2 * (distribution.poweredL2Distance left middle +
        distribution.poweredL2Distance middle right) :=
  distribution.toFiniteContent.poweredL2Distance_le_two_mul_add
    left middle right

end Distribution

end FiniteMeasure
