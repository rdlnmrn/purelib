import FiniteMeasure.L1
import FiniteMeasure.ZeroWeight

/-!
# Finite almost-everywhere calculus

Equality almost everywhere means equality at every displayed atom whose
rational weight is nonzero.  The relation is executable on finite atom
tables and supports arithmetic, integration, and an exact L1
characterization without quotienting a function space.
-/

namespace FiniteMeasure

theorem rationalSeparation_eq_zero_iff (left right : Coordinate) :
    rationalSeparation left right = 0 ↔ left = right := by
  constructor
  · intro zero
    have leftRight : left - right ≤ 0 :=
      (le_max_left (left - right) (right - left)).trans_eq zero
    have rightLeft : right - left ≤ 0 :=
      (le_max_right (left - right) (right - left)).trans_eq zero
    exact RFAP.ConstructiveFraction.le_antisymm _ _
      (sub_nonpos.mp leftRight) (sub_nonpos.mp rightLeft)
  · intro same
    subst right
    unfold rationalSeparation
    simp only [sub_self, max_self]

namespace EqualOffZeroWeightOn

/-- Pointwise postcomposition respects equality off zero weight. -/
theorem comp {α β γ : Type} {atoms : List (Weighted α)}
    {left right : α → β}
    (equal : EqualOffZeroWeightOn atoms left right)
    (function : β → γ) :
    EqualOffZeroWeightOn atoms
      (fun item => function (left item))
      (fun item => function (right item)) := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · exact Or.inr (congrArg function same)

theorem add {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Coordinate}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item + rightFirst item)
      (fun item => leftSecond item + rightSecond item) := by
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change leftFirst atom.item + rightFirst atom.item =
      leftSecond atom.item + rightSecond atom.item
    rw [leftSame, rightSame]

theorem neg {α : Type} {atoms : List (Weighted α)}
    {left right : α → Coordinate}
    (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms
      (fun item => -left item) (fun item => -right item) :=
  equal.comp fun value => -value

theorem sub {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Coordinate}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item - rightFirst item)
      (fun item => leftSecond item - rightSecond item) := by
  have combined := leftEqual.add rightEqual.neg
  exact combined

theorem mul {α : Type} {atoms : List (Weighted α)}
    {leftFirst leftSecond rightFirst rightSecond : α → Coordinate}
    (leftEqual : EqualOffZeroWeightOn atoms leftFirst leftSecond)
    (rightEqual : EqualOffZeroWeightOn atoms rightFirst rightSecond) :
    EqualOffZeroWeightOn atoms
      (fun item => leftFirst item * rightFirst item)
      (fun item => leftSecond item * rightSecond item) := by
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change leftFirst atom.item * rightFirst atom.item =
      leftSecond atom.item * rightSecond atom.item
    rw [leftSame, rightSame]

theorem scale {α : Type} {atoms : List (Weighted α)}
    (factor : Coordinate) {left right : α → Coordinate}
    (equal : EqualOffZeroWeightOn atoms left right) :
    EqualOffZeroWeightOn atoms
      (fun item => factor * left item)
      (fun item => factor * right item) :=
  equal.comp fun value => factor * value

end EqualOffZeroWeightOn

private theorem equalOffZeroWeight_of_expectationSeparation_eq_zero
    {α : Type} (left right : α → Coordinate) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight atoms (fun item =>
        rationalSeparation (left item) (right item)) = 0 →
      EqualOffZeroWeightOn atoms left right
  | [], zero => by
      intro atom member
      cases member
  | head :: remaining, zero => by
      let separation : α → Coordinate := fun item =>
        rationalSeparation (left item) (right item)
      have totalEquation :
          head.weight * separation head.item +
              Distribution.expectationWeight remaining separation = 0 := by
        simpa only [Distribution.expectationWeight] using zero
      have headNonnegative : 0 ≤ head.weight * separation head.item :=
        RFAP.ConstructiveFraction.mul_nonneg_direct head.nonnegative
          (rationalSeparation_nonneg _ _)
      have tailNonnegative :
          0 ≤ Distribution.expectationWeight remaining separation :=
        Distribution.expectationWeight_nonneg remaining separation
          (fun atom member => rationalSeparation_nonneg _ _)
      have headZero : head.weight * separation head.item = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          (calc
            head.weight * separation head.item ≤
                head.weight * separation head.item +
                  Distribution.expectationWeight remaining separation :=
              le_add_of_nonneg_right tailNonnegative
            _ = 0 := totalEquation)
          headNonnegative
      have tailZero :
          Distribution.expectationWeight remaining separation = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          (calc
            Distribution.expectationWeight remaining separation ≤
                head.weight * separation head.item +
                  Distribution.expectationWeight remaining separation :=
              le_add_of_nonneg_left headNonnegative
            _ = 0 := totalEquation)
          tailNonnegative
      intro atom member
      rcases List.mem_cons.mp member with same | tail
      · subst atom
        by_cases weightZero : head.weight = 0
        · exact Or.inl weightZero
        · apply Or.inr
          apply (rationalSeparation_eq_zero_iff
            (left head.item) (right head.item)).mp
          by_cases separationZero : separation head.item = 0
          · exact separationZero
          · have weightPositive : 0 < head.weight :=
              lt_of_le_of_ne head.nonnegative (Ne.symm weightZero)
            have separationPositive : 0 < separation head.item :=
              lt_of_le_of_ne (rationalSeparation_nonneg _ _)
                (Ne.symm separationZero)
            have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
              weightPositive separationPositive
            exact (productPositive.ne' headZero).elim
      · exact equalOffZeroWeight_of_expectationSeparation_eq_zero
          left right remaining tailZero atom tail

namespace FiniteContent

/-- Finite almost-everywhere equality relative to this displayed content. -/
def EqualAlmostEverywhere {α β : Type} (content : FiniteContent α)
    (left right : α → β) : Prop :=
  EqualOffZeroWeightOn content.atoms left right

theorem integral_congr_almostEverywhere {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (equal : content.EqualAlmostEverywhere left right) :
    content.integral left = content.integral right :=
  expectationWeight_congr_off_zero content.atoms left right equal

theorem l1Distance_eq_zero_of_equalAlmostEverywhere {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (equal : content.EqualAlmostEverywhere left right) :
    content.l1Distance left right = 0 := by
  have separationEqual : EqualOffZeroWeightOn content.atoms
      (fun item => rationalSeparation (left item) (right item))
      (fun _ => (0 : Coordinate)) := by
    intro atom member
    rcases equal atom member with zero | same
    · exact Or.inl zero
    · apply Or.inr
      change rationalSeparation (left atom.item) (right atom.item) = 0
      rw [same]
      exact (rationalSeparation_eq_zero_iff _ _).mpr rfl
  calc
    content.l1Distance left right = content.integral (fun _ => 0) := by
      unfold l1Distance FiniteContent.integral
      exact expectationWeight_congr_off_zero content.atoms _ _
        separationEqual
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem equalAlmostEverywhere_of_l1Distance_eq_zero {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (zero : content.l1Distance left right = 0) :
    content.EqualAlmostEverywhere left right := by
  apply equalOffZeroWeight_of_expectationSeparation_eq_zero left right
    content.atoms
  exact zero

/-- Exact finite L1 separation vanishes precisely for equality away from
zero-weight atoms. -/
theorem l1Distance_eq_zero_iff {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.l1Distance left right = 0 ↔
      content.EqualAlmostEverywhere left right :=
  ⟨content.equalAlmostEverywhere_of_l1Distance_eq_zero left right,
    content.l1Distance_eq_zero_of_equalAlmostEverywhere left right⟩

end FiniteContent

namespace Distribution

def EqualAlmostEverywhere {α β : Type} (distribution : Distribution α)
    (left right : α → β) : Prop :=
  EqualOffZeroWeightOn distribution.atoms left right

theorem l1Distance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.l1Distance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toFiniteContent.l1Distance_eq_zero_iff left right

end Distribution

end FiniteMeasure
