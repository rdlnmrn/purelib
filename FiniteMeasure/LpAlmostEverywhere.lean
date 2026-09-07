import FiniteMeasure.NaturalLp
import FiniteMeasure.AlmostEverywhere

/-!
# Powered Lp quantities modulo finite almost-everywhere equality

Natural-powered finite magnitudes and distances depend only on displayed
nonzero-weight rows.  At every explicitly positive natural exponent they
vanish exactly when the relevant observables are equal in the finite
almost-everywhere sense.  The proof is a direct induction over the weighted
atom list and uses no quotient function space.
-/

namespace FiniteMeasure

private theorem equalOffZeroWeight_of_poweredDistance_eq_zero
    {α : Type} (left right : α → Coordinate) (exponent : Nat) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight atoms (fun item =>
        rationalSeparation (left item) (right item) ^ (exponent + 1)) = 0 →
      EqualOffZeroWeightOn atoms left right
  | [], zero => by
      intro atom member
      cases member
  | head :: remaining, zero => by
      let poweredDistance : α → Coordinate := fun item =>
        rationalSeparation (left item) (right item) ^ (exponent + 1)
      have totalEquation :
          head.weight * poweredDistance head.item +
              Distribution.expectationWeight remaining poweredDistance = 0 := by
        simpa only [Distribution.expectationWeight] using zero
      have headNonnegative :
          0 ≤ head.weight * poweredDistance head.item :=
        RFAP.ConstructiveFraction.mul_nonneg_direct head.nonnegative
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            (rationalSeparation_nonneg _ _) (exponent + 1))
      have tailNonnegative :
          0 ≤ Distribution.expectationWeight remaining poweredDistance :=
        Distribution.expectationWeight_nonneg remaining poweredDistance
          (fun atom member =>
            RFAP.ConstructiveFraction.pow_nonneg_direct
              (rationalSeparation_nonneg _ _) (exponent + 1))
      have headZero : head.weight * poweredDistance head.item = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          (calc
            head.weight * poweredDistance head.item ≤
                head.weight * poweredDistance head.item +
                  Distribution.expectationWeight remaining poweredDistance :=
              le_add_of_nonneg_right tailNonnegative
            _ = 0 := totalEquation)
          headNonnegative
      have tailZero :
          Distribution.expectationWeight remaining poweredDistance = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          (calc
            Distribution.expectationWeight remaining poweredDistance ≤
                head.weight * poweredDistance head.item +
                  Distribution.expectationWeight remaining poweredDistance :=
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
          by_cases separationZero :
              rationalSeparation (left head.item) (right head.item) = 0
          · exact separationZero
          · have weightPositive : 0 < head.weight :=
              lt_of_le_of_ne head.nonnegative (Ne.symm weightZero)
            have separationPositive :
                0 < rationalSeparation (left head.item) (right head.item) :=
              lt_of_le_of_ne (rationalSeparation_nonneg _ _)
                (Ne.symm separationZero)
            have poweredPositive :
                0 < poweredDistance head.item :=
              RFAP.ConstructiveFraction.pow_pos_direct
                separationPositive (exponent + 1)
            have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
              weightPositive poweredPositive
            exact (productPositive.ne' headZero).elim
      · exact equalOffZeroWeight_of_poweredDistance_eq_zero
          left right exponent remaining tailZero atom tail

namespace FiniteContent

/-- Natural-powered magnitudes respect finite almost-everywhere equality. -/
theorem poweredLp_congr_almostEverywhere {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate)
    (equal : content.EqualAlmostEverywhere left right) :
    content.poweredLp exponent left = content.poweredLp exponent right := by
  unfold poweredLp
  apply content.integral_congr_almostEverywhere
  exact equal.comp fun value => rationalSeparation value 0 ^ exponent

/-- Powered distances respect almost-everywhere replacement in both
arguments. -/
theorem poweredLpDistance_congr_almostEverywhere {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (leftFirst leftSecond rightFirst rightSecond : α → Coordinate)
    (leftEqual : content.EqualAlmostEverywhere leftFirst leftSecond)
    (rightEqual : content.EqualAlmostEverywhere rightFirst rightSecond) :
    content.poweredLpDistance exponent leftFirst rightFirst =
      content.poweredLpDistance exponent leftSecond rightSecond := by
  unfold poweredLpDistance
  apply content.integral_congr_almostEverywhere
  intro atom member
  rcases leftEqual atom member with zero | leftSame
  · exact Or.inl zero
  rcases rightEqual atom member with zero | rightSame
  · exact Or.inl zero
  · apply Or.inr
    change rationalSeparation (leftFirst atom.item) (rightFirst atom.item) ^
        exponent =
      rationalSeparation (leftSecond atom.item) (rightSecond atom.item) ^
        exponent
    rw [leftSame, rightSame]

/-- At a positive natural exponent, powered distance vanishes exactly for
finite almost-everywhere equality. -/
theorem poweredLpDistance_eq_zero_iff {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    content.poweredLpDistance (exponent + 1) left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  constructor
  · intro zero
    exact equalOffZeroWeight_of_poweredDistance_eq_zero
      left right exponent content.atoms zero
  · intro equal
    unfold poweredLpDistance
    have integrandEqual : content.EqualAlmostEverywhere
        (fun item => rationalSeparation (left item) (right item) ^
          (exponent + 1))
        (fun _ => (0 : Coordinate)) := by
      intro atom member
      rcases equal atom member with weightZero | same
      · exact Or.inl weightZero
      · apply Or.inr
        have separationZero :
            rationalSeparation (left atom.item) (right atom.item) = 0 :=
          (rationalSeparation_eq_zero_iff _ _).mpr same
        change rationalSeparation (left atom.item) (right atom.item) ^
            (exponent + 1) = 0
        rw [separationZero]
        exact zero_pow (Nat.zero_lt_succ exponent).ne'
    calc
      content.integral (fun item =>
            rationalSeparation (left item) (right item) ^ (exponent + 1)) =
          content.integral (fun _ => 0) :=
        content.integral_congr_almostEverywhere _ _ integrandEqual
      _ = content.total * 0 := content.integral_constant 0
      _ = 0 := mul_zero _

theorem poweredLp_eq_zero_iff {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (value : α → Coordinate) :
    content.poweredLp (exponent + 1) value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have differenceIdentity := content.poweredLp_sub_eq_poweredLpDistance
    (exponent + 1) value (fun _ => 0)
  have identity : content.poweredLp (exponent + 1) value =
      content.poweredLpDistance (exponent + 1) value (fun _ => 0) := by
    calc
      content.poweredLp (exponent + 1) value =
          content.poweredLp (exponent + 1)
            (fun item => value item - 0) := by
        unfold poweredLp
        exact content.integral_congr _ _ (fun item => by
          simp only [sub_zero])
      _ = content.poweredLpDistance (exponent + 1) value (fun _ => 0) :=
        differenceIdentity
  rw [identity]
  exact content.poweredLpDistance_eq_zero_iff exponent value (fun _ => 0)

theorem poweredL1_eq_zero_iff {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredL1 value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have characterization := content.poweredLp_eq_zero_iff 0 value
  simpa only [Nat.zero_add, content.poweredLp_one] using characterization

theorem poweredL2_eq_zero_iff {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredL2 value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  have characterization := content.poweredLp_eq_zero_iff 1 value
  simpa only [content.poweredLp_two] using characterization

theorem poweredL2Distance_eq_zero_iff {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.poweredL2Distance left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  have characterization := content.poweredLpDistance_eq_zero_iff
    1 left right
  simpa only [content.poweredLpDistance_two] using characterization

end FiniteContent

namespace Distribution

theorem poweredLp_congr_almostEverywhere {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate)
    (equal : distribution.EqualAlmostEverywhere left right) :
    distribution.poweredLp exponent left =
      distribution.poweredLp exponent right :=
  distribution.toFiniteContent.poweredLp_congr_almostEverywhere
    exponent left right equal

theorem poweredLpDistance_congr_almostEverywhere {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (leftFirst leftSecond rightFirst rightSecond : α → Coordinate)
    (leftEqual : distribution.EqualAlmostEverywhere leftFirst leftSecond)
    (rightEqual : distribution.EqualAlmostEverywhere rightFirst rightSecond) :
    distribution.poweredLpDistance exponent leftFirst rightFirst =
      distribution.poweredLpDistance exponent leftSecond rightSecond :=
  distribution.toFiniteContent.poweredLpDistance_congr_almostEverywhere
    exponent leftFirst leftSecond rightFirst rightSecond leftEqual rightEqual

theorem poweredLpDistance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    distribution.poweredLpDistance (exponent + 1) left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toFiniteContent.poweredLpDistance_eq_zero_iff
    exponent left right

theorem poweredLp_eq_zero_iff {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) :
    distribution.poweredLp (exponent + 1) value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toFiniteContent.poweredLp_eq_zero_iff exponent value

theorem poweredL1_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL1 value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toFiniteContent.poweredL1_eq_zero_iff value

theorem poweredL2_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL2 value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toFiniteContent.poweredL2_eq_zero_iff value

theorem poweredL2Distance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL2Distance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toFiniteContent.poweredL2Distance_eq_zero_iff left right

end Distribution

end FiniteMeasure
