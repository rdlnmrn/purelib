import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.AlmostEverywhere
import FiniteMeasure.NaturalLp

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace FiniteMeasure

/-- Pointwise upper bound away from displayed zero-weight atoms. -/
def BoundedAboveOffZeroWeightOn {α : Type} (atoms : List (Weighted α))
    (value : α → Coordinate) (ceiling : Coordinate) : Prop :=
  ∀ atom, atom ∈ atoms →
    atom.weight = 0 ∨ value atom.item ≤ ceiling

/-- Rational magnitude is bounded away from displayed zero-weight atoms. -/
def EssentiallyBoundedByOn {α : Type} (atoms : List (Weighted α))
    (value : α → Coordinate) (ceiling : Coordinate) : Prop :=
  BoundedAboveOffZeroWeightOn atoms
    (fun item => rationalSeparation (value item) 0) ceiling

/-- Weighted finite integration is monotone when the pointwise comparison
may fail only at zero-weight atoms. -/
theorem expectationWeight_mono_off_zero {α : Type}
    (lower upper : α → Coordinate) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) →
      Distribution.expectationWeight atoms lower ≤
        Distribution.expectationWeight atoms upper
  | [], pointwise => le_rfl
  | atom :: remaining, pointwise => by
      have tailPointwise : ∀ candidate, candidate ∈ remaining →
          candidate.weight = 0 ∨
            lower candidate.item ≤ upper candidate.item :=
        fun candidate member =>
          pointwise candidate (List.mem_cons_of_mem atom member)
      have tailBound := expectationWeight_mono_off_zero
        lower upper remaining tailPointwise
      rcases pointwise atom List.mem_cons_self with zero | headBound
      · simp only [Distribution.expectationWeight, zero, zero_mul, zero_add]
        exact tailBound
      · simp only [Distribution.expectationWeight]
        exact add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            headBound atom.nonnegative)
          tailBound

namespace FiniteContent

def EssentiallyBoundedBy {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) (ceiling : Coordinate) : Prop :=
  EssentiallyBoundedByOn content.atoms value ceiling

theorem integral_mono_off_zero {α : Type} (content : FiniteContent α)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    content.integral lower ≤ content.integral upper :=
  expectationWeight_mono_off_zero lower upper content.atoms pointwise

/-- Essential boundedness is invariant under finite almost-everywhere
equality. -/
theorem essentiallyBoundedBy_congr_almostEverywhere {α : Type}
    (content : FiniteContent α) {left right : α → Coordinate}
    {ceiling : Coordinate}
    (equal : content.EqualAlmostEverywhere left right)
    (bounded : content.EssentiallyBoundedBy left ceiling) :
    content.EssentiallyBoundedBy right ceiling := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change rationalSeparation (right atom.item) 0 ≤ ceiling
    change rationalSeparation (left atom.item) 0 ≤ ceiling at bound
    rw [← same]
    exact bound

/-- The zero observable has the exact zero essential bound. -/
theorem essentiallyBoundedBy_zero {α : Type}
    (content : FiniteContent α) :
    content.EssentiallyBoundedBy (fun _ => 0) 0 := by
  intro atom member
  apply Or.inr
  unfold rationalSeparation
  change max ((0 : Coordinate) - 0) (0 - 0) ≤ 0
  rw [sub_self, max_self]

/-- A constant observable is bounded by its exact rational magnitude. -/
theorem essentiallyBoundedBy_constant {α : Type}
    (content : FiniteContent α) (constant : Coordinate) :
    content.EssentiallyBoundedBy (fun _ => constant)
      (rationalSeparation constant 0) := by
  intro atom member
  exact Or.inr le_rfl

theorem essentiallyBoundedBy_add {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (leftCeiling rightCeiling : Coordinate)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item + right item)
      (leftCeiling + rightCeiling) := by
  intro atom member
  rcases leftBound atom member with zero | leftLe
  · exact Or.inl zero
  rcases rightBound atom member with zero | rightLe
  · exact Or.inl zero
  · apply Or.inr
    exact (rationalSeparation_add_zero_le
      (left atom.item) (right atom.item)).trans
        (add_le_add leftLe rightLe)

theorem essentiallyBoundedBy_scale {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.EssentiallyBoundedBy (fun item => factor * value item)
      (rationalSeparation factor 0 * ceiling) := by
  intro atom member
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change rationalSeparation (factor * value atom.item) 0 ≤
      rationalSeparation factor 0 * ceiling
    change rationalSeparation (value atom.item) 0 ≤ ceiling at bound
    rw [rationalSeparation_mul_zero]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      bound (rationalSeparation_nonneg _ _)

theorem essentiallyBoundedBy_neg {α : Type}
    (content : FiniteContent α) (value : α → Coordinate)
    (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.EssentiallyBoundedBy (fun item => -value item) ceiling := by
  intro atom member
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change rationalSeparation (-value atom.item) 0 ≤ ceiling
    have magnitudeEqual :
        rationalSeparation (-value atom.item) 0 =
          rationalSeparation (value atom.item) 0 := by
      simpa only [neg_zero] using
        rationalSeparation_neg (value atom.item) 0
    rw [magnitudeEqual]
    exact bound

theorem essentiallyBoundedBy_sub {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (leftCeiling rightCeiling : Coordinate)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item - right item)
      (leftCeiling + rightCeiling) := by
  change content.EssentiallyBoundedBy
    (fun item => left item + -right item) (leftCeiling + rightCeiling)
  exact content.essentiallyBoundedBy_add left (fun item => -right item)
    leftCeiling rightCeiling leftBound
    (content.essentiallyBoundedBy_neg right rightCeiling rightBound)

/-- Products of essentially bounded finite observables multiply their
displayed rational ceilings. -/
theorem essentiallyBoundedBy_mul {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (leftCeiling rightCeiling : Coordinate)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item * right item)
      (leftCeiling * rightCeiling) := by
  intro atom member
  rcases leftBound atom member with zero | leftLe
  · exact Or.inl zero
  rcases rightBound atom member with zero | rightLe
  · exact Or.inl zero
  · apply Or.inr
    change rationalSeparation (left atom.item * right atom.item) 0 ≤
      leftCeiling * rightCeiling
    rw [rationalSeparation_mul_zero]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      leftLe rightLe (rationalSeparation_nonneg _ _)
        ((rationalSeparation_nonneg _ _).trans leftLe)

/-- An essential ceiling controls the exact finite L1 quantity, charged by
the total displayed mass. -/
theorem poweredL1_le_of_essentialBound {α : Type}
    (content : FiniteContent α) (value : α → Coordinate)
    (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredL1 value ≤ content.total * ceiling := by
  calc
    content.poweredL1 value ≤ content.integral (fun _ => ceiling) :=
      content.integral_mono_off_zero _ _ bounded
    _ = content.total * ceiling := content.integral_constant ceiling

/-- The same essential ceiling controls every displayed natural-powered
quantity. -/
theorem poweredLp_le_of_essentialBound {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredLp exponent value ≤
      content.total * ceiling ^ exponent := by
  calc
    content.poweredLp exponent value ≤
        content.integral (fun _ => ceiling ^ exponent) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · exact Or.inr (RFAP.ConstructiveFraction.pow_le_pow_direct
          (rationalSeparation_nonneg _ _) bound exponent)
    _ = content.total * ceiling ^ exponent :=
      content.integral_constant (ceiling ^ exponent)

/-- L1--essential-bound Hölder: a bound which fails only on zero-weight
atoms still controls the product integral exactly. -/
theorem poweredL1_mul_le_of_right_essentialBound {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy right ceiling) :
    content.poweredL1 (fun item => left item * right item) ≤
      ceiling * content.poweredL1 left := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          rationalSeparation (left item * right item) 0) =
        content.integral (fun item =>
          rationalSeparation (left item) 0 *
            rationalSeparation (right item) 0) := by
      exact content.integral_congr _ _ (fun item =>
        rationalSeparation_mul_zero (left item) (right item))
    _ ≤ content.integral (fun item =>
          rationalSeparation (left item) 0 * ceiling) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · exact Or.inr
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            bound (rationalSeparation_nonneg _ _))
    _ = ceiling * content.integral (fun item =>
          rationalSeparation (left item) 0) := by
      calc
        content.integral (fun item =>
            rationalSeparation (left item) 0 * ceiling) =
            content.integral (fun item =>
              ceiling * rationalSeparation (left item) 0) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling * content.integral (fun item =>
            rationalSeparation (left item) 0) := content.integral_scale _ _

end FiniteContent

namespace Distribution

def EssentiallyBoundedBy {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) (ceiling : Coordinate) : Prop :=
  distribution.toFiniteContent.EssentiallyBoundedBy value ceiling

theorem poweredL1_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (ceiling : Coordinate)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredL1 value ≤ ceiling := by
  have estimate := distribution.toFiniteContent.poweredL1_le_of_essentialBound
    value ceiling bounded
  rw [distribution.toFiniteContent_total, one_mul] at estimate
  exact estimate

theorem poweredLp_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredLp exponent value ≤ ceiling ^ exponent := by
  have estimate := distribution.toFiniteContent.poweredLp_le_of_essentialBound
    exponent value ceiling bounded
  rw [distribution.toFiniteContent_total, one_mul] at estimate
  exact estimate

end Distribution

end FiniteMeasure
