import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EssentialMaximum

/-!
# Root-free finite Lp comparison

An explicit essential magnitude ceiling converts a higher natural-powered
integral into a lower one with the expected ceiling factor.  The formulation
uses only rational powers and finite sums, avoiding roots and completed normed
spaces.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- Finite Cauchy comparison between powered L1 and powered L2.  The total
mass factor is explicit because a finite content need not be normalized. -/
theorem poweredL1_sq_le_total_mul_poweredL2 {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.poweredL1 value ^ 2 ≤
      content.total * content.poweredL2 value := by
  let magnitude := fun item => rationalSeparation (value item) 0
  let one := fun _ : α => (1 : Coordinate)
  have cauchy := content.productIntegral_sq_le_poweredL2_mul magnitude one
  have productIdentity : content.productIntegral magnitude one =
      content.poweredL1 value := by
    unfold productIntegral poweredL1 magnitude one
    exact content.integral_congr _ _ (fun item => by ring1)
  have magnitudeIdentity : content.poweredL2 magnitude =
      content.poweredL2 value := by
    unfold poweredL2 magnitude
    exact content.integral_congr _ _ (fun item => by
      rw [rationalSeparation_sq]
      ring1)
  have oneIdentity : content.poweredL2 one = content.total := by
    unfold poweredL2 one
    calc
      content.integral (fun _ : α => (1 : Coordinate) ^ 2) =
          content.integral (fun _ => (1 : Coordinate)) :=
        content.integral_congr _ _ (fun item => by ring1)
      _ = content.total * 1 := content.integral_constant 1
      _ = content.total := mul_one _
  rw [productIdentity, magnitudeIdentity, oneIdentity] at cauchy
  simpa only [mul_comm] using cauchy

/-- Distance form of finite L1--L2 comparison. -/
theorem l1Distance_sq_le_total_mul_poweredL2Distance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.l1Distance left right ^ 2 ≤
      content.total * content.poweredL2Distance left right := by
  have bound := content.poweredL1_sq_le_total_mul_poweredL2
    (fun item => left item - right item)
  rw [content.poweredL1_sub_eq_l1Distance] at bound
  exact bound

/-- Under an explicit nonnegative essential ceiling, adding `extra` to a
natural exponent costs at most `ceiling ^ extra`. -/
theorem poweredLp_add_le_of_essentialBound {α : Type}
    (content : FiniteContent α) (exponent extra : Nat)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.poweredLp (exponent + extra) value ≤
      ceiling ^ extra * content.poweredLp exponent value := by
  unfold poweredLp
  calc
    content.integral (fun item =>
          rationalSeparation (value item) 0 ^ (exponent + extra)) =
        content.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent *
            rationalSeparation (value item) 0 ^ extra) := by
      exact content.integral_congr _ _ (fun item => by rw [pow_add])
    _ ≤ content.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent *
            ceiling ^ extra) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.pow_le_pow_direct
            (rationalSeparation_nonneg _ _) bound extra)
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            (rationalSeparation_nonneg _ _) exponent)
    _ = ceiling ^ extra * content.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent) := by
      calc
        content.integral (fun item =>
            rationalSeparation (value item) 0 ^ exponent *
              ceiling ^ extra) =
            content.integral (fun item => ceiling ^ extra *
              rationalSeparation (value item) 0 ^ exponent) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling ^ extra * content.integral (fun item =>
              rationalSeparation (value item) 0 ^ exponent) :=
          content.integral_scale _ _

/-- The computed least essential maximum gives the canonical finite
higher-to-lower powered-Lp comparison. -/
theorem poweredLp_add_le_essentialMaximum {α : Type}
    (content : FiniteContent α) (exponent extra : Nat)
    (value : α → Coordinate) :
    content.poweredLp (exponent + extra) value ≤
      content.essentialMaximumMagnitude value ^ extra *
        content.poweredLp exponent value :=
  content.poweredLp_add_le_of_essentialBound exponent extra value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- In particular, the finite second moment is bounded by the essential
maximum times the exact L1 magnitude. -/
theorem poweredL2_le_essentialMaximum_mul_poweredL1 {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.poweredL2 value ≤
      content.essentialMaximumMagnitude value * content.poweredL1 value := by
  have bound := content.poweredLp_add_le_essentialMaximum 1 1 value
  rw [show 1 + 1 = 2 by decide, content.poweredLp_two,
    content.poweredLp_one, pow_one] at bound
  exact bound

/-- The same higher-to-lower comparison for exact finite powered distances,
given an essential ceiling on the pointwise separations. -/
theorem poweredLpDistance_add_le_of_essentialBound {α : Type}
    (content : FiniteContent α) (exponent extra : Nat)
    (left right : α → Coordinate) (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        rationalSeparation (left atom.item) (right atom.item) ≤ ceiling) :
    content.poweredLpDistance (exponent + extra) left right ≤
      ceiling ^ extra *
        content.poweredLpDistance exponent left right := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
          rationalSeparation (left item) (right item) ^
            (exponent + extra)) =
        content.integral (fun item =>
          rationalSeparation (left item) (right item) ^ exponent *
            rationalSeparation (left item) (right item) ^ extra) := by
      exact content.integral_congr _ _ (fun item => by rw [pow_add])
    _ ≤ content.integral (fun item =>
          rationalSeparation (left item) (right item) ^ exponent *
            ceiling ^ extra) := by
      apply content.integral_mono_off_zero
      intro atom member
      rcases bounded atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (RFAP.ConstructiveFraction.pow_le_pow_direct
            (rationalSeparation_nonneg _ _) bound extra)
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            (rationalSeparation_nonneg _ _) exponent)
    _ = ceiling ^ extra * content.integral (fun item =>
          rationalSeparation (left item) (right item) ^ exponent) := by
      calc
        content.integral (fun item =>
            rationalSeparation (left item) (right item) ^ exponent *
              ceiling ^ extra) =
            content.integral (fun item => ceiling ^ extra *
              rationalSeparation (left item) (right item) ^ exponent) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling ^ extra * content.integral (fun item =>
              rationalSeparation (left item) (right item) ^ exponent) :=
          content.integral_scale _ _

/-- Powered L2 distance is controlled by L1 distance times the computed
essential maximum of the explicit difference. -/
theorem poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL2Distance left right ≤
      content.essentialMaximumMagnitude
          (fun item => left item - right item) *
        content.l1Distance left right := by
  let difference := fun item => left item - right item
  let ceiling := content.essentialMaximumMagnitude difference
  have differenceBound :=
    content.essentiallyBoundedBy_essentialMaximumMagnitude difference
  have separationBound : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        rationalSeparation (left atom.item) (right atom.item) ≤ ceiling := by
    intro atom member
    rcases differenceBound atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      dsimp only [difference] at bound
      rw [rationalSeparation_eq_sub_zero]
      exact bound
  have bound := content.poweredLpDistance_add_le_of_essentialBound
    1 1 left right ceiling separationBound
  rw [show 1 + 1 = 2 by decide, content.poweredLpDistance_two,
    content.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- Quantitative finite interpolation: an L1 error allowance and an
essential pointwise separation ceiling imply a powered-L2 error allowance. -/
theorem poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
    {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) (ceiling epsilon : Coordinate)
    (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨
        rationalSeparation (left atom.item) (right atom.item) ≤ ceiling)
    (l1Bound : content.l1Distance left right ≤ epsilon) :
    content.poweredL2Distance left right ≤ ceiling * epsilon := by
  have comparison := content.poweredLpDistance_add_le_of_essentialBound
    1 1 left right ceiling bounded
  rw [show 1 + 1 = 2 by decide, content.poweredLpDistance_two,
    content.poweredLpDistance_one, pow_one] at comparison
  exact comparison.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      l1Bound ceilingNonnegative)

end FiniteContent

namespace Distribution

/-- On a normalized finite probability table, powered L1 squared is bounded
by powered L2.  This is the root-free `L2`-dominates-`L1` comparison. -/
theorem poweredL1_sq_le_poweredL2 {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL1 value ^ 2 ≤
      distribution.poweredL2 value := by
  have bound := distribution.toFiniteContent
    |>.poweredL1_sq_le_total_mul_poweredL2 value
  rw [distribution.toFiniteContent_total, one_mul] at bound
  exact bound

theorem l1Distance_sq_le_poweredL2Distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.l1Distance left right ^ 2 ≤
      distribution.poweredL2Distance left right := by
  have bound := distribution.toFiniteContent
    |>.l1Distance_sq_le_total_mul_poweredL2Distance left right
  rw [distribution.toFiniteContent_total, one_mul] at bound
  exact bound

/-- Squared separation of two exact finite expectations is bounded by the
powered-L2 distance of their displayed observables.  This is the root-free
expectation form of `L2`-dominates-`L1`. -/
theorem expectation_separation_sq_le_poweredL2Distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ^ 2 ≤
      distribution.poweredL2Distance left right := by
  have separationLe := distribution.expectation_separation_le_l1Distance
    left right
  have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
    (rationalSeparation_nonneg
      (distribution.expectation left) (distribution.expectation right))
    separationLe 2
  exact powered.trans
    (distribution.l1Distance_sq_le_poweredL2Distance left right)

private theorem lt_of_sq_lt_sq_of_nonnegative_right
    {left right : Coordinate} (rightNonnegative : 0 ≤ right)
    (squares : left ^ 2 < right ^ 2) : left < right := by
  rcases lt_trichotomy left right with less | equal | greater
  · exact less
  · subst right
    exact (lt_irrefl _ squares).elim
  · have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      rightNonnegative greater.le 2
    exact ((not_lt_of_ge squareOrder) squares).elim

/-- A strict powered-L2 error below the square of a supplied positive
rational tolerance gives ordinary strict separation of the exact finite
expectations.  The tolerance is supplied; no square root is selected. -/
theorem expectation_separation_lt_of_poweredL2Distance_lt_sq {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (small : distribution.poweredL2Distance left right < epsilon ^ 2) :
    rationalSeparation (distribution.expectation left)
        (distribution.expectation right) < epsilon := by
  have squares :=
    (distribution.expectation_separation_sq_le_poweredL2Distance
      left right).trans_lt small
  exact lt_of_sq_lt_sq_of_nonnegative_right positive.le squares

theorem poweredLp_add_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (exponent extra : Nat)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.poweredLp (exponent + extra) value ≤
      ceiling ^ extra * distribution.poweredLp exponent value :=
  distribution.toFiniteContent.poweredLp_add_le_of_essentialBound
    exponent extra value ceiling bounded

theorem poweredLp_add_le_essentialMaximum {α : Type}
    (distribution : Distribution α) (exponent extra : Nat)
    (value : α → Coordinate) :
    distribution.poweredLp (exponent + extra) value ≤
      distribution.essentialMaximumMagnitude value ^ extra *
        distribution.poweredLp exponent value :=
  distribution.toFiniteContent.poweredLp_add_le_essentialMaximum
    exponent extra value

theorem poweredL2_le_essentialMaximum_mul_poweredL1 {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL2 value ≤
      distribution.essentialMaximumMagnitude value *
        distribution.poweredL1 value :=
  distribution.toFiniteContent
    |>.poweredL2_le_essentialMaximum_mul_poweredL1 value

theorem poweredLpDistance_add_le_of_essentialBound {α : Type}
    (distribution : Distribution α) (exponent extra : Nat)
    (left right : α → Coordinate) (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨
        rationalSeparation (left atom.item) (right atom.item) ≤ ceiling) :
    distribution.poweredLpDistance (exponent + extra) left right ≤
      ceiling ^ extra *
        distribution.poweredLpDistance exponent left right :=
  distribution.toFiniteContent
    |>.poweredLpDistance_add_le_of_essentialBound exponent extra
      left right ceiling bounded

theorem poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.poweredL2Distance left right ≤
      distribution.essentialMaximumMagnitude
          (fun item => left item - right item) *
        distribution.l1Distance left right :=
  distribution.toFiniteContent
    |>.poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
      left right

theorem poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
    {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) (ceiling epsilon : Coordinate)
    (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨
        rationalSeparation (left atom.item) (right atom.item) ≤ ceiling)
    (l1Bound : distribution.l1Distance left right ≤ epsilon) :
    distribution.poweredL2Distance left right ≤ ceiling * epsilon :=
  distribution.toFiniteContent
    |>.poweredL2Distance_le_mul_of_l1Distance_le_and_essentialBound
      left right ceiling epsilon ceilingNonnegative bounded l1Bound

end Distribution

end FiniteMeasure
