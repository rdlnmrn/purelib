import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.PoweredLp

/-!
# Natural-powered finite Lp quantities

Natural powers of rational separation remain rational.  They provide exact
finite powered-Lp quantities and tail estimates without selecting roots or
constructing completed normed spaces.
-/

namespace FiniteMeasure

/-- Squaring rational separation removes its sign and recovers the ordinary
square of the difference. -/
theorem rationalSeparation_sq (left right : Coordinate) :
    rationalSeparation left right ^ 2 = (left - right) ^ 2 := by
  have separationSub : rationalSeparation left right =
      rationalSeparation (left - right) 0 := by
    unfold rationalSeparation
    congr 1 <;> ring1
  rw [separationSub]
  calc
    rationalSeparation (left - right) 0 ^ 2 =
        rationalSeparation (left - right) 0 *
          rationalSeparation (left - right) 0 := by
      ring1
    _ = rationalSeparation ((left - right) * (left - right)) 0 :=
      (rationalSeparation_mul_zero (left - right) (left - right)).symm
    _ = (left - right) * (left - right) := by
      apply rationalSeparation_zero_of_nonneg
      have squareNonnegative :=
        RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)
      simpa only [pow_two] using squareNonnegative
    _ = (left - right) ^ 2 := by ring1

/-- A squared rational-separation bound below the square of a supplied
positive tolerance gives the corresponding ordinary strict separation.  The
tolerance is explicit, so no square root is selected. -/
theorem rationalSeparation_lt_of_sq_lt_sq
    {left right tolerance : Coordinate} (positive : 0 < tolerance)
    (small : rationalSeparation left right ^ 2 < tolerance ^ 2) :
    rationalSeparation left right < tolerance := by
  rcases lt_trichotomy (rationalSeparation left right) tolerance with
    less | equal | greater
  · exact less
  · subst tolerance
    exact (lt_irrefl _ small).elim
  · have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      positive.le greater.le 2
    exact ((not_lt_of_ge squareOrder) small).elim

namespace FiniteContent

/-- Exact integral of a displayed natural power of rational magnitude. -/
def poweredLp {α : Type} (content : FiniteContent α) (exponent : Nat)
    (value : α → Coordinate) : Coordinate :=
  content.integral fun item =>
    rationalSeparation (value item) 0 ^ exponent

/-- Exact natural-powered separation of two rational observables. -/
def poweredLpDistance {α : Type} (content : FiniteContent α)
    (exponent : Nat) (left right : α → Coordinate) : Coordinate :=
  content.integral fun item =>
    rationalSeparation (left item) (right item) ^ exponent

theorem poweredLp_nonnegative {α : Type} (content : FiniteContent α)
    (exponent : Nat) (value : α → Coordinate) :
    0 ≤ content.poweredLp exponent value := by
  apply content.integral_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.pow_nonneg_direct
    (rationalSeparation_nonneg _ _) exponent

theorem poweredLpDistance_nonnegative {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    0 ≤ content.poweredLpDistance exponent left right := by
  apply content.integral_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.pow_nonneg_direct
    (rationalSeparation_nonneg _ _) exponent

/-- Exact homogeneity of natural-powered finite distance. -/
theorem poweredLpDistance_scale {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (factor : Coordinate) (left right : α → Coordinate) :
    content.poweredLpDistance exponent
        (fun item => factor * left item)
        (fun item => factor * right item) =
      rationalSeparation factor 0 ^ exponent *
        content.poweredLpDistance exponent left right := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        rationalSeparation (factor * left item) (factor * right item) ^
          exponent) =
        content.integral (fun item => rationalSeparation factor 0 ^ exponent *
          rationalSeparation (left item) (right item) ^ exponent) :=
      content.integral_congr _ _ (fun item => by
        rw [rationalSeparation_scale, mul_pow])
    _ = rationalSeparation factor 0 ^ exponent *
          content.integral (fun item =>
            rationalSeparation (left item) (right item) ^ exponent) :=
      content.integral_scale _ _

theorem poweredLp_scale {α : Type} (content : FiniteContent α)
    (exponent : Nat) (factor : Coordinate) (value : α → Coordinate) :
    content.poweredLp exponent (fun item => factor * value item) =
      rationalSeparation factor 0 ^ exponent *
        content.poweredLp exponent value := by
  unfold poweredLp
  calc
    content.integral (fun item =>
        rationalSeparation (factor * value item) 0 ^ exponent) =
        content.integral (fun item => rationalSeparation factor 0 ^ exponent *
          rationalSeparation (value item) 0 ^ exponent) :=
      content.integral_congr _ _ (fun item => by
        rw [rationalSeparation_mul_zero, mul_pow])
    _ = rationalSeparation factor 0 ^ exponent *
          content.integral (fun item =>
            rationalSeparation (value item) 0 ^ exponent) :=
      content.integral_scale _ _

theorem poweredLp_one {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredLp 1 value = content.poweredL1 value := by
  unfold poweredLp poweredL1
  exact content.integral_congr _ _ (fun item => by rw [pow_one])

theorem poweredLp_zero {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredLp 0 value = content.total := by
  unfold poweredLp
  calc
    content.integral (fun item => rationalSeparation (value item) 0 ^ 0) =
        content.integral (fun _ => (1 : Coordinate)) :=
      content.integral_congr _ _ (fun item => pow_zero _)
    _ = content.total * 1 := content.integral_constant 1
    _ = content.total := mul_one _

theorem poweredLp_constant {α : Type} (content : FiniteContent α)
    (exponent : Nat) (constant : Coordinate) :
    content.poweredLp exponent (fun _ => constant) =
      content.total * rationalSeparation constant 0 ^ exponent := by
  unfold poweredLp
  exact content.integral_constant _

theorem poweredLp_two {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredLp 2 value = content.poweredL2 value := by
  unfold poweredLp poweredL2
  exact content.integral_congr _ _ (fun item => by
    calc
      rationalSeparation (value item) 0 ^ 2 =
          (value item - 0) ^ 2 := rationalSeparation_sq (value item) 0
      _ = value item ^ 2 := by ring1)

theorem poweredLpDistance_one {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredLpDistance 1 left right =
      content.l1Distance left right := by
  unfold poweredLpDistance l1Distance
  exact content.integral_congr _ _ (fun item => by rw [pow_one])

theorem poweredLpDistance_two {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredLpDistance 2 left right =
      content.poweredL2Distance left right := by
  unfold poweredLpDistance poweredL2Distance poweredL2
  exact content.integral_congr _ _ (fun item =>
    rationalSeparation_sq (left item) (right item))

/-- The natural-powered magnitude of an explicit difference is exactly the
corresponding powered distance. -/
theorem poweredLp_sub_eq_poweredLpDistance {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    content.poweredLp exponent (fun item => left item - right item) =
      content.poweredLpDistance exponent left right := by
  unfold poweredLp poweredLpDistance
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun magnitude => magnitude ^ exponent)
      (rationalSeparation_eq_sub_zero (left item) (right item)).symm)

@[simp] theorem poweredLpDistance_refl {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (value : α → Coordinate) :
    content.poweredLpDistance (exponent + 1) value value = 0 := by
  unfold poweredLpDistance
  calc
    content.integral (fun item =>
        rationalSeparation (value item) (value item) ^ (exponent + 1)) =
        content.integral (fun _ => (0 : Coordinate)) :=
      content.integral_congr _ _ (fun item => by
        simp only [rationalSeparation, sub_self, max_self]
        exact zero_pow (Nat.zero_lt_succ exponent).ne')
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem poweredLpDistance_symm {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    content.poweredLpDistance exponent left right =
      content.poweredLpDistance exponent right left := by
  unfold poweredLpDistance
  exact content.integral_congr _ _ (fun item => by
    rw [rationalSeparation_symm])

end FiniteContent

namespace Distribution

def poweredLp {α : Type} (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.poweredLp exponent value

def poweredLpDistance {α : Type} (distribution : Distribution α)
    (exponent : Nat) (left right : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.poweredLpDistance exponent left right

theorem poweredLp_nonnegative {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) :
    0 ≤ distribution.poweredLp exponent value :=
  distribution.toFiniteContent.poweredLp_nonnegative exponent value

theorem poweredLpDistance_nonnegative {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    0 ≤ distribution.poweredLpDistance exponent left right :=
  distribution.toFiniteContent.poweredLpDistance_nonnegative
    exponent left right

theorem poweredLp_scale {α : Type} (distribution : Distribution α)
    (exponent : Nat) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.poweredLp exponent (fun item => factor * value item) =
      rationalSeparation factor 0 ^ exponent *
        distribution.poweredLp exponent value :=
  distribution.toFiniteContent.poweredLp_scale exponent factor value

theorem poweredLpDistance_scale {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (factor : Coordinate) (left right : α → Coordinate) :
    distribution.poweredLpDistance exponent
        (fun item => factor * left item)
        (fun item => factor * right item) =
      rationalSeparation factor 0 ^ exponent *
        distribution.poweredLpDistance exponent left right :=
  distribution.toFiniteContent.poweredLpDistance_scale
    exponent factor left right

@[simp] theorem poweredLpDistance_refl {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) :
    distribution.poweredLpDistance (exponent + 1) value value = 0 :=
  distribution.toFiniteContent.poweredLpDistance_refl exponent value

theorem poweredLpDistance_symm {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    distribution.poweredLpDistance exponent left right =
      distribution.poweredLpDistance exponent right left :=
  distribution.toFiniteContent.poweredLpDistance_symm exponent left right

theorem poweredLp_zero {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.poweredLp 0 value = 1 := by
  change distribution.toFiniteContent.poweredLp 0 value = 1
  rw [distribution.toFiniteContent.poweredLp_zero,
    distribution.toFiniteContent_total]

theorem poweredLp_constant {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (constant : Coordinate) :
    distribution.poweredLp exponent (fun _ => constant) =
      rationalSeparation constant 0 ^ exponent := by
  change distribution.toFiniteContent.poweredLp exponent
      (fun _ => constant) = _
  rw [distribution.toFiniteContent.poweredLp_constant,
    distribution.toFiniteContent_total, one_mul]

theorem poweredLp_one {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.poweredLp 1 value = distribution.poweredL1 value :=
  distribution.toFiniteContent.poweredLp_one value

theorem poweredLp_two {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.poweredLp 2 value = distribution.poweredL2 value :=
  distribution.toFiniteContent.poweredLp_two value

theorem poweredLpDistance_one {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredLpDistance 1 left right =
      distribution.l1Distance left right :=
  distribution.toFiniteContent.poweredLpDistance_one left right

theorem poweredLpDistance_two {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredLpDistance 2 left right =
      distribution.poweredL2Distance left right :=
  distribution.toFiniteContent.poweredLpDistance_two left right

theorem poweredLp_sub_eq_poweredLpDistance {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    distribution.poweredLp exponent (fun item => left item - right item) =
      distribution.poweredLpDistance exponent left right :=
  distribution.toFiniteContent.poweredLp_sub_eq_poweredLpDistance
    exponent left right

/-- Finite powered Markov estimate.  A large-error event is controlled by
the exact natural-powered distance divided by the displayed threshold power.
-/
theorem probability_separationAtLeast_le_poweredLpDistance
    {α : Type} (distribution : Distribution α) (exponent : Nat)
    (threshold : Coordinate) (positive : 0 < threshold)
    (left right : α → Coordinate) :
    distribution.probability (separationAtLeast threshold left right) ≤
      distribution.poweredLpDistance exponent left right /
        threshold ^ exponent := by
  apply distribution.markov_bound
    (separationAtLeast threshold left right)
    (fun item => rationalSeparation (left item) (right item) ^ exponent)
    (threshold ^ exponent)
    (RFAP.ConstructiveFraction.pow_pos_direct positive exponent)
  · intro atom member
    exact RFAP.ConstructiveFraction.pow_nonneg_direct
      (rationalSeparation_nonneg _ _) exponent
  · intro atom member selected
    have thresholdLe : threshold ≤
        rationalSeparation (left atom.item) (right atom.item) :=
      of_decide_eq_true selected
    exact RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
      thresholdLe exponent

end Distribution

end FiniteMeasure
