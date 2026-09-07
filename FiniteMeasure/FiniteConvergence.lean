import FiniteMeasure.L1

/-!
# Finite convergence certificates

The usual monotone, Fatou, and dominated convergence theorems concern
completed limits.  This module retains their executable finite content:
displayed monotone chains have monotone rational integrals, displayed lower
envelopes satisfy the finite Fatou inequality, and an integrable rational
error envelope gives an explicit accuracy certificate.

No sequence, limit, supremum, extended value, or completed function space is
formed.
-/

namespace FiniteMeasure

/-- Pointwise order only where a displayed atom table can observe it. -/
def PointwiseLeOn {α : Type} (atoms : List (Weighted α))
    (lower upper : α → Coordinate) : Prop :=
  ∀ atom, atom ∈ atoms → lower atom.item ≤ upper atom.item

theorem PointwiseLeOn.refl {α : Type} (atoms : List (Weighted α))
    (value : α → Coordinate) : PointwiseLeOn atoms value value := by
  intro atom member
  exact le_rfl

theorem PointwiseLeOn.trans {α : Type} {atoms : List (Weighted α)}
    {first second third : α → Coordinate}
    (firstSecond : PointwiseLeOn atoms first second)
    (secondThird : PointwiseLeOn atoms second third) :
    PointwiseLeOn atoms first third := by
  intro atom member
  exact (firstSecond atom member).trans (secondThird atom member)

/-- Adjacent pointwise monotonicity for one displayed finite observable
schedule. -/
def PointwiseMonotoneChainOn {α : Type} (atoms : List (Weighted α)) :
    List (α → Coordinate) → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      PointwiseLeOn atoms first second ∧
        PointwiseMonotoneChainOn atoms (second :: remaining)

/-- Adjacent monotonicity of a displayed rational list. -/
def MonotoneCoordinateChain : List Coordinate → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      first ≤ second ∧ MonotoneCoordinateChain (second :: remaining)

namespace FiniteContent

/-- Finite monotone convergence at the exact level available here: every
pointwise-monotone displayed schedule is sent to a monotone schedule of exact
rational integrals. -/
theorem integral_monotoneChain {α : Type} (content : FiniteContent α) :
    ∀ observables : List (α → Coordinate),
      PointwiseMonotoneChainOn content.atoms observables →
        MonotoneCoordinateChain (observables.map content.integral)
  | [], monotone => monotone
  | [_], monotone => monotone
  | first :: second :: remaining, monotone => by
      exact ⟨content.integral_mono first second monotone.1,
        content.integral_monotoneChain (second :: remaining) monotone.2⟩

end FiniteContent

/-- Pointwise minimum of one nonempty displayed observable family.  The
first observable is separate so no artificial value is needed for an empty
family. -/
def pointwiseMinimum {α : Type} (first : α → Coordinate) :
    List (α → Coordinate) → α → Coordinate
  | [], item => first item
  | next :: remaining, item =>
      min (first item) (pointwiseMinimum next remaining item)

theorem pointwiseMinimum_le_of_mem {α : Type}
    (first : α → Coordinate) (remaining : List (α → Coordinate))
    {candidate : α → Coordinate}
    (member : candidate ∈ first :: remaining) (item : α) :
    pointwiseMinimum first remaining item ≤ candidate item := by
  induction remaining generalizing first candidate with
  | nil =>
      have same : candidate = first := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      subst candidate
      exact le_rfl
  | cons next remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with same | tail
      · subst candidate
        exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis next tail)

namespace FiniteContent

/-- Finite Fatou lower-envelope inequality: the integral of the pointwise
minimum of a displayed nonempty family is below the integral of every member.
This is the finite arithmetic core of the usual liminf inequality. -/
theorem integral_pointwiseMinimum_le_of_mem {α : Type}
    (content : FiniteContent α) (first : α → Coordinate)
    (remaining : List (α → Coordinate)) {candidate : α → Coordinate}
    (member : candidate ∈ first :: remaining) :
    content.integral (pointwiseMinimum first remaining) ≤
      content.integral candidate := by
  apply content.integral_mono
  intro atom atomMember
  exact pointwiseMinimum_le_of_mem first remaining member atom.item

end FiniteContent

/-- A rational envelope dominates the absolute error on every displayed
atom. -/
def DominatesErrorOn {α : Type} (atoms : List (Weighted α))
    (envelope left right : α → Coordinate) : Prop :=
  ∀ atom, atom ∈ atoms →
    rationalSeparation (left atom.item) (right atom.item) ≤
      envelope atom.item

namespace FiniteContent

/-- A displayed pointwise dominator controls exact finite L1 error. -/
theorem l1Distance_le_integral_of_dominator {α : Type}
    (content : FiniteContent α) (envelope left right : α → Coordinate)
    (dominates : DominatesErrorOn content.atoms envelope left right) :
    content.l1Distance left right ≤ content.integral envelope := by
  apply content.integral_mono
  intro atom member
  exact dominates atom member

/-- Finite dominated convergence estimate, stated without a limit: the
integral separation is bounded by the exact integral of the supplied error
envelope. -/
theorem integral_separation_le_of_dominator {α : Type}
    (content : FiniteContent α) (envelope left right : α → Coordinate)
    (dominates : DominatesErrorOn content.atoms envelope left right) :
    rationalSeparation (content.integral left) (content.integral right) ≤
      content.integral envelope := by
  have l1Bound := content.l1Distance_le_integral_of_dominator
    envelope left right dominates
  have integralBound := content.integral_close_l1 left right
  unfold rationalSeparation
  apply max_le
  · exact integralBound.2.trans l1Bound
  · exact integralBound.1.trans l1Bound

/-- An explicit small dominating integral is an arbitrary-accuracy
certificate for the two displayed finite integrals. -/
theorem integral_separation_lt_of_dominator {α : Type}
    (content : FiniteContent α) (envelope left right : α → Coordinate)
    (dominates : DominatesErrorOn content.atoms envelope left right)
    (epsilon : Coordinate)
    (small : content.integral envelope < epsilon) :
    rationalSeparation (content.integral left) (content.integral right) <
      epsilon :=
  (content.integral_separation_le_of_dominator
    envelope left right dominates).trans_lt small

/-- Packaged finite dominated-approximation data.  The envelope is explicit,
nonnegative on the displayed atoms, and its integral is the complete error
budget. -/
structure IntegralErrorBudget {α : Type} (content : FiniteContent α)
    (candidate target : α → Coordinate) where
  envelope : α → Coordinate
  envelope_nonnegative : ∀ atom, atom ∈ content.atoms →
    0 ≤ envelope atom.item
  dominates : DominatesErrorOn content.atoms envelope candidate target

namespace IntegralErrorBudget

def error {α : Type} {content : FiniteContent α}
    {candidate target : α → Coordinate}
    (budget : IntegralErrorBudget content candidate target) : Coordinate :=
  content.integral budget.envelope

theorem error_nonnegative {α : Type} {content : FiniteContent α}
    {candidate target : α → Coordinate}
    (budget : IntegralErrorBudget content candidate target) :
    0 ≤ budget.error :=
  content.integral_nonneg budget.envelope budget.envelope_nonnegative

theorem integral_separation_le {α : Type} {content : FiniteContent α}
    {candidate target : α → Coordinate}
    (budget : IntegralErrorBudget content candidate target) :
    rationalSeparation (content.integral candidate)
        (content.integral target) ≤ budget.error :=
  content.integral_separation_le_of_dominator
    budget.envelope candidate target budget.dominates

theorem accurate {α : Type} {content : FiniteContent α}
    {candidate target : α → Coordinate}
    (budget : IntegralErrorBudget content candidate target)
    (epsilon : Coordinate) (small : budget.error < epsilon) :
    rationalSeparation (content.integral candidate)
        (content.integral target) < epsilon :=
  budget.integral_separation_le.trans_lt small

end IntegralErrorBudget

/-- A one-sided finite monotone approximation with an explicit residual
budget. -/
structure MonotoneIntegralBudget {α : Type} (content : FiniteContent α)
    (approximation target : α → Coordinate) where
  remainder : α → Coordinate
  remainder_nonnegative : ∀ atom, atom ∈ content.atoms →
    0 ≤ remainder atom.item
  approximation_le : PointwiseLeOn content.atoms approximation target
  gap_le_remainder : ∀ atom, atom ∈ content.atoms →
    target atom.item - approximation atom.item ≤ remainder atom.item

namespace MonotoneIntegralBudget

theorem integral_mono {α : Type} {content : FiniteContent α}
    {approximation target : α → Coordinate}
    (budget : MonotoneIntegralBudget content approximation target) :
    content.integral approximation ≤ content.integral target :=
  content.integral_mono approximation target budget.approximation_le

theorem remainderIntegral_nonnegative {α : Type}
    {content : FiniteContent α} {approximation target : α → Coordinate}
    (budget : MonotoneIntegralBudget content approximation target) :
    0 ≤ content.integral budget.remainder :=
  content.integral_nonneg budget.remainder budget.remainder_nonnegative

theorem integral_gap_le {α : Type} {content : FiniteContent α}
    {approximation target : α → Coordinate}
    (budget : MonotoneIntegralBudget content approximation target) :
    content.integral target - content.integral approximation ≤
      content.integral budget.remainder := by
  have averaged := content.integral_mono
    (fun item => target item - approximation item) budget.remainder
    budget.gap_le_remainder
  rw [content.integral_sub] at averaged
  exact averaged

theorem integral_separation_le {α : Type} {content : FiniteContent α}
    {approximation target : α → Coordinate}
    (budget : MonotoneIntegralBudget content approximation target) :
    rationalSeparation (content.integral approximation)
        (content.integral target) ≤ content.integral budget.remainder := by
  unfold rationalSeparation
  apply max_le
  · exact (sub_nonpos.mpr budget.integral_mono).trans
      budget.remainderIntegral_nonnegative
  · exact budget.integral_gap_le

theorem accurate {α : Type} {content : FiniteContent α}
    {approximation target : α → Coordinate}
    (budget : MonotoneIntegralBudget content approximation target)
    (epsilon : Coordinate)
    (small : content.integral budget.remainder < epsilon) :
    rationalSeparation (content.integral approximation)
        (content.integral target) < epsilon :=
  budget.integral_separation_le.trans_lt small

end MonotoneIntegralBudget

end FiniteContent

end FiniteMeasure
