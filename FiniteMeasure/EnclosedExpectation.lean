import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Stochastic
import FiniteMeasure.Mixture
import FiniteMeasure.Protocol

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace FiniteMeasure

namespace Distribution

/-- Integration cells obtained from one rational enclosure at every payload
of a finite distribution. -/
def enclosureCells {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) : List (IntegrationCell α) :=
  distribution.atoms.map fun atom =>
    { item := atom.item
      weight := atom.weight
      weight_nonnegative := atom.nonnegative
      lower := (ranges atom.item).lower
      upper := (ranges atom.item).upper
      range_valid := (ranges atom.item).valid }

/-- The finite rational expectation enclosure induced by pointwise rational
enclosures. -/
def enclosedExpectation {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) : Bound :=
  integralBound (distribution.enclosureCells ranges)

theorem lowerIntegral_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    lowerIntegral (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).lower) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, lowerIntegral, expectationWeight,
        inductionHypothesis]

theorem upperIntegral_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    upperIntegral (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).upper) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, upperIntegral, expectationWeight,
        inductionHypothesis]

theorem integralOscillation_enclosureCells {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    integralOscillation (distribution.enclosureCells ranges) =
      distribution.expectation (fun item => (ranges item).width) := by
  unfold enclosureCells expectation
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, integralOscillation, expectationWeight,
        IntegrationCell.oscillation, Bound.width, inductionHypothesis]

theorem enclosedExpectation_lower {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    (distribution.enclosedExpectation ranges).lower =
      distribution.expectation (fun item => (ranges item).lower) :=
  distribution.lowerIntegral_enclosureCells ranges

theorem enclosedExpectation_upper {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    (distribution.enclosedExpectation ranges).upper =
      distribution.expectation (fun item => (ranges item).upper) :=
  distribution.upperIntegral_enclosureCells ranges

/-- The expectation enclosure's uncertainty is exactly the probability-
weighted average of all displayed pointwise widths. -/
theorem enclosedExpectation_width {α : Type}
    (distribution : Distribution α) (ranges : α → Bound) :
    (distribution.enclosedExpectation ranges).width =
      distribution.expectation (fun item => (ranges item).width) := by
  unfold enclosedExpectation
  rw [integralBound_width,
    distribution.integralOscillation_enclosureCells]

/-- A one-row finite law simply returns that row's displayed enclosure. -/
theorem enclosedExpectation_pure {α : Type} (item : α)
    (ranges : α → Bound) :
    (Distribution.pure item).enclosedExpectation ranges = ranges item := by
  apply Bound.ext
  · rw [enclosedExpectation_lower, Distribution.pure_expectation]
  · rw [enclosedExpectation_upper, Distribution.pure_expectation]

/-- Pushforward of a finite law transports pointwise enclosures by ordinary
function composition. -/
theorem enclosedExpectation_map {α β : Type}
    (source : Distribution α) (function : α → β) (ranges : β → Bound) :
    (source.map function).enclosedExpectation ranges =
      source.enclosedExpectation (fun item => ranges (function item)) := by
  apply Bound.ext
  · rw [enclosedExpectation_lower, source.map_expectation,
      enclosedExpectation_lower]
  · rw [enclosedExpectation_upper, source.map_expectation,
      enclosedExpectation_upper]

/-- Exact finite enclosure tower law.  Enclose each transition expectation,
then enclose their source expectation; this is the same rational bound as
flattening the finite transition table first. -/
theorem enclosedExpectation_bind {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (ranges : β → Bound) :
    (source.bind transition).enclosedExpectation ranges =
      source.enclosedExpectation (fun item =>
        (transition item).enclosedExpectation ranges) := by
  apply Bound.ext
  · rw [(source.bind transition).enclosedExpectation_lower,
      source.bind_expectation, source.enclosedExpectation_lower]
    exact source.expectation_congr _ _ (fun item =>
      ((transition item).enclosedExpectation_lower ranges).symm)
  · rw [(source.bind transition).enclosedExpectation_upper,
      source.bind_expectation, source.enclosedExpectation_upper]
    exact source.expectation_congr _ _ (fun item =>
      ((transition item).enclosedExpectation_upper ranges).symm)

/-- Finite product/Fubini law for rational expectation enclosures. -/
theorem enclosedExpectation_product {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (ranges : α × β → Bound) :
    (left.product right).enclosedExpectation ranges =
      left.enclosedExpectation (fun leftItem =>
        right.enclosedExpectation (fun rightItem =>
          ranges (leftItem, rightItem))) := by
  apply Bound.ext
  · rw [enclosedExpectation_lower, left.product_expectation_iterated,
      enclosedExpectation_lower]
    exact left.expectation_congr _ _ (fun item =>
      (right.enclosedExpectation_lower
        (fun rightItem => ranges (item, rightItem))).symm)
  · rw [enclosedExpectation_upper, left.product_expectation_iterated,
      enclosedExpectation_upper]
    exact left.expectation_congr _ _ (fun item =>
      (right.enclosedExpectation_upper
        (fun rightItem => ranges (item, rightItem))).symm)

/-- A rational mixture of laws gives the correspondingly scaled sum of
their expectation enclosures. -/
theorem enclosedExpectation_mixture {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (ranges : α → Bound) :
    (left.mixture right weight).enclosedExpectation ranges =
      ((left.enclosedExpectation ranges).scale
        weight.coefficient weight.nonnegative).add
      ((right.enclosedExpectation ranges).scale
        weight.complement weight.complement_nonnegative) := by
  apply Bound.ext
  · rw [enclosedExpectation_lower,
      left.mixture_expectation right weight]
    change weight.coefficient * left.expectation (fun item =>
        (ranges item).lower) +
      weight.complement * right.expectation (fun item =>
        (ranges item).lower) =
      weight.coefficient * (left.enclosedExpectation ranges).lower +
        weight.complement * (right.enclosedExpectation ranges).lower
    rw [left.enclosedExpectation_lower, right.enclosedExpectation_lower]
  · rw [enclosedExpectation_upper,
      left.mixture_expectation right weight]
    change weight.coefficient * left.expectation (fun item =>
        (ranges item).upper) +
      weight.complement * right.expectation (fun item =>
        (ranges item).upper) =
      weight.coefficient * (left.enclosedExpectation ranges).upper +
        weight.complement * (right.enclosedExpectation ranges).upper
    rw [left.enclosedExpectation_upper, right.enclosedExpectation_upper]

/-- Under finite bind, total enclosure width is the exact source expectation
of the transition-level enclosure widths. -/
theorem enclosedExpectation_bind_width {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (ranges : β → Bound) :
    ((source.bind transition).enclosedExpectation ranges).width =
      source.expectation (fun item =>
        ((transition item).enclosedExpectation ranges).width) := by
  rw [enclosedExpectation_width, source.bind_expectation]
  exact source.expectation_congr _ _ (fun item =>
    ((transition item).enclosedExpectation_width ranges).symm)

theorem enclosedExpectation_mixture_width {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (ranges : α → Bound) :
    ((left.mixture right weight).enclosedExpectation ranges).width =
      weight.coefficient * (left.enclosedExpectation ranges).width +
        weight.complement * (right.enclosedExpectation ranges).width := by
  rw [enclosedExpectation_mixture, Bound.add_width,
    Bound.scale_width, Bound.scale_width]

/-- Pointwise addition of rational enclosures commutes exactly with finite
expectation. -/
theorem enclosedExpectation_add {α : Type}
    (distribution : Distribution α) (left right : α → Bound) :
    distribution.enclosedExpectation (fun item =>
        (left item).add (right item)) =
      (distribution.enclosedExpectation left).add
        (distribution.enclosedExpectation right) := by
  apply Bound.ext
  · rw [distribution.enclosedExpectation_lower]
    change distribution.expectation (fun item =>
        (left item).lower + (right item).lower) =
      (distribution.enclosedExpectation left).lower +
        (distribution.enclosedExpectation right).lower
    rw [distribution.expectation_add,
      distribution.enclosedExpectation_lower,
      distribution.enclosedExpectation_lower]
  · rw [distribution.enclosedExpectation_upper]
    change distribution.expectation (fun item =>
        (left item).upper + (right item).upper) =
      (distribution.enclosedExpectation left).upper +
        (distribution.enclosedExpectation right).upper
    rw [distribution.expectation_add,
      distribution.enclosedExpectation_upper,
      distribution.enclosedExpectation_upper]

/-- Pointwise multiplication by a displayed nonnegative rational commutes
exactly with finite expectation enclosure. -/
theorem enclosedExpectation_scale {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) (ranges : α → Bound) :
    distribution.enclosedExpectation (fun item =>
        (ranges item).scale factor nonnegative) =
      (distribution.enclosedExpectation ranges).scale
        factor nonnegative := by
  apply Bound.ext
  · rw [distribution.enclosedExpectation_lower]
    change distribution.expectation (fun item =>
        factor * (ranges item).lower) =
      factor * (distribution.enclosedExpectation ranges).lower
    rw [distribution.expectation_scale,
      distribution.enclosedExpectation_lower]
  · rw [distribution.enclosedExpectation_upper]
    change distribution.expectation (fun item =>
        factor * (ranges item).upper) =
      factor * (distribution.enclosedExpectation ranges).upper
    rw [distribution.expectation_scale,
      distribution.enclosedExpectation_upper]

theorem enclosedExpectation_add_width {α : Type}
    (distribution : Distribution α) (left right : α → Bound) :
    (distribution.enclosedExpectation (fun item =>
      (left item).add (right item))).width =
        (distribution.enclosedExpectation left).width +
          (distribution.enclosedExpectation right).width := by
  rw [distribution.enclosedExpectation_add, Bound.add_width]

theorem enclosedExpectation_scale_width {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) (ranges : α → Bound) :
    (distribution.enclosedExpectation (fun item =>
      (ranges item).scale factor nonnegative)).width =
        factor * (distribution.enclosedExpectation ranges).width := by
  rw [distribution.enclosedExpectation_scale, Bound.scale_width]

/-- Any rational observable certified inside every relevant pointwise
enclosure has its exact finite expectation inside the induced enclosure. -/
theorem expectation_mem_enclosedExpectation {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (distribution.enclosedExpectation ranges).Contains
      (distribution.expectation value) := by
  rw [Bound.Contains, distribution.enclosedExpectation_lower,
    distribution.enclosedExpectation_upper]
  exact ⟨distribution.expectation_mono
      (fun item => (ranges item).lower) value
      (fun atom member => (inside atom member).1),
    distribution.expectation_mono value
      (fun item => (ranges item).upper)
      (fun atom member => (inside atom member).2)⟩

/-- Pointwise finite refinement propagates monotonically through a finite
expectation enclosure. -/
theorem enclosedExpectation_refines {α : Type}
    (distribution : Distribution α) (inner outer : α → Bound)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Bound.Refines (inner atom.item) (outer atom.item)) :
    Bound.Refines (distribution.enclosedExpectation inner)
      (distribution.enclosedExpectation outer) := by
  constructor
  · rw [distribution.enclosedExpectation_lower,
      distribution.enclosedExpectation_lower]
    exact distribution.expectation_mono
      (fun item => (outer item).lower)
      (fun item => (inner item).lower)
      (fun atom member => (refines atom member).lower)
  · rw [distribution.enclosedExpectation_upper,
      distribution.enclosedExpectation_upper]
    exact distribution.expectation_mono
      (fun item => (inner item).upper)
      (fun item => (outer item).upper)
      (fun atom member => (refines atom member).upper)

/-- Exact pointwise rational data induces a zero-width exact expectation. -/
theorem enclosedExpectation_exact {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.enclosedExpectation (fun item => Bound.exact (value item)) =
      Bound.exact (distribution.expectation value) := by
  apply Bound.ext
  · rw [distribution.enclosedExpectation_lower]
    rfl
  · rw [distribution.enclosedExpectation_upper]
    rfl

/-- A uniform displayed pointwise width bounds the complete finite
expectation uncertainty by the same rational allowance. -/
theorem enclosedExpectation_width_le_of_uniform {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (allowance : Coordinate)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).width ≤ allowance) :
    (distribution.enclosedExpectation ranges).width ≤ allowance := by
  rw [distribution.enclosedExpectation_width]
  calc
    distribution.expectation (fun item => (ranges item).width) ≤
        distribution.expectation (fun _ => allowance) :=
      distribution.expectation_mono _ _ bounded
    _ = allowance := distribution.expectation_constant allowance

theorem enclosedExpectation_width_lt_of_uniform {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (allowance epsilon : Coordinate)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).width ≤ allowance)
    (budget : allowance < epsilon) :
    (distribution.enclosedExpectation ranges).width < epsilon :=
  (distribution.enclosedExpectation_width_le_of_uniform
    ranges allowance bounded).trans_lt budget

end Distribution

/-! ## Lifting pointwise finite requests through expectation -/

/-- An executable family of pointwise rational enclosures over one fixed
finite distribution.  Each request sharpens all displayed atoms to the
supplied rational width.  Only individual finite states and requests exist. -/
structure PointwiseEnclosureProcess {α : Type}
    (distribution : Distribution α) where
  State : Type
  ranges : State → α → Bound
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive atom,
    atom ∈ distribution.atoms →
      Bound.Refines
        (ranges (request state epsilon positive) atom.item)
        (ranges state atom.item)
  accurate : ∀ state epsilon positive atom,
    atom ∈ distribution.atoms →
      (ranges (request state epsilon positive) atom.item).width ≤ epsilon
  refinesInitial : ∀ state atom, atom ∈ distribution.atoms →
    Bound.Refines (ranges state atom.item) (ranges initial atom.item)

namespace PointwiseEnclosureProcess

private theorem half_lt_self
    {epsilon : Coordinate} (positive : 0 < epsilon) :
    epsilon / 2 < epsilon := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    epsilon = epsilon * 1 := by ring1
    _ < epsilon * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

/-- Pointwise finite requests induce a finite rational bound process for the
expectation.  Half of each requested budget is used pointwise, leaving an
explicit strict margin for the resulting expectation enclosure. -/
def toExpectationBoundProcess {α : Type} {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution) : BoundProcess where
  State := process.State
  bound state := distribution.enclosedExpectation (process.ranges state)
  initial := process.initial
  request state epsilon positive :=
    process.request state (epsilon / 2)
      (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
  request_refines state epsilon positive := by
    apply distribution.enclosedExpectation_refines
    intro atom member
    exact process.request_refines state (epsilon / 2)
      (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
      atom member
  accurate state epsilon positive := by
    apply distribution.enclosedExpectation_width_lt_of_uniform
      (process.ranges (process.request state (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))))
      (epsilon / 2) epsilon
    · intro atom member
      exact process.accurate state (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))
        atom member
    · exact half_lt_self positive
  refinesInitial state := by
    apply distribution.enclosedExpectation_refines
    exact process.refinesInitial state

theorem expectation_mem {α : Type} {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (state : process.State) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item)) :
    (process.toExpectationBoundProcess.bound state).Contains
      (distribution.expectation value) :=
  distribution.expectation_mem_enclosedExpectation
    (process.ranges state) value inside

/-- One finite request returns a rational representative within the supplied
tolerance of every admitted rational expectation. -/
theorem candidate_close_to_approximation {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    {candidate : Coordinate}
    (inside :
      (process.toExpectationBoundProcess.bound
        (process.toExpectationBoundProcess.request state epsilon positive)).Contains
          candidate) :
    candidate - process.toExpectationBoundProcess.approximate
        state epsilon positive < epsilon ∧
      process.toExpectationBoundProcess.approximate
        state epsilon positive - candidate < epsilon :=
  process.toExpectationBoundProcess.candidate_close_to_approximate
    state epsilon positive inside

end PointwiseEnclosureProcess

end FiniteMeasure
