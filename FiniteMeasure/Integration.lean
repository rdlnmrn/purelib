import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Content

/-!
# Certified finite integration

Integration is a pair of finite rational sums.  Each displayed cell carries a
nonnegative weight and rational lower and upper values.  No function space,
partition limit, supremum, or completed integral is introduced.
-/

namespace FiniteMeasure

/-- One weighted finite cell with a rational range for an integrand. -/
structure IntegrationCell (α : Type) where
  item : α
  weight : Coordinate
  weight_nonnegative : 0 ≤ weight
  lower : Coordinate
  upper : Coordinate
  range_valid : lower ≤ upper

namespace IntegrationCell

/-- A cell on which the displayed integrand value is exact. -/
def exact {α : Type} (item : α) (weight value : Coordinate)
    (weightNonnegative : 0 ≤ weight) : IntegrationCell α where
  item := item
  weight := weight
  weight_nonnegative := weightNonnegative
  lower := value
  upper := value
  range_valid := le_rfl

/-- Rational oscillation of the integrand on one displayed cell. -/
def oscillation {α : Type} (cell : IntegrationCell α) : Coordinate :=
  cell.upper - cell.lower

theorem oscillation_nonneg {α : Type} (cell : IntegrationCell α) :
    0 ≤ cell.oscillation :=
  sub_nonneg.mpr cell.range_valid

end IntegrationCell

/-- Sum of the displayed cell weights. -/
def integrationWeight {α : Type} : List (IntegrationCell α) → Coordinate
  | [] => 0
  | cell :: remaining => cell.weight + integrationWeight remaining

/-- Lower finite integral sum. -/
def lowerIntegral {α : Type} : List (IntegrationCell α) → Coordinate
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.lower + lowerIntegral remaining

/-- Upper finite integral sum. -/
def upperIntegral {α : Type} : List (IntegrationCell α) → Coordinate
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.upper + upperIntegral remaining

/-- The exactly displayed uncertainty in the finite integral. -/
def integralOscillation {α : Type} :
    List (IntegrationCell α) → Coordinate
  | [] => 0
  | cell :: remaining =>
      cell.weight * cell.oscillation + integralOscillation remaining

@[simp] theorem integrationWeight_nil {α : Type} :
    integrationWeight ([] : List (IntegrationCell α)) = 0 := rfl

@[simp] theorem lowerIntegral_nil {α : Type} :
    lowerIntegral ([] : List (IntegrationCell α)) = 0 := rfl

@[simp] theorem upperIntegral_nil {α : Type} :
    upperIntegral ([] : List (IntegrationCell α)) = 0 := rfl

@[simp] theorem integralOscillation_nil {α : Type} :
    integralOscillation ([] : List (IntegrationCell α)) = 0 := rfl

theorem integrationWeight_nonneg {α : Type} :
    ∀ cells : List (IntegrationCell α), 0 ≤ integrationWeight cells
  | [] => le_rfl
  | cell :: remaining =>
      add_nonneg cell.weight_nonnegative
        (integrationWeight_nonneg remaining)

theorem integralOscillation_nonneg {α : Type} :
    ∀ cells : List (IntegrationCell α), 0 ≤ integralOscillation cells
  | [] => le_rfl
  | cell :: remaining =>
      add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          cell.weight_nonnegative cell.oscillation_nonneg)
        (integralOscillation_nonneg remaining)

theorem upperIntegral_eq_lower_add_oscillation {α : Type} :
    ∀ cells : List (IntegrationCell α),
      upperIntegral cells = lowerIntegral cells + integralOscillation cells
  | [] => by
      simp only [upperIntegral_nil, lowerIntegral_nil,
        integralOscillation_nil, add_zero]
  | cell :: remaining => by
      have inductionHypothesis :=
        upperIntegral_eq_lower_add_oscillation remaining
      dsimp only [upperIntegral, lowerIntegral, integralOscillation,
        IntegrationCell.oscillation]
      rw [inductionHypothesis]
      ring1

theorem lowerIntegral_le_upperIntegral {α : Type}
    (cells : List (IntegrationCell α)) :
    lowerIntegral cells ≤ upperIntegral cells := by
  rw [upperIntegral_eq_lower_add_oscillation]
  exact le_add_of_nonneg_right (integralOscillation_nonneg cells)

/-- Certified finite lower and upper integral sums. -/
def integralBound {α : Type} (cells : List (IntegrationCell α)) : Bound where
  lower := lowerIntegral cells
  upper := upperIntegral cells
  valid := lowerIntegral_le_upperIntegral cells

theorem integralBound_width {α : Type}
    (cells : List (IntegrationCell α)) :
    (integralBound cells).width = integralOscillation cells := by
  dsimp only [Bound.width, integralBound]
  rw [upperIntegral_eq_lower_add_oscillation]
  ring1

theorem integrationWeight_append {α : Type}
    (left right : List (IntegrationCell α)) :
    integrationWeight (left ++ right) =
      integrationWeight left + integrationWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, integrationWeight_nil, zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, integrationWeight, inductionHypothesis]
      ring1

theorem lowerIntegral_append {α : Type}
    (left right : List (IntegrationCell α)) :
    lowerIntegral (left ++ right) =
      lowerIntegral left + lowerIntegral right := by
  induction left with
  | nil => simp only [List.nil_append, lowerIntegral_nil, zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, lowerIntegral, inductionHypothesis]
      ring1

theorem upperIntegral_append {α : Type}
    (left right : List (IntegrationCell α)) :
    upperIntegral (left ++ right) =
      upperIntegral left + upperIntegral right := by
  induction left with
  | nil => simp only [List.nil_append, upperIntegral_nil, zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, upperIntegral, inductionHypothesis]
      ring1

theorem integralOscillation_append {α : Type}
    (left right : List (IntegrationCell α)) :
    integralOscillation (left ++ right) =
      integralOscillation left + integralOscillation right := by
  induction left with
  | nil => simp only [List.nil_append, integralOscillation_nil, zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, integralOscillation, inductionHypothesis]
      ring1

theorem integralBound_append {α : Type}
    (left right : List (IntegrationCell α)) :
    integralBound (left ++ right) =
      (integralBound left).add (integralBound right) := by
  apply Bound.ext
  · exact lowerIntegral_append left right
  · exact upperIntegral_append left right

/-- Exact finite weighted evaluation of a displayed function. -/
def weightedEvaluation {α : Type} (value : α → Coordinate) :
    List (IntegrationCell α) → Coordinate
  | [] => 0
  | cell :: remaining =>
      cell.weight * value cell.item + weightedEvaluation value remaining

/-- If every displayed value meets its cell range, the exact finite weighted
evaluation lies in the certified integral enclosure. -/
theorem weightedEvaluation_mem_integralBound
    {α : Type} (value : α → Coordinate) :
    ∀ {cells : List (IntegrationCell α)},
      (∀ cell, cell ∈ cells →
        cell.lower ≤ value cell.item ∧ value cell.item ≤ cell.upper) →
      (integralBound cells).Contains (weightedEvaluation value cells)
  | [], _ => ⟨le_rfl, le_rfl⟩
  | cell :: remaining, ranges => by
      have head := ranges cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.lower ≤ value candidate.item ∧
            value candidate.item ≤ candidate.upper :=
        fun candidate member =>
          ranges candidate (List.mem_cons_of_mem cell member)
      have inductionHypothesis :=
        weightedEvaluation_mem_integralBound value tail
      constructor
      · dsimp only [integralBound, lowerIntegral, weightedEvaluation]
        exact add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            head.1 cell.weight_nonnegative)
          inductionHypothesis.1
      · dsimp only [integralBound, upperIntegral, weightedEvaluation]
        exact add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            head.2 cell.weight_nonnegative)
          inductionHypothesis.2

/-- A uniform rational cell-oscillation estimate bounds the entire finite
integral uncertainty by total weight times that estimate. -/
theorem integralOscillation_le_weight_mul
    {α : Type} {delta : Coordinate} (deltaNonnegative : 0 ≤ delta) :
    ∀ {cells : List (IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.oscillation ≤ delta) →
      integralOscillation cells ≤ integrationWeight cells * delta
  | [], _ => by
      simp only [integralOscillation_nil, integrationWeight_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, bounded => by
      have head := bounded cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.oscillation ≤ delta :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled :=
        integralOscillation_le_weight_mul deltaNonnegative tail
      dsimp only [integralOscillation, integrationWeight]
      calc
        cell.weight * cell.oscillation + integralOscillation remaining ≤
            cell.weight * delta + integrationWeight remaining * delta :=
          add_le_add headScaled tailScaled
        _ = (cell.weight + integrationWeight remaining) * delta := by ring1

/-- A finite uniform oscillation calculation meets a requested integral
accuracy whenever its displayed rational budget does. -/
theorem integralBound_width_lt_of_uniform
    {α : Type} {cells : List (IntegrationCell α)}
    {delta epsilon : Coordinate} (deltaNonnegative : 0 ≤ delta)
    (bounded : ∀ cell, cell ∈ cells → cell.oscillation ≤ delta)
    (budget : integrationWeight cells * delta < epsilon) :
    (integralBound cells).width < epsilon := by
  rw [integralBound_width]
  exact (integralOscillation_le_weight_mul deltaNonnegative bounded).trans_lt
    budget

/-! ## Certified finite subdivision -/

/-- Finite subdivision of one integration cell.  Child weights conserve the
parent weight and every child integrand range lies inside the parent range. -/
structure IntegrationSplit {α : Type} (parent : IntegrationCell α) where
  children : List (IntegrationCell α)
  weight_conserved : integrationWeight children = parent.weight
  lower_refines : ∀ child, child ∈ children → parent.lower ≤ child.lower
  upper_refines : ∀ child, child ∈ children → child.upper ≤ parent.upper

private theorem weight_mul_lower_le_lowerIntegral
    {α : Type} (baseline : Coordinate) :
    ∀ {cells : List (IntegrationCell α)},
      (∀ cell, cell ∈ cells → baseline ≤ cell.lower) →
      integrationWeight cells * baseline ≤ lowerIntegral cells
  | [], _ => by
      simp only [integrationWeight_nil, lowerIntegral_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, lowerBounds => by
      have head := lowerBounds cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          baseline ≤ candidate.lower :=
        fun candidate member =>
          lowerBounds candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled := weight_mul_lower_le_lowerIntegral baseline tail
      dsimp only [integrationWeight, lowerIntegral]
      calc
        (cell.weight + integrationWeight remaining) * baseline =
            cell.weight * baseline +
              integrationWeight remaining * baseline := by ring1
        _ ≤ cell.weight * cell.lower + lowerIntegral remaining :=
          add_le_add headScaled tailScaled

private theorem upperIntegral_le_weight_mul
    {α : Type} (ceiling : Coordinate) :
    ∀ {cells : List (IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.upper ≤ ceiling) →
      upperIntegral cells ≤ integrationWeight cells * ceiling
  | [], _ => by
      simp only [upperIntegral_nil, integrationWeight_nil, zero_mul]
      exact le_rfl
  | cell :: remaining, upperBounds => by
      have head := upperBounds cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.upper ≤ ceiling :=
        fun candidate member =>
          upperBounds candidate (List.mem_cons_of_mem cell member)
      have headScaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          head cell.weight_nonnegative
      have tailScaled := upperIntegral_le_weight_mul ceiling tail
      dsimp only [upperIntegral, integrationWeight]
      calc
        cell.weight * cell.upper + upperIntegral remaining ≤
            cell.weight * ceiling +
              integrationWeight remaining * ceiling :=
          add_le_add headScaled tailScaled
        _ = (cell.weight + integrationWeight remaining) * ceiling := by
          ring1

/-- A certified finite subdivision raises the lower sum and lowers the upper
sum. -/
theorem IntegrationSplit.integralBound_refines
    {α : Type} {parent : IntegrationCell α}
    (split : IntegrationSplit parent) :
    Bound.Refines (integralBound split.children) (integralBound [parent]) := by
  constructor
  · dsimp only [integralBound, lowerIntegral]
    have lower := weight_mul_lower_le_lowerIntegral parent.lower
      split.lower_refines
    rw [split.weight_conserved] at lower
    simpa only [add_zero] using lower
  · dsimp only [integralBound, upperIntegral]
    have upper := upperIntegral_le_weight_mul parent.upper
      split.upper_refines
    rw [split.weight_conserved] at upper
    simpa only [add_zero] using upper

/-- Subdividing one cell inside an arbitrary finite integration frontier
narrows the complete integral enclosure. -/
theorem IntegrationSplit.frontier_integralBound_refines
    {α : Type} {parent : IntegrationCell α}
    (split : IntegrationSplit parent)
    (before after : List (IntegrationCell α)) :
    Bound.Refines
      (integralBound (before ++ split.children ++ after))
      (integralBound (before ++ [parent] ++ after)) := by
  have middle := split.integralBound_refines
  have withAfter := Bound.Refines.add middle
    (Bound.Refines.refl (integralBound after))
  have complete := Bound.Refines.add
    (Bound.Refines.refl (integralBound before)) withAfter
  rw [List.append_assoc, List.append_assoc]
  rw [integralBound_append before (split.children ++ after),
    integralBound_append split.children after,
    integralBound_append before ([parent] ++ after),
    integralBound_append [parent] after]
  exact complete

/-! ## Finite integration-refinement histories -/

/-- Constructively generated finite integration refinement, closed under a
single displayed subdivision and finite composition. -/
inductive IntegrationFrontierRefines {α : Type} :
    List (IntegrationCell α) → List (IntegrationCell α) → Prop where
  | refl (frontier : List (IntegrationCell α)) :
      IntegrationFrontierRefines frontier frontier
  | split (before after : List (IntegrationCell α))
      (parent : IntegrationCell α) (children : IntegrationSplit parent) :
      IntegrationFrontierRefines
        (before ++ children.children ++ after)
        (before ++ [parent] ++ after)
  | trans {inner middle outer : List (IntegrationCell α)} :
      IntegrationFrontierRefines inner middle →
      IntegrationFrontierRefines middle outer →
      IntegrationFrontierRefines inner outer

namespace IntegrationFrontierRefines

/-- Every generated finite subdivision narrows the lower/upper integral
enclosure. -/
theorem integralBound_refines {α : Type}
    {inner outer : List (IntegrationCell α)}
    (refines : IntegrationFrontierRefines inner outer) :
    Bound.Refines (integralBound inner) (integralBound outer) := by
  induction refines with
  | refl frontier => exact Bound.Refines.refl _
  | split before after parent children =>
      exact children.frontier_integralBound_refines before after
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

theorem lower_mono {α : Type}
    {inner outer : List (IntegrationCell α)}
    (refines : IntegrationFrontierRefines inner outer) :
    lowerIntegral outer ≤ lowerIntegral inner :=
  refines.integralBound_refines.lower

theorem upper_antitone {α : Type}
    {inner outer : List (IntegrationCell α)}
    (refines : IntegrationFrontierRefines inner outer) :
    upperIntegral inner ≤ upperIntegral outer :=
  refines.integralBound_refines.upper

/-- Displayed integral uncertainty cannot increase under finite
subdivision. -/
theorem oscillation_le {α : Type}
    {inner outer : List (IntegrationCell α)}
    (refines : IntegrationFrontierRefines inner outer) :
    integralOscillation inner ≤ integralOscillation outer := by
  rw [← integralBound_width, ← integralBound_width]
  exact refines.integralBound_refines.width_le

private theorem integrationWeight_context_split
    {α : Type} (before after : List (IntegrationCell α))
    (parent : IntegrationCell α) (children : IntegrationSplit parent) :
    integrationWeight (before ++ children.children ++ after) =
      integrationWeight (before ++ [parent] ++ after) := by
  rw [List.append_assoc, List.append_assoc]
  rw [integrationWeight_append before (children.children ++ after),
    integrationWeight_append children.children after,
    integrationWeight_append before ([parent] ++ after),
    integrationWeight_append [parent] after]
  simp only [integrationWeight, add_zero]
  rw [children.weight_conserved]

/-- Finite subdivision redistributes but never creates or destroys
integration weight. -/
theorem weight_conserved {α : Type}
    {inner outer : List (IntegrationCell α)}
    (refines : IntegrationFrontierRefines inner outer) :
    integrationWeight inner = integrationWeight outer := by
  induction refines with
  | refl frontier => rfl
  | split before after parent children =>
      exact integrationWeight_context_split before after parent children
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

end IntegrationFrontierRefines

private theorem integralOscillation_eq_zero_of_exact {α : Type} :
    ∀ {cells : List (IntegrationCell α)},
      (∀ cell, cell ∈ cells → cell.lower = cell.upper) →
      integralOscillation cells = 0
  | [], _ => rfl
  | cell :: remaining, exactRanges => by
      have head := exactRanges cell List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          candidate.lower = candidate.upper :=
        fun candidate member =>
          exactRanges candidate (List.mem_cons_of_mem cell member)
      dsimp only [integralOscillation, IntegrationCell.oscillation]
      rw [head, sub_self, mul_zero, zero_add,
        integralOscillation_eq_zero_of_exact tail]

/-- Exact simple functions have zero finite integration uncertainty. -/
theorem integralBound_exact_width
    {α : Type} (entries : List (Weighted (α × Coordinate))) :
    (integralBound (entries.map fun entry =>
      IntegrationCell.exact entry.item.1 entry.weight entry.item.2
        entry.nonnegative)).width = 0 := by
  rw [integralBound_width]
  apply integralOscillation_eq_zero_of_exact
  intro cell member
  simp only [QuotientFreeList.mem_map] at member
  rcases member with ⟨entry, sourceMember, equal⟩
  rw [← equal]
  rfl

end FiniteMeasure
