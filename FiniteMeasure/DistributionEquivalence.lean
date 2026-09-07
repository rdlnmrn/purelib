import FiniteMeasure.Stochastic
import FiniteMeasure.Mixture

/-!
# Evaluation equivalence of finite distributions

Finite atom tables are retained as executable data, so harmless differences
in ordering or duplicated payloads need not be quotiented away.  Instead, two
tables are equivalent when every executable Boolean event and every rational
observable gives the same exact result.
-/

namespace FiniteMeasure

namespace Distribution

/-- Constructive observational equality of two displayed finite rational
distributions. -/
structure EvaluationEquivalent {α : Type}
    (left right : Distribution α) : Prop where
  probability_eq : ∀ event : α → Bool,
    left.probability event = right.probability event
  expectation_eq : ∀ value : α → Coordinate,
    left.expectation value = right.expectation value

namespace EvaluationEquivalent

/-- Equality of every rational expectation already supplies event equality,
because executable event probabilities are indicator expectations. -/
theorem of_expectation_eq {α : Type} {left right : Distribution α}
    (expectationEqual : ∀ value : α → Coordinate,
      left.expectation value = right.expectation value) :
    EvaluationEquivalent left right where
  probability_eq event := by
    rw [← left.expectation_indicator event,
      ← right.expectation_indicator event]
    exact expectationEqual _
  expectation_eq := expectationEqual

theorem refl {α : Type} (distribution : Distribution α) :
    EvaluationEquivalent distribution distribution where
  probability_eq _ := rfl
  expectation_eq _ := rfl

theorem symm {α : Type} {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right) :
    EvaluationEquivalent right left where
  probability_eq event := (equivalent.probability_eq event).symm
  expectation_eq value := (equivalent.expectation_eq value).symm

theorem trans {α : Type} {first second third : Distribution α}
    (left : EvaluationEquivalent first second)
    (right : EvaluationEquivalent second third) :
    EvaluationEquivalent first third where
  probability_eq event :=
    (left.probability_eq event).trans (right.probability_eq event)
  expectation_eq value :=
    (left.expectation_eq value).trans (right.expectation_eq value)

/-- Evaluation equivalence is preserved by an exact finite pushforward. -/
theorem map {α β : Type} {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right) (function : α → β) :
    EvaluationEquivalent (left.map function) (right.map function) where
  probability_eq event := by
    rw [left.map_probability, right.map_probability]
    exact equivalent.probability_eq _
  expectation_eq value := by
    rw [left.map_expectation, right.map_expectation]
    exact equivalent.expectation_eq _

/-- Finite bind respects equivalent sources and pointwise equivalent
transition tables. -/
theorem bind {α β : Type} {leftSource rightSource : Distribution α}
    (sourceEquivalent : EvaluationEquivalent leftSource rightSource)
    {leftTransition rightTransition : α → Distribution β}
    (transitionEquivalent : ∀ item,
      EvaluationEquivalent (leftTransition item) (rightTransition item)) :
    EvaluationEquivalent (leftSource.bind leftTransition)
      (rightSource.bind rightTransition) where
  probability_eq event := by
    rw [leftSource.bind_probability, rightSource.bind_probability]
    calc
      leftSource.expectation (fun item =>
            (leftTransition item).probability event) =
          leftSource.expectation (fun item =>
            (rightTransition item).probability event) :=
        leftSource.expectation_congr _ _ (fun item =>
          (transitionEquivalent item).probability_eq event)
      _ = rightSource.expectation (fun item =>
            (rightTransition item).probability event) :=
        sourceEquivalent.expectation_eq _

  expectation_eq value := by
    rw [leftSource.bind_expectation, rightSource.bind_expectation]
    calc
      leftSource.expectation (fun item =>
            (leftTransition item).expectation value) =
          leftSource.expectation (fun item =>
            (rightTransition item).expectation value) :=
        leftSource.expectation_congr _ _ (fun item =>
          (transitionEquivalent item).expectation_eq value)
      _ = rightSource.expectation (fun item =>
            (rightTransition item).expectation value) :=
        sourceEquivalent.expectation_eq _

/-- Products preserve evaluation equivalence in both displayed components. -/
theorem product {α β : Type}
    {leftFirst leftSecond : Distribution α}
    {rightFirst rightSecond : Distribution β}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    EvaluationEquivalent (leftFirst.product rightFirst)
      (leftSecond.product rightSecond) := by
  unfold Distribution.product
  apply leftEquivalent.bind
  intro leftItem
  exact rightEquivalent.map fun rightItem => (leftItem, rightItem)

/-- Rational mixtures preserve evaluation equivalence componentwise. -/
theorem mixture {α : Type}
    {leftFirst leftSecond rightFirst rightSecond : Distribution α}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond)
    (weight : MixingWeight) :
    EvaluationEquivalent (leftFirst.mixture rightFirst weight)
      (leftSecond.mixture rightSecond weight) where
  probability_eq event := by
    rw [leftFirst.mixture_probability rightFirst weight,
      leftSecond.mixture_probability rightSecond weight,
      leftEquivalent.probability_eq event,
      rightEquivalent.probability_eq event]
  expectation_eq value := by
    rw [leftFirst.mixture_expectation rightFirst weight,
      leftSecond.mixture_expectation rightSecond weight,
      leftEquivalent.expectation_eq value,
      rightEquivalent.expectation_eq value]

/-- Exact variance depends only on finite rational evaluations, not on the
layout of the displayed atom table. -/
theorem variance_eq {α : Type} {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.variance value = right.variance value := by
  rw [left.variance_eq_secondMoment_sub_sq,
    right.variance_eq_secondMoment_sub_sq,
    equivalent.expectation_eq (fun item => value item ^ 2),
    equivalent.expectation_eq value]

/-- Exact covariance is likewise invariant under evaluation equivalence. -/
theorem covariance_eq {α : Type} {left right : Distribution α}
    (equivalent : EvaluationEquivalent left right)
    (leftValue rightValue : α → Coordinate) :
    left.covariance leftValue rightValue =
      right.covariance leftValue rightValue := by
  rw [left.covariance_eq_productMoment_sub_means,
    right.covariance_eq_productMoment_sub_means,
    equivalent.expectation_eq
      (fun item => leftValue item * rightValue item),
    equivalent.expectation_eq leftValue,
    equivalent.expectation_eq rightValue]

end EvaluationEquivalent

/-- Mapping by the identity function preserves all finite evaluations. -/
theorem map_id_evaluationEquivalent {α : Type}
    (source : Distribution α) :
    EvaluationEquivalent (source.map fun item => item) source where
  probability_eq event := by rw [source.map_probability]
  expectation_eq value := by rw [source.map_expectation]

/-- Two successive finite pushforwards agree observationally with their
displayed composition. -/
theorem map_map_evaluationEquivalent {α β γ : Type}
    (source : Distribution α) (first : α → β) (second : β → γ) :
    EvaluationEquivalent ((source.map first).map second)
      (source.map fun item => second (first item)) where
  probability_eq event := by
    rw [(source.map first).map_probability,
      source.map_probability, source.map_probability]
  expectation_eq value := by
    rw [(source.map first).map_expectation,
      source.map_expectation, source.map_expectation]

/-- Pushing every atom to one displayed payload is observationally the same
as the one-atom deterministic distribution. -/
theorem map_const_evaluationEquivalent {α β : Type}
    (source : Distribution α) (constant : β) :
    EvaluationEquivalent (source.map fun _ => constant)
      (Distribution.pure constant) := by
  apply EvaluationEquivalent.of_expectation_eq
  intro value
  rw [source.map_expectation, source.expectation_constant,
    pure_expectation]

/-- Binding a deterministic source evaluates exactly as the selected finite
transition table. -/
theorem pure_bind_evaluationEquivalent {α β : Type} (item : α)
    (transition : α → Distribution β) :
    EvaluationEquivalent ((Distribution.pure item).bind transition)
      (transition item) where
  probability_eq event := pure_bind_probability item transition event
  expectation_eq value := pure_bind_expectation item transition value

/-- Binding to deterministic copies is observationally the identity. -/
theorem bind_pure_evaluationEquivalent {α : Type}
    (source : Distribution α) :
    EvaluationEquivalent (source.bind Distribution.pure) source where
  probability_eq event := source.bind_pure_probability event
  expectation_eq value := source.bind_pure_expectation value

/-- Finite bind associativity as equivalence of exact evaluations, while
retaining the two different executable table layouts. -/
theorem bind_bind_evaluationEquivalent {α β γ : Type}
    (source : Distribution α) (first : α → Distribution β)
    (second : β → Distribution γ) :
    EvaluationEquivalent ((source.bind first).bind second)
      (source.bind fun item => (first item).bind second) where
  probability_eq event := source.bind_bind_probability first second event
  expectation_eq value := source.bind_bind_expectation first second value

/-- Swapping the concatenation order of a finite mixture together with its
two displayed coefficients preserves all evaluations, even though the atom
table order changes. -/
theorem mixture_swap_evaluationEquivalent {α : Type}
    (left right : Distribution α) (weight : MixingWeight) :
    EvaluationEquivalent (left.mixture right weight)
      (right.mixture left weight.swap) where
  probability_eq event := left.mixture_swap_probability right weight event
  expectation_eq value := left.mixture_swap_expectation right weight value

end Distribution

end FiniteMeasure
